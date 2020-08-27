(** Internal representation of the language and operations to manipulate it
   (typechecking, reduction, etc.). *)

open Extralib
open Common

module T = Type

(** An expression. *)
type t =
  {
    descr : descr; (** The expression. *)
    pos : pos; (** Position in source file. *)
    mutable t : T.t option; (** Type. *)
  }
(** Contents of an expression. *)
and descr =
  | Float of float
  | Var of string (** A variable. *)
  | Fun of string list * t (** A function with given arguments. *)
  | FFI of ffi
  | Let of string * t * t (** A variable declaration. *)
  | App of t * t list
  | Seq of t * t
  | Tuple of t list
and ffi =
  {
    ffi_name : string;
    ffi_type : T.scheme;
    ffi_eval : env -> t; (** evaluation *)
  }
(** An environment. *)
and env = (string * t) list
type expr = t

(** Create an expression. *)
let make ?(pos=dummy_pos) ?t e =
  {
    descr = e;
    pos;
    t
  }

(** The dt special variable. *)
let dtv = "#dt"

let typ e = Option.get e.t

let var ?pos s = make ?pos (Var s)

let float ?pos x = make ?pos (Float x)

let unit ?pos () = make ?pos (Tuple [])

let fct ?pos args e = make ?pos (Fun (args, e))

let app ?pos f l = make ?pos (App (f, l))

let seq ?pos e1 e2 = make ?pos (Seq (e1, e2))

let letin ?pos var def body = make ?pos (Let (var, def, body))

let ffi ?pos name ?(eval=fun _ -> error "Not implemented: %s" name) t =
  let f =
    FFI
      {
        ffi_name = name;
        ffi_type = t;
        ffi_eval = eval;
      }
  in
  make ?pos f

(** String representation of an expression. *)
let rec to_string ~tab p e =
  let pa p s = if p then Printf.sprintf "(%s)" s else s in
  let tabs ?(tab=tab) () = String.make (2*tab) ' ' in
  let tabss () = tabs ~tab:(tab+1) () in
  match e.descr with
  | Var x -> x
  | Float f -> string_of_float f
  | FFI ffi -> Printf.sprintf "<%s>" ffi.ffi_name
  | Fun (args, e) ->
    let args = String.concat ", " args in
    let e = to_string ~tab:(tab+1) false e in
    pa p (Printf.sprintf "fun (%s) ->%s%s" args (if String.contains e '\n' then ("\n"^(tabs ~tab:(tab+1) ())) else " ") e)
  | App (e, a) ->
    let e = to_string ~tab true e in
    let a = List.map (to_string ~tab:(tab+1) false) a |> String.concat ", " in
    pa p (Printf.sprintf "%s(%s)" e a)
  | Seq (e1, e2) ->
    let e1 = to_string ~tab false e1 in
    let e2 = to_string ~tab false e2 in
    pa p (Printf.sprintf "%s%s\n%s%s" e1 (if !Config.Debug.Lang.show_seq then ";" else "") (tabs ()) e2)
  | Let (var, def, body) ->
    let def = to_string ~tab:(tab+1) false def in
    let def =
      if String.contains def '\n' then Printf.sprintf "\n%s%s" (tabss ()) def
      else Printf.sprintf " %s " def
    in
    let body = to_string ~tab false body in
    if !Config.Debug.Lang.show_let then
      pa p (Printf.sprintf "let %s =%s%s\n%s%s" var def (if String.contains def '\n' then "\n"^tabs()^"in" else "in") (tabs ()) body)
    else
      pa p (Printf.sprintf "%s =%s\n%s%s" var def (tabs ()) body)
  | Tuple l ->
    let l = List.map (to_string ~tab:(tab+1) false) l |> String.concat ", " in
    Printf.sprintf "(%s)" l

let to_string e = to_string ~tab:0 false e

let get_float t =
  match t.descr with
  | Float x -> x
  | _ -> error "Expected float but got %s" (to_string t)

(** {2 Type inference} *)

(** Typing error. *)
exception Typing of pos * string

let type_error e s =
  Printf.ksprintf (fun s -> raise (Typing (e.pos, s))) s

(** Check the type of an expression. *)
let rec check level (env:T.env) e =
  (* Printf.printf "infer_type:\n%s\n\n\n%!" (to_string e); *)
  (* let check level env e = *)
    (* check level env e; *)
    (* Printf.printf "ck: %s : %s\n\n%!" (to_string e) (T.to_string (typ e)) *)
  (* in *)
  (* Printf.printf "env: %s\n\n" (String.concat_map " , " (fun (x,(_,t)) -> x ^ ":" ^ T.to_string t) env.T.Env.t); *)
  let (<:) e a = try (T.( <: ) (typ e) a) with T.Error -> error "%s: %s has type %s but %s expected." (Common.string_of_pos e.pos) (to_string e) (T.to_string (typ e)) (T.to_string a) in
  let (>:) e a = try (T.( <: ) a (typ e)) with T.Error -> error "%s: %s has type %s but %s expected." (Common.string_of_pos e.pos) (to_string e) (T.to_string (typ e)) (T.to_string a) in
  assert (e.t = None);
  e.t <- Some (T.var level);
  match e.descr with
  | Float _ -> e >: T.float ()
  | FFI f -> e >: T.instantiate level f.ffi_type
  | Var x when x = dtv -> e >: T.float ()
  | Var x ->
    let t = try List.assoc x env with Not_found -> type_error e "Unbound variable %s." x in
    e >: T.instantiate level t
  | Seq (e1, e2) ->
    check level env e1;
    e1 <: T.unit ();
    check level env e2;
    e >: typ e2
  | Let (var,def,body) ->
    check (level+1) env def;
    let t = T.generalize level (typ def) in
    if level = 0 then Printf.printf "%s : %s\n%!" var (T.string_of_scheme t);
    let env = (var, t)::env in
    check level env body;
    e >: typ body
  | Fun (args,v) ->
    let targs = List.map (fun x -> x, if x = dtv then T.float () else T.var level) args in 
    let env = (List.map (fun (x,t) -> x,([],t)) targs)@env in
    check level env v;
    e >: T.arr (List.map snd targs) (typ v)
  | App (f, v) ->
    let b = T.var level in
    check level env f;
    List.iter (check level env) v;
    f <: T.arr (List.map typ v) b;
    e >: b
  | Tuple l ->
    List.iter (check level env) l;
    e >: T.tuple (List.map typ l)

let check env t = check 0 env t

(* (\** Evaluate a term to a value *\) *)
(* let rec reduce env t = *)
  (* (\* Printf.printf "reduce: %s\n\n%!" (to_string t); *\) *)
  (* match t.desc with *)
  (* | Bool _ | Int _ | Float _ | String _ | FFI _ -> t *)
  (* | Var x -> (try List.assoc x env with Not_found -> error "Unbound variable during reduction: %s" x) *)
  (* | Fun _ -> make ~pos:t.pos (Closure (env, t)) *)
  (* | Closure (env, t) -> reduce env t *)
  (* | Let (pat, def, body) -> *)
     (* let def = reduce env def in *)
     (* let env = reduce_pattern env pat def in *)
     (* reduce env body *)
  (* | App (t, u) -> *)
     (* let u = reduce env u in *)
     (* let t = reduce env t in *)
     (* ( *)
       (* match t.desc with *)
       (* | Closure (env', {desc = Fun (pat, t)}) -> *)
          (* let env' = reduce_pattern [] pat u in *)
          (* let t = closure env' t in *)
          (* let t = letin args_pattern u t in *)
          (* reduce env t *)
       (* | FFI f -> f.ffi_eval u *)
       (* | _ -> error "Unexpected term during application: %s" (to_string t) *)
     (* ) *)
  (* | Seq (t, u) -> *)
     (* let _ = reduce env t in *)
     (* reduce env u *)
  (* | Record (r, l) -> *)
     (* let l = *)
       (* List.fold_left *)
         (* (fun l (x,t) -> *)
           (* let env = if r then l@env else env in *)
           (* (x, reduce env t)::l *)
         (* ) [] l *)
     (* in *)
     (* make ~pos:t.pos (Record (false, List.rev l)) *)

(* let reduce t = reduce [] t *)

(* module Run = struct *)
  (* let fst t = reduce (fst t) *)

  (* let snd t = reduce (snd t) *)
(* end *)
