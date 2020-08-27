(** Internal representation of the language and operations to manipulate it
   (typechecking, reduction, etc.). *)

open Extralib
open Common

module T = Type

(** Values. *)
module Value = struct
  type value =
    | Float of float
    | Bool of bool
    | Null
    | Var of string
    | Fun of (env -> value)
    | Tuple of value list
    | Neutral of neutral
  and neutral =
    | App of neutral * (string * value) list
    | Seq of neutral * (unit -> value)
  and env = (string * value) list

  type t = value

  let float x = Float x
    
  let get_float = function
    | Float x -> x
    | _ -> assert false
end
module V = Value

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
  | Bool of bool
  | Var of string (** A variable. *)
  | Fun of (string * (string * t option)) list * t (** A function with given arguments (label, variable, default value). *)
  | FFI of ffi
  | Let of string * t * t (** A variable declaration. *)
  | App of t * (string * t) list
  | Seq of t * t
  | Tuple of t list
  | Null
and ffi =
  {
    ffi_name : string;
    ffi_type : T.scheme;
    ffi_eval : V.env -> V.t; (** evaluation *)
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

let null ?pos () = make ?pos Null

let float ?pos x = make ?pos (Float x)

let unit ?pos () = make ?pos (Tuple [])

let fct ?pos args e = make ?pos (Fun (args, e))

let app ?pos f l = make ?pos (App (f, l))

let appnl ?pos f l = app ?pos f (List.map (fun e -> "", e) l)

let seq ?pos e1 e2 = make ?pos (Seq (e1, e2))

let letin ?pos var def body = make ?pos (Let (var, def, body))

let tuple ?pos l = make ?pos (Tuple l)

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
  | Bool b -> string_of_bool b
  | FFI ffi -> Printf.sprintf "<%s>" ffi.ffi_name
  | Fun (args, e) ->
    let args = args |> List.map (fun (l,(x,d)) -> (if l<>"" then "~"^l^":" else "")^x^(match d with None -> "" | Some d -> "="^to_string ~tab:(tab+1) true d)) |> String.concat ", " in
    let e = to_string ~tab:(tab+1) false e in
    pa p (Printf.sprintf "fun (%s) ->%s%s" args (if String.contains e '\n' then ("\n"^(tabs ~tab:(tab+1) ())) else " ") e)
  | App (e, a) ->
    let e = to_string ~tab true e in
    let a = a |> List.map (fun (l,v) -> (if l<>"" then l^"=" else "") ^ to_string ~tab:(tab+1) false v) |> String.concat ", " in
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
  | Null -> "null"

let to_string e = to_string ~tab:0 false e

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
  | Bool _ -> e >: T.bool ()
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
    let targs =
      List.map
        (fun (l,(x,d)) ->
           let t, o =
             match d with
             | Some d ->
               check level env d;
               typ d, true
             | None ->
               (if x = dtv then T.float () else T.var level),
               false
           in
           l,x,t,o
        ) args
    in 
    let env = (List.map (fun (l,x,t,o) -> x,([],t)) targs)@env in
    check level env v;
    e >: T.arr (List.map (fun (l,x,t,o) -> l,(t,o)) targs) (typ v)
  | App (f, a) ->
    let b = T.var level in
    check level env f;
    let a =
      List.map
        (fun (l,v) ->
           check level env v;
           l,(typ v,false)
        ) a
    in
    f <: T.arr a b;
    e >: b
  | Tuple l ->
    List.iter (check level env) l;
    e >: T.tuple (List.map typ l)
  | Null ->
    e >: T.nullable (T.var level)

let check env t = check 0 env t

(** Evaluate a term to a value *)
let rec eval (env : V.env) t : V.t =
  (* Printf.printf "eval: %s\n\n%!" (to_string t); *)
  match t.descr with
  | Float x -> Float x
  | Bool b -> Bool b
  | Null -> Null
  | Tuple l -> Tuple (List.map (eval env) l)
  | Var x -> List.assoc x env
  | Seq (t,u) ->
    (
      match eval env t with
      | Tuple [] -> eval env u
      | Neutral t -> Neutral (Seq (t, (fun () -> eval env u)))
      | _ -> assert false
    )
  | App (t, u) ->
    (
      let t = eval env t in
      let u = List.map (fun (l,t) -> l, eval env t) u in
      match t with
      | Fun f -> f u
      | Neutral t -> Neutral (App (t, u))
      | _ -> assert false
    )
  | Let (x, def, body) ->
    let def = eval env def in
    let env = (x,def)::env in
    eval env body
  | Fun (a,b) ->
    let f args =
      let args =
        let args = ref args in
        List.map
          (fun (l,(x,d)) ->
             try
               let v = List.assoc l !args in
               args := List.remove_assoc l !args;
               x, v
             with Not_found ->
               let d = Option.get d in
               x, eval env d
          ) a
      in
      let env = args@env in
      eval env b
    in
    Fun f
  | FFI f -> Fun f.ffi_eval

(* let eval t = eval [] t *)

(* module Run = struct *)
  (* let fst t = eval (fst t) *)

  (* let snd t = eval (snd t) *)
(* end *)
