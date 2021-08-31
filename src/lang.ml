(** Internal representation of the language and operations to manipulate it
    (typechecking, reduction, etc.). *)

open Extralib
open Common

module T = Type

(** An expression. *)
type t =
  {
    desc : desc; (** The expression. *)
    pos : pos; (** Position in source file. *)
    t : T.t; (** Type. *)
  }

(** Contents of an expression. *)
and desc =
  | Bool of bool
  | Int of int
  | Float of float
  | String of string
  | Var of string (** A variable. *)
  | Fun of pattern * t (** A function. *)
  | FFI of ffi
  | Let of pattern * t * t (** A variable declaration. *)
  | App of t * t
  | Seq of t * t
  | Tuple of t list
  | Meth of t * (string * t) (** A method. *)
  | Field of t * string (** A field. *)
  | Closure of environment * t (** A closure. *)
  | Cast of t * T.t (** Type casting. *)
  | Monad of string * (T.t -> T.t) * t * t (** Monad declaration : name, type, implementation, rest. *)

and pattern =
  | PVar of string
  | PTuple of pattern list (** A tuple. *)

and ffi =
  {
    ffi_name : string;
    ffi_itype : T.t; (** type of the input *)
    ffi_otype : T.t; (** type of the output *)
    ffi_eval : t -> t; (** evaluation *)
  }

(** An environment. *)
and environment = (string * t) list

type expr = t

let tenv = ref ([] : T.environment)
let env = ref ([] : environment)

(** Create an expression. *)
let make ?(pos=dummy_pos) ?t e =
  let t =
    match t with
    | Some t -> t
    | None -> T.var max_int
  in
  {
    desc = e;
    pos;
    t
  }

let var ?pos s = make ?pos (Var s)

(*
let free_var_name =
  let n = ref (-1) in
  fun () ->
    incr n;
    Printf.sprintf "#x%d" !n
*)

let args_name = "args"

let args_pattern = PVar args_name

let args ?pos () = var ?pos args_name

let bool ?pos b = make ?pos (Bool b)

let float ?pos x = make ?pos (Float x)

let string ?pos x = make ?pos (String x)

let fct ?pos args e = make ?pos (Fun (args, e))

let ufun ?pos e = fct ?pos (PTuple []) e

let app ?pos f x = make ?pos (App (f, x))

let seq ?pos e1 e2 = make ?pos (Seq (e1, e2))

let letin ?pos pat def body = make ?pos (Let (pat, def, body))

let tuple ?pos l =
  match l with
  | [e] -> e
  | l -> make ?pos (Tuple l)

let pair ?pos x y = tuple ?pos [x; y]

let unit ?pos () = tuple ?pos []

let meth ?pos e lv =
  make ?pos (Meth (e,lv))

let rec meths ?pos e m =
  match m with
  | lv::m -> meth ?pos (meths ?pos e m) lv
  | [] -> e

let record ?pos l = meths ?pos (unit ?pos ()) l

(*
module
  b = v
  a = u
end
is translated to
a = u
b = v
(a=a, b=b)
 *)
let modul ?pos decls =
  let rec aux e = function
    | (l,v)::m -> aux (letin ~pos:v.pos (PVar l) v e) m
    | [] -> e
  in
  aux (record ?pos (List.map (fun (l,_) -> l, var l) decls)) decls

let field ?pos e l  = make ?pos (Field (e, l))

let cast ?pos e t = make ?pos (Cast (e,t))

let ffi ?pos name ?(eval=fun _ -> error "Not implemented: %s" name) a b =
  let f =
    FFI
      {
        ffi_name = name;
        ffi_itype = a;
        ffi_otype = b;
        ffi_eval = eval;
      }
  in
  make ?pos f

let closure ?pos env t =
  make ?pos (Closure (env, t))

(** String representation of an expression. *)
let rec to_string ~tab p e =
  let pa p s = if p then Printf.sprintf "(%s)" s else s in
  let tabs ?(tab=tab) () = String.make (2*tab) ' ' in
  let tabss () = tabs ~tab:(tab+1) () in
  match e.desc with
  | Var x -> x
  | Bool b -> string_of_bool b
  | Int n -> string_of_int n
  | Float f -> string_of_float f
  | String s -> Printf.sprintf "%S" s
  | FFI ffi -> Printf.sprintf "<%s>" ffi.ffi_name
  | Fun (pat, e) ->
    let pat = string_of_pattern ~tab pat in 
    let e = to_string ~tab:(tab+1) false e in
    pa p (Printf.sprintf "fun %s ->%s%s" pat (if String.contains e '\n' then ("\n"^(tabs ~tab:(tab+1) ())) else " ") e)
  | Closure (_, e) -> Printf.sprintf "<closure>%s" (to_string ~tab true e)
  | App (e, a) ->
    let e = to_string ~tab true e in
    let a = to_string ~tab:(tab+1) true a in
    pa p (Printf.sprintf "%s %s" e a)
  | Seq (e1, e2) ->
    let e1 = to_string ~tab false e1 in
    let e2 = to_string ~tab false e2 in
    pa p (Printf.sprintf "%s%s\n%s%s" e1 (if !Config.Debug.Lang.show_seq then ";" else "") (tabs ()) e2)
  | Let (pat, def, body) ->
    let pat = string_of_pattern ~tab pat in
    let def = to_string ~tab:(tab+1) false def in
    let def =
      if String.contains def '\n' then Printf.sprintf "\n%s%s" (tabss ()) def
      else Printf.sprintf " %s " def
    in
    let body = to_string ~tab false body in
    if !Config.Debug.Lang.show_let then
      pa p (Printf.sprintf "let %s =%s%s\n%s%s" pat def (if String.contains def '\n' then "\n"^tabs()^"in" else "in") (tabs ()) body)
    else
      pa p (Printf.sprintf "%s =%s\n%s%s" pat def (tabs ()) body)
  | Tuple l ->
    let l = List.map (to_string ~tab false) l |> String.concat ", " in
    Printf.sprintf "(%s)" l
  | Meth (e,(l,v)) -> Printf.sprintf "(%s,%s=%s)" (to_string ~tab:(tab+1) false e) l (to_string ~tab:(tab+1) false v)
  | Field (e, l) ->
    Printf.sprintf "%s.%s" (to_string ~tab true e) l
  | Cast (e, t) -> Printf.sprintf "(%s : %s)" (to_string ~tab:(tab+1) false e) (T.to_string t)
  | Monad (s, t, v, body) ->
    Printf.sprintf "%s = monad %s with %s\n%s" s (T.to_string (t (T.var 0))) (to_string ~tab:(tab+1) false v) (to_string ~tab false body)

and string_of_pattern ~tab = function
  | PVar x -> x
  | PTuple l ->
    let l = List.map (string_of_pattern ~tab) l |> String.concat ", " in
    Printf.sprintf "(%s)" l

let to_string e = to_string ~tab:0 false e

let get_float t =
  match t.desc with
  | Float x -> x
  | _ ->
     error "Expected float but got %s" (to_string t)

let get_string t =
  match t.desc with
  | String s -> s
  | _ -> assert false

(** Free variables of a pattern. *)
let pattern_variables = function
  | PVar x -> [x]
(* | PRecord l -> List.map (fun (_,x,_) -> x) l *)
  | _ -> assert false

(** {2 Type inference} *)

(** Typing error. *)
exception Typing of pos * string

let type_error e s =
  Printf.ksprintf (fun s -> raise (Typing (e.pos, s))) s

(** Check the type of an expression. *)
let rec check level (env:T.environment) e =
  (* Printf.printf "check %s\n\n\n%!" (to_string e); *)
  (* Printf.printf "env: %s\n\n" (String.concat_map " , " (fun (x,(_,t)) -> x ^ ":" ^ T.to_string t) env.T.Env.t); *)
  let (<:) e a = if not (T.( <: ) e.t a) then error "%s: %s has type %s but %s expected." (Common.string_of_pos e.pos) (to_string e) (T.to_string e.t) (T.to_string a) in
  let (>:) e a = if not (T.( <: ) a e.t) then error "%s: %s has type %s but %s expected." (Common.string_of_pos e.pos) (to_string e) (T.to_string e.t) (T.to_string a) in
  let rec type_of_pattern level env = function
    | PVar x ->
      let a = T.var level in
      let env = (x,a)::env in
      env, a
    | PTuple l ->
      let env, l = List.fold_map (type_of_pattern level) env l in
      env, T.tuple l
  in
  match e.desc with
  | Bool _ -> e >: T.bool ()
  | Int _ -> e >: T.int ()
  | Float _ -> e >: T.float ()
  | String _ -> e >: T.string ()
  | FFI f -> e >: T.instantiate level (T.arr f.ffi_itype f.ffi_otype)
  | Var x ->
    let t = try List.assoc x env with Not_found -> type_error e "Unbound variable %s." x in
    e >: T.instantiate level t
  | Seq (e1, e2) ->
    check level env e1;
    e1 <: T.unit ();
    check level env e2;
    e >: e2.t
  | Let (pat,def,body) ->
    check (level+1) env def;
    let env, a = type_of_pattern (level+1) env pat in
    def >: a;
    Printf.printf "let %s : %s\n%!" (string_of_pattern ~tab:0 pat) (T.to_string def.t);
    let env =
      (* Generalize the bound variables. *)
      (List.map
         (fun x ->
            let t = List.assoc x env in
            (* Printf.printf "generalize %s: %s\n%!" x (T.to_string t); *)
            T.generalize level t;
            (* Printf.printf "generalized  : %s\n%!" (T.to_string t); *)
            x, t)
         (pattern_variables pat)
      )@env
    in
    check level env body;
    e >: body.t
  | Fun (pat,v) ->
    let env, a = type_of_pattern level env pat in
    check level env v;
    e >: T.arr a v.t
  | Closure _ -> assert false
  | App (f, v) ->
    let b = T.var level in
    check level env f;
    check level env v;
    f <: T.arr v.t b;
    e >: b
  | Tuple l ->
    List.iter (check level env) l;
    e >: T.tuple (List.map (fun v -> v.t) l)
  | Meth (u,(l,v)) ->
    check level env u;
    check level env v;
    e >: T.meth u.t (l, v.t)
  | Field (v, l) ->
    check level env v;
    let a = T.var level in
    let b = T.var level in
    v <: T.meth b (l, a);
    e >: a
  | Cast (u,a) ->
    check level env u;
    u <: a;
    e >: a
  | Monad (_, t, r, e) ->
    check level env r;
    check level env e;
    let a = T.var level in
    let ta = t a in
    r <: T.meths (T.var level) ["return", T.arr a ta]

let check t = check 0 !tenv t

(** Evaluate a term to a value *)
let rec reduce env t =
  (* Printf.printf "reduce: %s\n\n%!" (to_string t); *)
  match t.desc with
  | Bool _ | Int _ | Float _ | String _ | FFI _ -> t
  | Var x -> (try List.assoc x env with Not_found -> error "Unbound variable during reduction: %s" x)
  | Fun _ -> make ~pos:t.pos (Closure (env, t))
  | Closure (env, t) -> reduce env t
  | Let (pat, def, body) ->
    let def = reduce env def in
    let env = reduce_pattern env pat def in
    reduce env body
  | App (t, u) ->
    let u = reduce env u in
    let t = reduce env t in
    (
      match t.desc with
      | Closure (env', {desc = Fun (pat, t) ; _}) ->
        let env'' = reduce_pattern [] pat u in
        let env' = env''@env' in
        let t = closure env' t in
        let t = letin args_pattern u t in
        reduce env t
      | FFI f -> f.ffi_eval u
      | _ -> error "Unexpected term during application: %s" (to_string t)
    )
  | Seq (t, u) ->
    let _ = reduce env t in
    reduce env u
  | Meth (t,(l,v)) ->
    meth (reduce env t) (l, reduce env v)
  | Tuple l ->
    { t with desc = Tuple (List.map (reduce env) l) }
  | Field (t, l) ->
    let t = reduce env t in
    let rec aux t =
      match t.desc with
      | Meth (_,(l',v)) when l = l' -> v
      | Meth (t,(_,_)) -> aux t
      | _ -> assert false
    in
    aux t
  | Cast (u, _) ->
    reduce env u
  | Monad (_, _, _, e) ->
    reduce env e

and reduce_pattern env pat v =
  match pat, v.desc with
  | PVar x, _ -> (x,v)::env
  | PTuple p, Tuple l -> List.fold_left2 reduce_pattern env p l
  | _ -> assert false

let reduce t = reduce !env t

module Run = struct
  let fst t =
    match t.desc with
    | Tuple [a; _] -> a
    | _ -> assert false

  let snd t =
    match t.desc with
    | Tuple [_; b] -> b
    | _ -> assert false
end
