(** Internal representation of the language and operations to manipulate it
   (typechecking, reduction, etc.). *)

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
  | Let of pattern * t * t (** A variable declaration. *)
  | App of t * t
  | Seq of t * t
  | Record of bool * (string * t) list (** A record, the boolean indicates whether it is recursive (= a module) or not. *)
and pattern =
  | PVar of string
  | PRecord of (string * t option) list
type term = t

(** Create an expression. *)
let make ?(pos=dummy_pos) ?t e =
  let t =
    match t with
    | Some t -> t
    | None -> T.evar (-1)
  in
  {
    desc = e;
    pos;
    t
  }

let var ?pos s =
  make ?pos (Var s)

let bool ?pos b =
  make ?pos (Bool b)

let float ?pos x =
  make ?pos (Float x)

let fct ?pos args e =
  make ?pos (Fun (args, e))

let app ?pos f x =
  make ?pos (App (f, x))

let seq ?pos e1 e2 =
  make ?pos (Seq (e1, e2))

let letin ?pos pat def body =
  make ?pos (Let (pat, def, body))

let record ?pos r l =
  make ?pos (Record (r, l))

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
  | Fun (pat, e) ->
     let pat = string_of_pattern ~tab pat in 
     let e = to_string ~tab:(tab+1) false e in
     pa p (Printf.sprintf "fun %s ->%s%s" pat (if String.contains e '\n' then ("\n"^(tabs ~tab:(tab+1) ())) else " ") e)
  | App (e, a) ->
     let e = to_string ~tab true e in
     let a = to_string ~tab:(tab+1) true a in
     pa p (Printf.sprintf "%s %s" e a)
  | Seq (e1, e2) ->
     let e1 = to_string ~tab false e1 in
     let e2 = to_string ~tab false e2 in
     pa p (Printf.sprintf "%s\n%s%s" e1 (tabs ()) e2)
  | Let (pat, def, body) ->
     let pat = string_of_pattern ~tab pat in
     let def = to_string ~tab:(tab+1) false def in
     let def =
       if String.contains def '\n' then Printf.sprintf "\n%s%s" (tabss ()) def
       else Printf.sprintf " %s " def
     in
     let body = to_string ~tab false body in
     pa p (Printf.sprintf "%s =%s\n%s%s" pat def (tabs ()) body)
  | Record (r,l) ->
     let l = List.map (fun (x,v) -> Printf.sprintf "%s%s = %s" (tabss()) x (to_string ~tab:(tab+1) false v)) l in
     let l = String.concat "\n" l in
     if r then Printf.sprintf "module\n%s\n%send" l (tabs())
     else Printf.sprintf "{\n%s\n%s}" l (tabs())
and string_of_pattern ~tab = function
  | PVar x -> x
  | PRecord l ->
     let l =
       List.map
         (fun (x,v) ->
           let v =
             match v with
             | Some v -> "="^to_string ~tab:(tab+1) false v
             | None -> ""
           in
           x^v) l
     in
     let l = String.concat ", " l in
     Printf.sprintf "(%s)" l

(** Free variables of a pattern. *)
let pattern_variables = function
  | PVar x -> [x]
  | PRecord l -> List.map fst l

let to_string e = to_string ~tab:0 false e

(** {2 Type inference} *)

(** Typing error. *)
exception Typing of pos * string

let type_error e s =
  Printf.ksprintf (fun s -> raise (Typing (e.pos, s))) s

(** Check the type of an expression. *)
let rec check env e =
  (* Printf.printf "infer_type:\n%s\n\n\n%!" (to_string e); *)
  (* Printf.printf "env: %s\n\n" (String.concat_map " , " (fun (x,(_,t)) -> x ^ ":" ^ T.to_string t) env.T.Env.t); *)
  let (<:) e1 e2 = assert (T.( <: ) e1 e2) in
  let (>:) e2 e1 = assert (T.( <: ) e2 e1) in
  let type_of_pattern env = function
    | PVar x ->
       let a = T.evar (T.Env.level env) in
       let env = T.Env.bind env x a in
       env, a
    | PRecord l ->
       let env, l =
         List.fold_left
           (fun (env, l) (x,d) ->
             let a = T.evar (T.Env.level env) in
             (
               match d with
               | Some d ->
                  check env d;
                  d.t <: a
               | None -> ()
             );
             let env = T.Env.bind env x a in
             env, (x,a)::l
           ) (env,[]) l
       in
       let l = List.rev l in
       env, { desc = Record l }
  in
  match e.desc with
  | Bool _ -> e.t >: T.bool ()
  | Int _ -> e.t >: T.int ()
  | Float _ -> e.t >: T.float ()
  | String _ -> e.t >: T.string ()
  | Var x ->
     let t = try T.Env.typ env x with Not_found -> type_error e "Unbound variable %s." x in
     e.t >: T.instantiate (T.Env.level env) t
  | Seq (e1, e2) ->
     check env e1;
     e1.t <: T.unit ();
     check env e2;
     e.t >: e2.t
  | Let (pat,def,body) ->
     check (T.Env.enter env) def;
     let env, a = type_of_pattern env pat in
     let env =
       (* Generalize the bound variables. *)
       T.Env.binds env
         (List.map
            (fun x -> x, T.generalize (T.Env.level env) (T.Env.typ env x))
            (pattern_variables pat))
     in
     a <: def.t;
     check env body;
     e.t >: body.t
  | Fun (pat,v) ->
     let env, a = type_of_pattern env pat in
     check env v;
     e.t >: T.arr a v.t
  | App (f, v) ->
     let b = T.evar (T.Env.level env) in
     check env f;
     check env v;
     f.t <: T.arr v.t b;
     e.t >: b
  | Record (_,l) ->
     let l = List.map (fun (x,e) -> check env e; x, e.t) l in
     e.t <: T.record l

(** {2 Values} *)
module Value = struct
  type t =
    | Bool of bool
    | Int of int
    | Float of float
    | String of string
    | Record of (string * t) list
    | Fun of environment * pattern * term
  and environment = (string * t) list

  let to_string = function
    | Bool b -> string_of_bool b
    | Int n -> string_of_int n
    | Float x -> string_of_float x
    | String s -> Printf.sprintf "%S" s
    | Record _ -> "<rec>"
    | Fun _ -> "<fun>"
end
module V = Value

(** Evaluate a term to a value *)
let rec reduce env t =
  match t.desc with
  | Bool b -> V.Bool b
  | Int n -> V.Int n
  | Float x -> V.Float x
  | String s -> V.String s
  | Var x -> List.assoc x env
  | Fun (pat, t) -> V.Fun (env, pat, t)
  | Let (pat, def, body) ->
     let def = reduce env def in
     let env = reduce_pattern env pat def in
     reduce env body
  | App (t, u) ->
     let u = reduce env u in
     let t = reduce env t in
     (
       match t with
       | Fun (env, pat, t) ->
          let env = reduce_pattern env pat u in
          reduce env t
       | _ -> assert false
     )
  | Seq (t, u) ->
     let _ = reduce env t in
     reduce env u
  | Record (r, l) ->
       let l =
         List.fold_left
           (fun l (x,t) ->
             let env = if r then l@env else env in
             (x, reduce env t)::l
           ) [] l
       in
       V.Record (List.rev l)

and reduce_pattern env pat v =
  match pat, v with
  | PVar x, v -> (x,v)::env
  | PRecord p, Record l ->
     let env' =
       List.map
         (fun (x,d) ->
           let v =
             try List.assoc x l
             with Not_found ->
               reduce env (Option.get d)
           in
           x, v
         ) p
     in
     env'@env
  | _ -> assert false

(* This wil be filled later on. *)
let parse_file_ctx_fun = ref ((fun _ -> failwith "Parse file function should have been filled") : string -> t -> t)
 
let parse_file_ctx f = !parse_file_ctx_fun f
