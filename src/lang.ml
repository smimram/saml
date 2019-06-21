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
  | Record of bool * (string * t) list (** A record, the boolean indicates whether it is recursive (= a module) or not. *)
  | Closure of environment * t (** A closure. *)
and pattern =
  | PVar of string
  | PRecord of (string * string * t option) list (** A record pattern: label, variable, default value. *)
and ffi =
  {
    ffi_name : string;
    ffi_itype : T.t; (** type of the input *)
    ffi_otype : T.t; (** type of the output *)
  }
(** An environment. *)
and environment = (string * t) list
type term = t


(** Create an expression. *)
let make ?(pos=dummy_pos) ?t e =
  let t =
    match t with
    | Some t -> t
    | None -> T.evar max_int
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
  | FFI ffi -> ffi.ffi_name
  | Fun (pat, e) ->
     let pat = string_of_pattern ~tab pat in 
     let e = to_string ~tab:(tab+1) false e in
     pa p (Printf.sprintf "fun %s ->%s%s" pat (if String.contains e '\n' then ("\n"^(tabs ~tab:(tab+1) ())) else " ") e)
  | Closure (env, e) -> Printf.sprintf "<closure>%s" (to_string ~tab true e)
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
         (fun (l,x,v) ->
           let v =
             match v with
             | Some v -> "="^to_string ~tab:(tab+1) false v
             | None -> ""
           in
           Printf.sprintf "%s(%s)%s" l x v) l
     in
     let l = String.concat ", " l in
     Printf.sprintf "(%s)" l

(** Free variables of a pattern. *)
let pattern_variables = function
  | PVar x -> [x]
  | PRecord l -> List.map (fun (_,x,_) -> x) l

let to_string e = to_string ~tab:0 false e

(** {2 Type inference} *)

(** Typing error. *)
exception Typing of pos * string

let type_error e s =
  Printf.ksprintf (fun s -> raise (Typing (e.pos, s))) s

(** Check the type of an expression. *)
let rec check level env e =
  (* Printf.printf "infer_type:\n%s\n\n\n%!" (to_string e); *)
  (* Printf.printf "env: %s\n\n" (String.concat_map " , " (fun (x,(_,t)) -> x ^ ":" ^ T.to_string t) env.T.Env.t); *)
  let (<:) e1 e2 = assert (T.( <: ) e1 e2) in
  let (>:) e2 e1 = assert (T.( <: ) e2 e1) in
  let type_of_pattern env = function
    | PVar x ->
       let a = T.evar level in
       let env = (x,a)::env in
       env, a
    | PRecord l ->
       let env, l =
         List.fold_left
           (fun (env, l) (lab,x,d) ->
             let a = T.evar level in
             (
               match d with
               | Some d ->
                  check level env d;
                  d.t <: a
               | None -> ()
             );
             let env = (x,a)::env in
             env, (lab,a)::l
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
  | FFI f -> e.t >: T.arr f.ffi_itype f.ffi_otype
  | Var x ->
     let t = try List.assoc x env with Not_found -> type_error e "Unbound variable %s." x in
     e.t >: T.instantiate level t
  | Seq (e1, e2) ->
     check level env e1;
     e1.t <: T.unit ();
     check level env e2;
     e.t >: e2.t
  | Let (pat,def,body) ->
     check (level+1) env def;
     let env, a = type_of_pattern env pat in
     let env =
       (* Generalize the bound variables. *)
       (List.map
          (fun x -> x, T.generalize level (List.assoc x env))
          (pattern_variables pat)
       )@env
     in
     a <: def.t;
     check level env body;
     e.t >: body.t
  | Fun (pat,v) ->
     let env, a = type_of_pattern env pat in
     check level env v;
     e.t >: T.arr a v.t
  | Closure _ -> assert false
  | App (f, v) ->
     let b = T.evar level in
     check level env f;
     check level env v;
     f.t <: T.arr v.t b;
     e.t >: b
  | Record (r,l) ->
     (* TODO: use r ..... *)
     let l = List.map (fun (x,e) -> check level env e; x, e.t) l in
     e.t >: T.record l

(** Evaluate a term to a value *)
let rec reduce env t =
  match t.desc with
  | Bool _ | Int _ | Float _ | String _ | FFI _ -> t
  | Var x -> List.assoc x env
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
       | Closure (env, {desc = Fun (pat, t)}) ->
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
     make ~pos:t.pos (Record (false, List.rev l))

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
