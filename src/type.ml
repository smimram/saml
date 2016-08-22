(** Types. *)

open Common
open Stdlib

(** A type. *)
type t =
  {
    desc : desc
  }
 and desc =
   | Unit
   | Int
   | Float
   | String
   | Bool
   (* | Ident of string (\** A variable identifier. *\) *)
   | Var of var (** A type variable. *)
   | EVar of t option ref
   (** An existential type variable: this is an opaque type whose contents will
be revealed later (it is used only for states at the moment because they are not
known at typing time). They cannot be substituted by types with universal
variables. *)
   | Arr of (string * (t * bool)) list * t
   (** Arrow type, the boolean indicates whether the argument is optional. *)
   | Monadic of monadic
 and monadic =
   | Ref of t
 and var = var_contents ref
 (** Contents of a variable. *)
 and var_contents =
   | FVar of int ref (** A free variable at given level. *)
   | Link of t (** A link to another type. *)

(** A type scheme is a universally quantified type. *)
type scheme = var list * t

let make t =
  { desc = t }
              
let unit () = make Unit

let float () = make Float

let int () = make Int

let invar =
  let n = ref 0 in
  fun level ->
    incr n;
    ref (FVar (ref level))
                  
let var level =
  make (Var (invar level))

let evar () =
  make (EVar (ref None))

let arr a t = make (Arr (a, t))

let arrnl a t =
  let a = List.map (fun t -> "",(t,false)) a in
  arr a t

(** Follow links in variables. *)
let unvar t =
  let rec aux t =
    match t.desc with
    | Var { contents = Link t } -> aux t
    | EVar { contents = Some t } -> aux t
    | _ -> t
  in
  aux t

(** String representation of a type. *)
let to_string t =
  let un = univ_namer () in
  let en = univ_namer () in
  let pa p s = if p then Printf.sprintf "(%s)" s else s in
  (* When p is false we don't need parenthesis. *)
  let rec to_string p t =
    match t.desc with
    | Var v ->
       (
         match !v with
         | Link t -> Printf.sprintf "[%s]" (to_string false t)
         | FVar level ->
            un v ^ (if !Config.Debug.Typing.show_levels then "@" ^ string_of_int !level else "")
       )
    | EVar v ->
       (
         match !v with
         | Some t -> Printf.sprintf "?[%s]" (to_string false t)
         | None -> "?" ^ en v
       )
    | Unit -> "unit"
    | Int -> "int"
    | Float -> "float"
    | String -> "string"
    | Bool -> "bool"
    | Arr (a,t) ->
       let a =
         String.concat_map
           ", "
           (fun (l,(t,o)) ->
             if l = "" then
               to_string false t
             else
               Printf.sprintf "%s%s:%s" (if o then "?" else "") l (to_string false t)
           ) a
       in
       pa p (Printf.sprintf "(%s) -> %s" a (to_string false t))
    | Monadic (Ref t) -> pa p (Printf.sprintf "%s ref" (to_string false t))
  in
  to_string false t

(** Variables. *)
module Var = struct
  type t = var

  let make level = var level

  let level x =
    match !x with
    | FVar l -> !l
    | Link _ -> assert false
end

(** Typing environments. *)
module Env = struct
  (** A typing environment. *)
  type t =
    {
      (** Types for free variables. *)
      t : (string * scheme) list;
      (** Generalization level. *)
      level : int;
    }

  (** The empty environment. *)
  let empty =
    {
      t = [];
      level = 0;
    }

  let typ env x =
    List.assoc x env.t

  let level env = env.level

  let bind env l =
    { env with t = l@env.t }
end

let subtype (env:Env.t) (t1:t) (t2:t) =
  (assert false : bool)

(** Instantiate a type scheme: replace universally quantified variables
    with fresh variables. *)
let instantiate ((l,t):scheme) =
  let s = List.map (fun x -> x, invar (Var.level x)) l in
  let rec aux t =
    let desc =
      match (unvar t).desc with
      | Var x ->
         let x = try List.assq x s with Not_found -> x in
         Var x
      | Arr (a, t) ->
         let a = List.map (fun (l,(t,o)) -> l,(aux t,o)) a in
         let t = aux t in
         Arr (a, t)
    in
    { desc }
  in
  aux t
