(** Types. *)

open Common
open Extralib

(** A type. *)
type t =
  {
    desc : desc
  }
 and desc =
   | Unit
   | Bool
   | Int
   | Float
   | String
   (* | Ident of string (\** A variable identifier. *\) *)
   | Var of var (** A type variable. *)
   | EVar of t option ref
   (** An existential type variable: this is an opaque type whose contents will
be revealed later (it is used only for states at the moment because they are not
known at typing time). They cannot be substituted by types with universal
variables. *)
   | Arr of (string * (t * bool)) list * t
   (** Arrow type, the boolean indicates whether the argument is optional. *)
   | Record of (string * t) list
   | Array of t
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

let bool () = make Bool

let int () = make Int

let float () = make Float

let string () = make String

let record l = make (Record l)

let array t = make (Array t)

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

(** Arrow type without labels. *)
let arrnl a t =
  let a = List.map (fun t -> "",(t,false)) a in
  arr a t

let reference t =
  make (Monadic (Ref t))

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
         | Link t ->
            if !Config.Debug.Typing.show_links
            then Printf.sprintf "[%s]" (to_string false t)
            else to_string false t
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
    | Record l ->
       let l = String.concat_map " , " (fun (x,t) -> Printf.sprintf "%s : %s" x (to_string false t)) l in
       Printf.sprintf "{ %s }" l
    | Array t ->
       Printf.sprintf "[%s]" (to_string false t)
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

  let enter env = { env with level = env.level + 1 }
  (* let leave env = { env with level = env.level - 1 } *)

  let bind env x l =
    { env with t = (x,l)::env.t }

  let binds env l =
    { env with t = l@env.t }
end

let rec free_vars t =
  (* Printf.printf "free_vars: %s\n%!" (to_string t); *)
  let u fv1 fv2 = fv1@fv2 in
  let fv = free_vars in
  match (unvar t).desc with
  | Arr (a, t) -> List.fold_left (fun v (_,(t,_)) -> u (fv t) v) (fv t) a
  | Var v -> [v]
  | EVar _ -> []
  | Unit | Int | Float | String | Bool -> []
  | Array t -> fv t
  | Record l -> List.fold_left (fun v (_,t) -> u (fv t) v) [] l
  | Monadic (Ref t) -> fv t

let update_level l t =
  let rec aux t =
    let update_var v =
      match !v with
      | Link t -> aux t
      | FVar l' -> l' := min l !l'
    in
    match t.desc with
    | Arr (a, t) -> aux t
    | Var v -> update_var v
    | EVar v -> (match !v with Some t -> aux t | None -> ())
    | Unit | Int | Float | String | Bool -> ()
    | Array t -> aux t
    | Record l -> List.iter (fun (_,t) -> aux t) l
    | Monadic (Ref t) -> aux t
  in
  aux t

exception Cannot_unify

let subtype (env:Env.t) (t1:t) (t2:t) =
  let rec ( <: ) t1 t2 =
    (* Printf.printf "subtype: %s with %s\n%!" (to_string t1) (to_string t2); *)
    let t1 = unvar t1 in
    let t2 = unvar t2 in
    match t1.desc, t2.desc with
    | Var v1, Var v2 when v1 == v2 -> ()
    | _, Var ({ contents = FVar l } as v2) ->
       if List.memq v2 (free_vars t1) then
         raise Cannot_unify
       else
         (
           update_level !l t1;
           if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t2) (to_string t1);
           v2 := Link t1
         )
    | Var _, _ -> t2 <: t1
    | EVar v1, EVar v2 when v1 == v2 -> ()
    | Arr (t1', t1''), Arr (t2', t2'') ->
       t1'' <: t2'';
       let a2 = ref t2' in
       List.iter
         (fun (l,(t1,o1)) ->
           try
             let t2,o2 = List.assoc l !a2 in
             a2 := List.remove_assoc l !a2;
             if o2 && not o1 then raise Cannot_unify;
             t2 <: t1
           with
           | Not_found ->
              if not o1 then raise Cannot_unify
         ) t1';
       if List.exists (fun (_,(_,o)) -> not o) !a2 then raise Cannot_unify
    | Array t1, Array t2 -> t1 <: t2
    | Record l1, Record l2 ->
       begin
         try
           List.iter (fun (x,t) -> List.assoc x l1 <: t) l2
         with
         | Not_found -> raise Cannot_unify
       end
    | Monadic (Ref t1), Monadic (Ref t2) -> t1 <: t2
    | Unit, Unit -> ()
    | Bool, Bool -> ()
    | Int, Int -> ()
    | Float, Float -> ()
    | String, String -> ()
    | _, _ -> raise Cannot_unify
  in
  try
    t1 <: t2;
    true
  with
  | Cannot_unify -> false

let generalize level t : scheme =
  let rec aux t =
    let generalize_var v =
      match !v with
      | FVar l -> if !l > level then [v] else []
      | Link _ -> assert false
    in
    match (unvar t).desc with
    | Var v -> generalize_var v
    | EVar v -> []
    | Arr (a, t) ->
       let a = List.concat_map (fun (l,(t,o)) -> aux t) a in
       (aux t)@a
    | Record l -> List.concat_map (fun (x,t) -> aux t) l
    | Array t -> aux t
    | Unit | Bool | Int | Float | String -> []
    | Monadic (Ref t) ->  aux t
  in
  aux t, t

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
      | EVar v -> EVar v
      | Arr (a, t) ->
         let a = List.map (fun (l,(t,o)) -> l,(aux t,o)) a in
         let t = aux t in
         Arr (a, t)
      | Array t ->
         Array (aux t)
      | Record l ->
         let l = List.map (fun (x,t) -> x, aux t) l in
         Record l
      | Unit | Bool | Int | Float | String as t -> t
      | Monadic (Ref t) ->
         let t = aux t in
         Monadic (Ref t)
    in
    { desc }
  in
  aux t
