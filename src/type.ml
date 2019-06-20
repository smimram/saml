(** Types. *)

open Common
open Extralib

(** A type. *)
type t =
  {
    desc : desc
  }
 and desc =
   | Bool
   | Int
   | Float
   | String
   | UVar of uvar
   | EVar of t option ref
   (** An existential type variable: this is an opaque type whose contents will
      be revealed later (it is used only for states at the moment because they
      are not known at typing time). They cannot be substituted by types with
      universal variables. *)
   | Arr of t * t
   | Record of (string * t) list
 and uvar = uvar_contents ref
 (** Contents of a variable. *)
 and uvar_contents =
   | FVar of int ref (** A free variable at given level. *)
   | Link of t (** A link to another type. *)

let make t = { desc = t }

let bool () = make Bool

let int () = make Int

let float () = make Float

let string () = make String

let record l = make (Record l)

let invar =
  let n = ref 0 in
  fun level ->
    incr n;
    ref (FVar (ref level))
                  
let uvar level =
  make (UVar (invar level))

let evar () =
  make (EVar (ref None))

let arr a b = make (Arr (a, b))

(** Follow links in variables. *)
let unvar t =
  let rec aux t =
    match t.desc with
    | UVar { contents = Link t } -> aux t
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
    | UVar v ->
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
    | Int -> "int"
    | Float -> "float"
    | String -> "string"
    | Bool -> "bool"
    | Record l ->
       let l = String.concat_map " , " (fun (x,t) -> Printf.sprintf "%s : %s" x (to_string false t)) l in
       Printf.sprintf "{ %s }" l
    | Arr (a,b) ->
       let a = to_string true a in
       let b = to_string false b in
       pa p (Printf.sprintf "%s -> %s" a b)
  in
  to_string false t

(** Typing environments. *)
module Env = struct
  (** A typing environment. *)
  type t =
    {
      (** Types for free variables. *)
      t : (string * t) list;
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

let rec occurs x t =
  match (unvar t).desc with
  | Arr (a, b) -> occurs x a || occurs x b
  | UVar v -> x == v
  | EVar _ -> false
  | Int | Float | String | Bool -> false
  | Record l -> List.exists (fun (_,t) -> occurs x t) l

let update_level l t =
  let rec aux t =
    let update_var v =
      match !v with
      | Link t -> aux t
      | FVar l' -> l' := min l !l'
    in
    match t.desc with
    | Arr (a, t) -> aux t
    | UVar v -> update_var v
    | EVar v -> (match !v with Some t -> aux t | None -> ())
    | Int | Float | String | Bool -> ()
    | Record l -> List.iter (fun (_,t) -> aux t) l
  in
  aux t

let rec ( <: ) (t1:t) (t2:t) =
    (* Printf.printf "subtype: %s with %s\n%!" (to_string t1) (to_string t2); *)
    let t1 = unvar t1 in
    let t2 = unvar t2 in
    match t1.desc, t2.desc with
    | UVar v1, UVar v2 when v1 == v2 -> true
    | _, UVar ({ contents = FVar l } as v2) ->
       if occurs v2 t1 then false
       else
         (
           update_level !l t1;
           if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t2) (to_string t1);
           v2 := Link t1;
           true
         )
    | UVar _, _ -> t2 <: t1
    | EVar v1, EVar v2 when v1 == v2 -> true
    | Arr (a, b), Arr (a', b') ->
       a' <: a && b <: b'
    | Record l1, Record l2 ->
       List.for_all (fun (x,t) -> t <: List.assoc x l2) l1
    | Bool, Bool
    | Int, Int
    | Float, Float
    | String, String -> true
    | _, _ -> false

let rec generalize level t =
  let desc =
    match (unvar t).desc with
    | UVar v -> UVar v
    | EVar v -> 
    | Arr (a, b) ->
       let a = List.concat_map (fun (l,(t,o)) -> aux t) a in
       (aux t)@a
    | Record l -> List.concat_map (fun (x,t) -> aux t) l
    | Bool | Int | Float | String -> []
  in
  { desc }

(** Instantiate a type scheme: replace universally quantified variables with
    fresh variables. *)
let instantiate t =
  let tenv = ref [] in
  let rec aux t =
    let desc =
      match (unvar t).desc with
      | UVar x ->
         if not (List.mem_assq x !tenv) then tenv := (x, (evar ()).desc) :: !tenv;
         List.assq x !tenv
      | EVar v -> EVar v
      | Arr (a, b) -> Arr (aux a, aux b)
      | Record l ->
         let l = List.map (fun (x,t) -> x, aux t) l in
         Record l
      | Bool | Int | Float | String as t -> t
    in
    { desc }
  in
  aux t
