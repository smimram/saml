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
  | UVar of t option ref
  | EVar of evar
  (** An existential type variable: this is an opaque type whose contents will
      be revealed later (it is used only for states at the moment because they
      are not known at typing time). They cannot be substituted by types with
      universal variables. *)
  | Arr of t * t
  | Record of (string * t) list
and evar = evar_contents ref
(** Contents of a variable. *)
and evar_contents =
  | Level of int (** A free variable at given level. *)
  | Link of t (** A link to another type. *)
and environment = (string * t) list

type typ = t

let make t = { desc = t }

let bool () = make Bool

let int () = make Int

let float () = make Float

let string () = make String

let record l = make (Record l)

let unit () = record []

let uvar () =
  make (UVar (ref None))

let evar level =
  make (EVar (ref (Level level)))

let arr a b = make (Arr (a, b))

(** An arrow with no labels. *)
let arrnl aa b =
  let aa = List.map (fun t -> "",t) aa in
  let aa = record aa in
  arr aa b

(** Follow links in variables. *)
let unvar t =
  let rec aux t =
    match t.desc with
    | UVar { contents = Some t } -> aux t
    | EVar { contents = Link t } -> aux t
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
         | Some t ->
            if !Config.Debug.Typing.show_links
            then Printf.sprintf "[%s]" (to_string false t)
            else to_string p t
         | None -> un v
       )
    | EVar v ->
       (
         match !v with
         | Link t ->
            if !Config.Debug.Typing.show_links
            then Printf.sprintf "?[%s]" (to_string false t)
            else to_string p t
         | Level l ->
            "?" ^ en v ^ (if !Config.Debug.Typing.show_levels then "@" ^ string_of_int l else "")
       )
    | Int -> "int"
    | Float -> "float"
    | String -> "string"
    | Bool -> "bool"
    | Record l ->
       if l = [] then "unit" else
         let l = String.concat_map ", " (fun (x,t) -> Printf.sprintf "%s : %s" x (to_string false t)) l in
         Printf.sprintf "(%s)" l
    | Arr (a,b) ->
       let a = to_string true a in
       let b = to_string false b in
       pa p (Printf.sprintf "%s -> %s" a b)
  in
  to_string false t

let rec occurs x t =
  match (unvar t).desc with
  | Arr (a, b) -> occurs x a || occurs x b
  | EVar v -> x == v
  | UVar _ -> false
  | Int | Float | String | Bool -> false
  | Record l -> List.exists (fun (_,t) -> occurs x t) l

let update_level l t =
  let rec aux t =
    match t.desc with
    | Arr (a, t) -> aux t
    | UVar v ->
       (
         match !v with
         | Some t -> aux t
         | None -> ()
       )
    | EVar v ->
       (
         match !v with
         | Link t -> aux t
         | Level l' -> v := Level (min l l')
       )
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
    | UVar _, _ -> t2 <: t1
    | EVar v1, EVar v2 when v1 == v2 -> true
    | EVar ({ contents = Level l } as x), _ ->
       if occurs x t2 then false
       else
         (
           update_level l t2;
           if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t1) (to_string t2);
           x := Link t2;
           true
         )
    | Arr (a, b), Arr (a', b') ->
       a' <: a && b <: b'
    | Record l1, Record l2 ->
       List.for_all (fun (x,t) -> t <: List.assoc x l2) l1
    | Bool, Bool
    | Int, Int
    | Float, Float
    | String, String -> true
    | _, _ -> false

(** Generalize existential variable to universal ones. *)
let rec generalize level t =
  let desc =
    match (unvar t).desc with
    | UVar v -> UVar v
    | EVar { contents = Level l } as t -> if l <= level then t else (uvar ()).desc
    | EVar { contents = Link _ } -> assert false
    | Arr (a, b) -> Arr (generalize level a, generalize level b)
    | Record l -> Record (List.map (fun (x,t) -> x , generalize level t) l)
    | Bool | Int | Float | String as t -> t
  in
  { desc }

(** Instantiate a type scheme: replace universally quantified variables with
    fresh variables. *)
let instantiate level t =
  let tenv = ref [] in
  let rec aux t =
    let desc =
      match (unvar t).desc with
      | UVar x ->
         if not (List.mem_assq x !tenv) then tenv := (x, (evar level).desc) :: !tenv;
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
