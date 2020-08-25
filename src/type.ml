(** Types. *)

open Common
open Extralib

(** A type. *)
type t =
  {
    descr : descr;
  }
and descr =
  | Float
  | Var of var ref
  | Arr of t * t
(** Contents of a variable. *)
and var =
  | Free of int (** A free variable with given level. *)
  | Link of t (** A link to another type. *)
and environment = (string * t) list

(** A type scheme. *)
type scheme = var ref list * t

let make t = { descr = t }

let float () = make Float

let fresh =
  let n = ref (-1) in
  fun level ->
    incr n;
    make (Var (ref (Free level)))

let arr a b = make (Arr (a, b))

(** Follow links in variables. *)
let rec unlink t =
  match t.descr with
  | Var { contents = Link t } -> unlink t
  | _ -> t

(** String representation of a type. *)
let to_string t =
  let namer = univ_namer () in
  let pa p s = if p then Printf.sprintf "(%s)" s else s in
  (* When p is false we don't need parenthesis. *)
  let rec to_string p t =
    match t.descr with
    | Var v ->
       (
         match !v with
         | Link t ->
            if !Config.Debug.Typing.show_links
            then Printf.sprintf "?[%s]" (to_string false t)
            else to_string p t
         | Free l ->
            "?" ^ namer v ^ (if !Config.Debug.Typing.show_levels then "@" ^ string_of_int l else "")
       )
    | Float -> "float"
    (* | Record l -> *)
       (* if l = [] then "unit" else *)
         (* let l = String.concat_map ", " (fun (x,t) -> Printf.sprintf "%s : %s" x (to_string false t)) l in *)
         (* Printf.sprintf "(%s)" l *)
    | Arr (a,b) ->
       let a = to_string true a in
       let b = to_string false b in
       pa p (Printf.sprintf "%s -> %s" a b)
  in
  to_string false t

let rec occurs x t =
  match (unlink t).descr with
  | Arr (a, b) -> occurs x a || occurs x b
  | Var v -> x == v
  | Float -> false

let rec update_level l t =
  match t.descr with
  | Arr (a, t) -> update_level l t
  | Var v ->
    (
      match !v with
      | Link t -> update_level l t
      | Free l' -> v := Free (min l l')
    )
  | Float -> ()

exception Typing

let rec ( <: ) (t1:t) (t2:t) =
    (* Printf.printf "subtype: %s with %s\n%!" (to_string t1) (to_string t2); *)
    let t1 = unlink t1 in
    let t2 = unlink t2 in
    match t1.descr, t2.descr with
    | Var v1, Var v2 when v1 == v2 -> ()
    | _, Var ({ contents = Free l } as x) ->
      if occurs x t1 then raise Typing;
      (* TODO: qs usual, we could do occurs and update_level at the same time *)
       update_level l t1;
      if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t2) (to_string t1);
      x := Link t1
    | Var ({ contents = Free l } as x), _ ->
       if occurs x t2 then raise Typing;
       update_level l t2;
       if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t1) (to_string t2);
       x := Link t2
    | Arr (a, b), Arr (a', b') -> a' <: a; b <: b'
    | Float, Float -> ()
    | _, _ -> raise Typing

(** Generalize existential variable to universal ones. *)
let generalize level t : scheme =
  let rec vars t =
    match (unlink t).descr with
    | Var ({ contents = Free l } as x) -> if l > level then [x] else []
    | Var { contents = Link _ } -> assert false
    | Arr (a, b) -> (vars a)@(vars b)
    | Float -> []
  in
  (* TODO: remove duplicates *)
  vars t, t

(** Instantiate a type scheme: replace universally quantified variables with
    fresh variables. *)
let instantiate level (g,t) =
  let tenv = ref [] in
  let rec aux t =
    let descr =
      match (unlink t).descr with
      | Var x when List.memq x g ->
        if not (List.mem_assq x !tenv) then tenv := (x, (fresh level).descr) :: !tenv;
        List.assq x !tenv
      | Var x -> Var x
      | Arr (a, b) -> Arr (aux a, aux b)
      | Float as t -> t
    in
    { descr }
  in
  aux t
