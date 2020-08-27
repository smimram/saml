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
  | Bool
  | Var of var ref
  | Arr of (string * (t * bool)) list * t (* label, type, optional? *)
  | Tuple of t list
  | Ref of t
  | Nullable of t
(** Contents of a variable. *)
and var =
  | Free of int (** A free variable with given level. *)
  | Link of t (** A link to another type. *)

(** A type scheme. *)
type scheme = var ref list * t

(** A type environment. *)
type env = (string * scheme) list

let make t = { descr = t }

let float () = make Float

let tuple l = make (Tuple l)

let unit () = tuple []

let var =
  let n = ref (-1) in
  fun level ->
    incr n;
    make (Var (ref (Free level)))

let arr a b = make (Arr (a, b))

let arrnl a b =
  let a = List.map (fun t -> "",(t,false)) a in
  arr a b

let nullable a = make (Nullable a)

(** Follow links in variables. *)
let rec unlink t =
  match t.descr with
  | Var { contents = Link t } -> unlink t
  | _ -> t

let var_level x =
  match !x with
  | Free l -> l
  | Link _ -> assert false

let global_namer = univ_namer ()

(** String representation of a type. *)
let to_string ?(generalized=[]) t =
  let namer = if !Config.Debug.Typing.global_names then global_namer else univ_namer () in
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
          (if List.memq v generalized then "'" else "?")
          ^ namer v
          ^ (if !Config.Debug.Typing.show_levels then "@" ^ string_of_int l else "")
      )
    | Float -> "float"
    | Bool -> "bool"
    | Tuple l ->
      if l = [] then "unit" else
        let l = List.map (to_string false) l |> String.concat ", " in
        Printf.sprintf "(%s)" l
    | Arr (a, b) ->
      let a = a |> List.map (fun (l,(t,o)) -> (if o then "?" else "") ^ (if l = "" then "" else l ^ " : ") ^ to_string false t) |> String.concat ", " in 
      let b = to_string false b in
      pa p (Printf.sprintf "(%s) -> %s" a b)
    | Ref t ->
      let t = to_string true t in
      pa p (Printf.sprintf "ref %s" t)
    | Nullable t ->
      let t = to_string true t in
      "?"^t
  in
  to_string false t

let string_of_scheme ((generalized,t):scheme) =
 to_string ~generalized t

let rec occurs x t =
  match (unlink t).descr with
  | Arr (a, b) -> List.exists (fun (l,(t,o)) -> occurs x t) a || occurs x b
  | Var v -> x == v
  | Tuple l -> List.exists (occurs x) l
  | Float | Bool -> false
  | Ref t | Nullable t -> occurs x t

let rec update_level l t =
  match t.descr with
  | Arr (a, t) -> update_level l t
  | Var v ->
    (
      match !v with
      | Link t -> update_level l t
      | Free l' -> v := Free (min l l')
    )
  | Tuple t -> List.iter (update_level l) t
  | Ref t | Nullable t -> update_level l t
  | Float | Bool -> ()

exception Error

let rec ( <: ) (t1:t) (t2:t) =
  (* Printf.printf "st: %s with %s\n%!" (to_string t1) (to_string t2); *)
  let t1 = unlink t1 in
  let t2 = unlink t2 in
  match t1.descr, t2.descr with
  | Var v1, Var v2 when v1 == v2 -> ()
  | _, Var x ->
    if occurs x t1 then raise Error;
    (* TODO: as usual, we could do occurs and update_level at the same time *)
    update_level (var_level x) t1;
    if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t2) (to_string t1);
    x := Link t1
  | Var x, _ ->
    if occurs x t2 then raise Error;
    update_level (var_level x) t2;
    if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t1) (to_string t2);
    x := Link t2
  | Arr (a, b), Arr (a', b') ->
    if List.length a <> List.length a' then raise Error;
    let a' = ref a' in
    List.iter
      (fun (l,(t,o)) ->
         let t',o' = try List.assoc l !a' with Not_found -> raise Error in
         a' := List.remove_assoc l !a';
         t' <: t;
         if o' && not o then raise Error
      ) a;
    b <: b'
  | Tuple l, Tuple l' ->
    if List.length l <> List.length l' then raise Error;
    List.iter2 ( <: ) l l'
  | Ref a, Ref b
  | Nullable a, Nullable b -> a <: b
  | _, Nullable t2 -> t1 <: t2
  | Float, Float -> ()
  | Bool, Bool -> ()
  | _, _ -> raise Error

(** Generalize existential variable to universal ones. *)
let generalize level t : scheme =
  let rec vars t =
    match (unlink t).descr with
    | Var ({ contents = Free l } as x) -> if l > level then [x] else []
    | Var { contents = Link _ } -> assert false
    | Arr (a, b) ->
      let a = List.fold_left (fun v (l,(t,o)) -> (vars t)@v) [] a in
      a@(vars b)
    | Tuple l -> List.fold_left (fun v t -> (vars t)@v) [] l
    | Ref t | Nullable t -> vars t
    | Float | Bool -> []
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
        if not (List.mem_assq x !tenv) then tenv := (x, (var level).descr) :: !tenv;
        List.assq x !tenv
      | Var x -> Var x
      | Arr (a, b) -> Arr (List.map (fun (l,(t,o)) -> l, (aux t,o)) a, aux b)
      | Tuple l -> Tuple (List.map aux l)
      | Ref t -> Ref (aux t)
      | Nullable t -> Nullable (aux t)
      | Float | Bool as t -> t
    in
    { descr }
  in
  aux t

let ref t = make (Ref t)
