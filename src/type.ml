(** Types. *)

open Common
open Extralib

(** A type. *)
type t =
  {
    desc : desc;
  }

and desc =
  | Bool
  | Int
  | Float
  | String
  | UVar of unit ref (** A universally quantified variable. *)
  | Var of [`Free of int (* level *) | `Link of t] ref (** A variable. *)
  | Arr of t * t
  | Tuple of t list
  | Meth of t * (string * t)
  | Monad of ([`Unknown | `Monad of monad | `Link of 'b] as 'b) ref * t

(** Typing environment. *)
and environment = (string * t) list

(** A monad. *)
and monad =
  {
    m_name : string;
  }

type typ = t

let make t = { desc = t }

let bool () = make Bool

let int () = make Int

let float () = make Float

let string () = make String

let tuple l = make (Tuple l)

let pair x y = tuple [x;y]

let unit () = tuple []

let uvar () = make (UVar (ref ()))

let var level = make (Var (ref (`Free level)))

let arr a b = make (Arr (a, b))

let meth a lv = make (Meth (a, lv))

let rec meths a = function
  | lv::m -> meth (meths a m) lv
  | [] -> a

let of_string = function
  | "int" -> int ()
  | "bool" -> bool ()
  | "float" -> float ()
  | t -> failwith ("Unknown type "^t)

(** Types with bindings. *)
module Bind = struct
  type nonrec t = (string * t) list -> t

  let of_string t : t = fun env ->
    try List.assoc t env
    with Not_found -> of_string t

  let arr a b : t = fun env -> arr (a env) (b env)

  let tuple l : t = fun env -> tuple (List.map (fun a -> a env) l)

  let unit () : t = fun _ -> unit ()
end

let rec unlink x =
  match x with
  | `Link x -> unlink x
  | x -> x

(** Follow links in variables. *)
let unvar t =
  let rec aux t =
    match t.desc with
    | Var { contents = `Link t } -> aux t
    | _ -> t
  in
  aux t

let rec split_meths t =
  match (unvar t).desc with
  | Meth (t,lv) ->
    let t, m = split_meths t in
    t, lv::m
  | _ ->
    t, []

(** String representation of a type. *)
let to_string t =
  let un = univ_namer () in
  let en =
    let n = univ_namer () in
    fun v -> String.capitalize_ascii (n v)
  in
  let pa p s = if p then Printf.sprintf "(%s)" s else s in
  (* When p is false we don't need parenthesis. *)
  let rec to_string p t =
    let t = if !Config.Debug.Typing.show_links then t else unvar t in
    match t.desc with
    | UVar v -> un v
    | Var v ->
      (
        match !v with
        | `Link t' -> Printf.sprintf "[%s]" (to_string false t')
        | `Free l -> en v ^ (if !Config.Debug.Typing.show_levels then "@" ^ string_of_int l else "")
      )
    | Int -> "int"
    | Float -> "float"
    | String -> "string"
    | Bool -> "bool"
    | Tuple l ->
      if l = [] then "unit"
      else
        let l = String.concat_map ", " (to_string false) l in
        Printf.sprintf "(%s)" l
    | Arr (a,b) ->
      let a = to_string true a in
      let b = to_string false b in
      pa p (Printf.sprintf "%s -> %s" a b)
    | Meth _ ->
      let t, m = split_meths t in
      let t = to_string false t in
      "(" ^ List.fold_right (fun (l,v) s -> Printf.sprintf "%s, %s : %s" s l (to_string false v)) m t ^ ")"
    | Monad (m, a) ->
      let m =
        match unlink !m with
        | `Unknown -> "monad"
        | `Monad m -> m.m_name
        | `Link _ -> assert false
      in
      let a = to_string true a in
      pa p (Printf.sprintf "%s %s" m a)
  in
  to_string false t

let rec occurs x t =
  match (unvar t).desc with
  | Arr (a, b) -> occurs x a || occurs x b
  | Var v -> x == v
  | UVar _ -> false
  | Int | Float | String | Bool -> false
  | Tuple l -> List.exists (occurs x) l
  | Meth (a,(_,b)) -> occurs x a || occurs x b
  | Monad (_, a) -> occurs x a

let update_level l t =
  let rec aux t =
    match t.desc with
    | Arr (a, t) -> aux a; aux t
    | UVar _ -> ()
    | Var v ->
      (
        match !v with
        | `Link t -> aux t
        | `Free l' -> v := `Free (min l l')
      )
    | Int | Float | String | Bool -> ()
    | Tuple l -> List.iter aux l
    | Meth (a,(_,b)) -> aux a; aux b
    | Monad (_, a) -> aux a
  in
  aux t

let rec ( <: ) (t1:t) (t2:t) =
  (* Printf.printf "subtype: %s <: %s\n%!" (to_string t1) (to_string t2); *)
  let t1 = unvar t1 in
  let t2 = unvar t2 in
  match t1.desc, t2.desc with
  | UVar v1, UVar v2 when v1 == v2 -> true
  | UVar _, _ -> t2 <: t1
  | Var v1, Var v2 when v1 == v2 -> true
  | _, Var ({ contents = `Free l } as x) ->
    if occurs x t1 then false
    else
      (
        update_level l t1;
        if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t2) (to_string t1);
        x := `Link t1;
        true
      )
  | Var ({ contents = `Free l } as x), _ ->
    if occurs x t2 then false
    else
      (
        update_level l t2;
        if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t1) (to_string t2);
        x := `Link t2;
        true
      )
  | Arr (a, b), Arr (a', b') -> a' <: a && b <: b'
  | Bool, Bool
  | Int, Int
  | Float, Float
  | String, String -> true
  | Tuple l, Tuple l' -> List.length l = List.length l' && List.for_all2 ( <: ) l l'
  | Meth (a,(l,b)), Meth (a',(l',b')) when l = l' -> a <: a' && b <: b'
  | Meth (t1,_), _ -> t1 <: t2
  | _, _ -> false

(** Generalize existential variables to universal ones. *)
let generalize level t =
  let rec generalize t =
    match (unvar t).desc with
    | UVar _ -> ()
    | Var ({ contents = `Free l } as x) -> if l > level then x := `Link (uvar ())
    | Var { contents = `Link _ } -> assert false
    | Arr (a, b) -> generalize a; generalize b
    | Tuple l -> List.iter generalize l
    | Meth (a,(_,b)) -> generalize a; generalize b
    | Monad (_, a) -> generalize a
    | Bool | Int | Float | String -> ()
  in
  generalize t

(** Instantiate a type scheme: replace universally quantified variables with
    fresh variables. *)
let instantiate level t =
  let tenv = ref [] in
  let rec aux t =
    let desc =
      match (unvar t).desc with
      | UVar x ->
        if not (List.mem_assq x !tenv) then tenv := (x, (var level).desc) :: !tenv;
        List.assq x !tenv
      | Var v -> Var v
      | Arr (a, b) -> Arr (aux a, aux b)
      | Tuple l -> Tuple (List.map aux l)
      | Meth (a, (l, b)) -> Meth (aux a, (l, aux b))
      | Monad (m, a) -> Monad (m, aux a)
      | Bool | Int | Float | String as t -> t
    in
    { desc }
  in
  aux t
