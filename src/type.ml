(** Types. *)

open Common
open Extralib

(** A type. *)
type t =
  {
    desc : desc;
    methods : ([ `Meth of (string * t) * 'a | `None | `Link of 'a option ref] as 'a); (** Methods. *)
  }

and desc =
  | Bool
  | Int
  | Float
  | String
  | UVar of unit ref (** A universally quantified variable. *)
  | Var of [`Level of int | `Link of t] ref (** A variable. *)
  | Arr of t * t
  | Tuple of t list
  | Monad of ([`Unknown | `Monad of monad | `Link of 'b] as 'b) ref * t

(** Typing environment. *)
and environment = (string * t) list

(** A monad. *)
and monad =
  {
    m_name : string;
  }

type typ = t

let make ?(methods=`None) t =
  let rec aux = function
    | `At_least ((l,a)::m) -> `Meth ((l,a), aux (`At_least m))
    | `At_least [] -> aux `Any
    | `Exactly ((l,a)::m) -> `Meth ((l,a), aux (`Exactly m))
    | `Exactly [] -> aux `None
    | `Any -> `Link (ref None)
    | `None -> `None
  in
  let methods = aux methods in
  { desc = t ; methods }

let bool () = make Bool

let int () = make Int

let float () = make Float

let string () = make String

let tuple l = make (Tuple l)

let pair x y = tuple [x;y]

let unit () = tuple []

let uvar () = make (UVar (ref ()))

let var level =
  make (Var (ref (`Level level)))

let arr a b = make (Arr (a, b))

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

(** String representation of a type. *)
let to_string t =
  let un = univ_namer () in
  let en = univ_namer () in
  let pa p s = if p then Printf.sprintf "(%s)" s else s in
  (* When p is false we don't need parenthesis. *)
  let rec to_string p t =
    let p = if t.methods = `None then p else false in
    let desc =
      match t.desc with
      | UVar v -> un v
      | Var v ->
        (
          match !v with
          | `Link t ->
            if !Config.Debug.Typing.show_links
            then Printf.sprintf "?[%s]" (to_string false t)
            else to_string p t
          | `Level l ->
            "?" ^ en v ^ (if !Config.Debug.Typing.show_levels then "@" ^ string_of_int l else "")
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
    if t.methods = `None then desc
    else
      let methods =
        let rec aux = function
          | `Meth ((l,a),`None) -> Printf.sprintf "%s=%s" l (to_string false a)
          | `Meth ((l,a),m) -> Printf.sprintf "%s=%s, %s" l (to_string false a) (aux m)
          | `Link { contents = Some m } -> aux m
          | `Link { contents = None } -> "..."
          | `None -> ""
        in
        aux t.methods
      in
      Printf.sprintf "(%s, %s)" desc methods
  in
  to_string false t

let rec occurs x t =
  match (unvar t).desc with
  | Arr (a, b) -> occurs x a || occurs x b
  | Var v -> x == v
  | UVar _ -> false
  | Int | Float | String | Bool -> false
  | Tuple l -> List.exists (occurs x) l
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
        | `Level l' -> v := `Level (min l l')
      )
    | Int | Float | String | Bool -> ()
    | Tuple l -> List.iter aux l
    | Monad (_, a) -> aux a
  in
  aux t

let rec ( <: ) (t1:t) (t2:t) =
  (* Printf.printf "subtype: %s with %s\n%!" (to_string t1) (to_string t2); *)
  let t1 = unvar t1 in
  let t2 = unvar t2 in
  match t1.desc, t2.desc with
  | UVar v1, UVar v2 when v1 == v2 -> true
  | UVar _, _ -> t2 <: t1
  | Var v1, Var v2 when v1 == v2 -> true
  | _, Var ({ contents = `Level l } as x) ->
    if occurs x t1 then false
    else
      (
        update_level l t1;
        if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t2) (to_string t1);
        x := `Link t1;
        true
      )
  | Var ({ contents = `Level l } as x), _ ->
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
  | _, _ -> false

(** Generalize existential variables to universal ones. *)
let generalize level t =
  let rec generalize t =
    match (unvar t).desc with
    | UVar _ -> ()
    | Var ({ contents = `Level l } as x) -> if l > level then x := `Link (uvar ())
    | Var { contents = `Link _ } -> assert false
    | Arr (a, b) -> generalize a; generalize b
    | Tuple l -> List.iter generalize l
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
      | Monad (m, a) -> Monad (m, aux a)
      | Bool | Int | Float | String as t -> t
    in
    { desc ; methods = t.methods }
  in
  aux t
