(** Types. *)

open Common
open Extralib

(** A type. *)
type t =
  {
    desc : desc;
    methods : methods; (** Methods. *)
  }

and methods = [ `Meth of (string * t) * 'a | `None | `Link of 'a option ref] as 'a

and desc =
  | Bool
  | Int
  | Float
  | String
  | UVar of unit ref (** A universally quantified variable. *)
  | Var of [`Free of int (* level *) | `Link of t] ref (** A variable. *)
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

let rec string_of_methods = function
  | `Meth ((l,_),`None) -> Printf.sprintf "%s=?" l
  | `Meth ((l,_),m) -> Printf.sprintf "%s=?, %s" l (string_of_methods m)
  | `Link { contents = Some m } -> string_of_methods m
  | `Link { contents = None } -> "..."
  | `None -> ""

(** Add methods to a type. *)
let meth m t =
  let rec aux = function
    | (l,a)::m -> `Meth ((l,a), aux m)
    | [] -> t.methods
  in
  if m = [] then t else
    let methods = aux m in
    { t with methods }

(*
(** Add methods to a type. *)
let meth' m t =
  Printf.printf "meth': %s\n%!" (string_of_methods m);
  let rec aux = function
    | `Meth ((l,a),m) -> `Meth ((l,a), aux m)
    | `None -> t.methods
    | `Link ({ contents = None } as x) ->
      let rec aux2 = function
        | `Meth (_,m) -> aux2 m
        | `Link { contents = Some m } -> aux2 m
        | `Link { contents = None } as m ->
          (* We always merge the variables (this is the most canonical thing to
             do, although not the only possibility). *)
          x := Some m
        | `None -> failwith "not sure"
      in
      aux2 t.methods;
      t.methods
    | `Link { contents = Some m } -> aux m
  in
  if m = `None then t else
    let methods = aux m in
    { t with methods }
*)

let bool ?methods () = make ?methods Bool

let int ?methods () = make ?methods Int

let float ?methods () = make ?methods Float

let string ?methods () = make ?methods String

let tuple ?methods l = make ?methods (Tuple l)

let pair ?methods x y = tuple ?methods [x;y]

let unit ?methods () = tuple ?methods []

let uvar ?methods () = make ?methods (UVar (ref ()))

let var ?methods level = make ?methods (Var (ref (`Free level)))

let arr ?methods a b = make ?methods (Arr (a, b))

let rec unlink x =
  match x with
  | `Link x -> unlink x
  | x -> x

(** Follow links in variables. *)
let unvar t =
  let rec aux t =
    if t.methods <> `None then t else
    match t.desc with
    | Var { contents = `Link t } -> aux t
    | _ -> t
  in
  aux t

let rec unvar_meth = function
  | `Link { contents = Some m } -> unvar_meth m
  | m -> m

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
    let p = if t.methods = `None then p else false in
    let desc =
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
    if unvar_meth t.methods = `None then desc
    else
      let methods =
        let rec aux = function
          | `Meth ((l,a),`None) -> Printf.sprintf "%s:%s" l (to_string false a)
          | `Meth ((l,a),m) -> Printf.sprintf "%s:%s, %s" l (to_string false a) (aux m)
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
  | Var { contents = `Link a } -> occurs x a
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
        | `Free l' -> v := `Free (min l l')
      )
    | Int | Float | String | Bool -> ()
    | Tuple l -> List.iter aux l
    | Monad (_, a) -> aux a
  in
  aux t

let rec ( <: ) (t1:t) (t2:t) =
  Printf.printf "subtype: %s <: %s\n%!" (to_string t1) (to_string t2);
  let t1 = unvar t1 in
  let t2 = unvar t2 in
  let rec submeth (m1:methods) (m2:methods) =
    (* Printf.printf "submeth: %s / %s\n%!" (string_of_methods m1) (string_of_methods m2); *)
    match m1, m2 with
    | _, `Meth ((l2,a2),m2) ->
      (* Find l2 in m1 *)
      let rec aux = function
        | `Meth ((l1,a1),m1) -> if l1 = l2 then a1 <: a2 else aux m1
        | `Link { contents = Some m1 } -> aux m1
        | `Link ({ contents = None } as x) -> x := Some (`Meth ((l2,a2), `Link (ref None))); true
        | `None -> false
      in
      aux m1 && submeth m1 m2
    | _, `Link { contents = Some m2 } -> submeth m1 m2
    | `Link { contents = Some m1 }, _ -> submeth m1 m2
    | `Link v1, `Link v2 when v1 == v2 -> true
    | _, `Link ({ contents = None } as x) -> x := Some m1; true
    | `Link ({ contents = None } as x), _ -> x := Some m2; true
    | `None, `None -> true
    | _, `None -> false
  in
  let submeth = submeth t1.methods t2.methods in
  if not submeth then Printf.printf "bad methods\n%!";
  submeth &&
  match t1.desc, t2.desc with
  | UVar v1, UVar v2 when v1 == v2 -> true
  | UVar _, _ -> t2 <: t1
  | Var v1, Var v2 when v1 == v2 -> true
  | _, Var ({ contents = `Free l } as x) ->
    if occurs x t1 then false
    else
      (
        update_level l t1;
        let t1 = { t1 with methods = `None } in
        if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t2) (to_string t1);
        x := `Link t1;
        Printf.printf "x = %s\n%!" (to_string t2);
        true
      )
  | Var ({ contents = `Free l } as x), _ ->
    if occurs x t2 then false
    else
      (
        update_level l t2;
        if !Config.Debug.Typing.show_assignations then Printf.printf "%s <- %s\n%!" (to_string t1) (to_string t2);
        x := `Link { t2 with methods = `None };
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
    | Var ({ contents = `Free l } as x) -> if l > level then x := `Link (uvar ())
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
