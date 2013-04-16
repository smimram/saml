(** Types. *)

open Stdlib
open Common

module B = Backend

(** A type. *)
type t =
  {
    desc : desc; (** The type. *)
  }
and desc =
| Ident of string
(** A variable identifier. *)
| Var of var
(** A type variable. *)
| EVar of t option ref
(** An existential type variable: this is an opaque type whose contents will be
    revealed later (it is used only for states at the moment because they are
    not known at typing time). They cannot be substituted by types with
    universal variables. *)
| Int
| Float
| String
| Bool
| Arr of (string * (t * bool)) list * t
| Ref of t
| Array of t
(* TODO: possible variants that can appear as in OCaml *)
| Variant
(** A polymorphic variant. *)
| Record of ((string * (t * bool)) list * var option)
(** Records may have optional types and have optional row type variables which
    might point to other records. *)
and var = var_contents ref
and var_contents =
| FVar of var_name * int ref
(** A free variable of given name at given level. *)
| Link of t
(** A link to another variable *)
and var_name = string

(** A type scheme is a universally quantified type. *)
type scheme = var_name list * t

let make ?pos t =
  {
    desc = t;
  }

(** Construct an arrow. *)
let arr a r = make (Arr (a, r))

(** Construct an arrow with unlabeled arguments. *)
let arrnl a r =
  let a = List.map (fun t -> "",(t,false)) a in
  arr a r

let check_record r =
  (* TODO: check that we don't have multiply defined labels, some being
     optional. *)
  List.iter (fun (l,(t,o)) -> if l = "" then assert (not o)) r

(** Operations on records. *)
module Record = struct
  (** Canonize the members of records. *)
  let rec canonize (r,v) =
    let r', v =
      let rec aux v =
        match v with
        | None -> [], None
        | Some v ->
          match !v with
          | Link t ->
            (
              match t.desc with
              | Record (r,v) -> canonize (r,v)
              | Var v -> aux (Some v)
            )
          | FVar _ -> [], Some v
      in
      aux v
    in
    let r = r@r' in
    check_record r;
    r, v
end

let unvar t =
  let rec aux t =
    match t.desc with
    | Var { contents = Link t } -> aux t
    | EVar { contents = Some t } -> aux t
    | Record r -> { t with desc = Record (Record.canonize r) }
    | _ -> t
  in
  aux t

let is_var t =
  match (unvar t).desc with
  | Var v -> true
  | _ -> false

(** Typing environments. *)
module Env = struct
  type typ = t

  type t =
    {
      (** Type of free variables. *)
      t : (string * scheme) list;
      (** Type definitions. *)
      defs : (string * typ) list;
      (** Type of variants. *)
      variants : (string * typ) list;
    }

  let empty =
    {
      t = [];
      defs = [];
      variants = [];
    }

  let typ env x =
    List.assoc x env.t

  let def env x =
    List.assoc x env.defs

  let defs env =
    env.defs

  let variants env =
    Array.of_list (List.rev env.variants)

  let add env x scheme =
    { env with t = (x,scheme)::env.t }

  let add_t env x t =
    add env x ([],t)

  let add_def env x t =
    { env with defs = (x,t)::env.defs }

  let add_variant env x t =
    { env with variants = (x,t)::env.variants }

  let merge env' env =
    {
      t = env'@env.t;
      defs = env.defs;
      variants = env.variants;
    }
end

let show_unique_names = false
let show_levels = false

let to_string ?env t =
  let un = univ_namer () in
  let en = univ_namer () in
  let pa p s = if p then Printf.sprintf "(%s)" s else s in
  (* When p is false we don't need parenthesis. *)
  let rec to_string p t =
    match (unvar t).desc with
    | Ident s ->
      let s =
        match env with
        | Some env ->
          let s' =
            try
              let defs = Env.defs env in
              to_string false (List.assoc s defs)
            with
            | Not_found -> "?"
          in
          Printf.sprintf "%s = %s" s s'
        | None -> s
      in
      s
    | Var v ->
      (
        match !v with
        | Link t -> Printf.sprintf "[%s]" (to_string false t)
        | FVar (name,level) ->
          let s = if show_unique_names then name else un v in
          if show_levels then s ^ "@" ^ string_of_int !level else s
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
    | Arr (a,t) ->
      let a =
        String.concat_map ", " (fun (l,(t,o)) ->
          if l = "" then
            to_string false t
          else
            Printf.sprintf "%s%s:%s" (if o then "?" else "") l (to_string false t)
        ) a
      in
      pa p (Printf.sprintf "(%s) -> %s" a (to_string false t))
    | Ref t -> pa p (Printf.sprintf "%s ref" (to_string false t))
    | Array t -> pa p (Printf.sprintf "%s array" (to_string false t))
    | Record ([],None) -> "unit"
    | Record r ->
      let r, v = Record.canonize r in
      let v =
        if v = None then "" else
          if show_unique_names then
            (to_string false (make (Var (get_some v)))) ^ ">"
          else
            ">"
      in
      Printf.sprintf "{%s %s }" v
        (String.concat_map "; "
           (fun (x,(t,o)) ->
             let x = if x = "" then "" else x ^ " : " in
             Printf.sprintf "%s%s%s" x (if o then "?" else "") (to_string false t)
           ) r)
    | Variant -> "variant"
  in
  to_string false t

(** Inline idents in a type. *)
let expand env t =
  (* Printf.printf "expand: %s\n%!" (to_string t); *)
  let rec aux t =
    let d =
      match (unvar t).desc with
      | Ident x when List.mem_assoc x env.Env.defs -> (List.assoc x env.Env.defs).desc
      | Arr (a,t) ->
        let a = List.map (fun (l,(t,o)) -> l,(aux t,o)) a in
        let t = aux t in
        Arr (a,t)
      | Record (r,v) ->
        let r = List.map (fun (l,(t,o)) -> l,(aux t,o)) r in
        Record (r,v)
      | Array t ->
        Array (aux t)
      | Float | Int -> t.desc
    in
    { t with desc = d }
  in
  aux t

(** Current level for generalization. *)
let current_level = ref 0
let enter_level () = incr current_level
let leave_level () = decr current_level

let fresh_invar =
  let n = ref 0 in
  fun ?level () ->
    let level = match level with Some level -> level | None -> !current_level in
    incr n;
    let name = "'a" ^ string_of_int !n in
    ref (FVar (name, ref level))

let fresh_var ?level () =
  make (Var (fresh_invar ?level ()))

let fresh_evar () =
  make (EVar (ref None))

let get_var t =
  match t.desc with
  | Var v -> v
  | _ -> assert false

(* TODO: use multiplicities *)
let rec free_vars ?(multiplicities=false) t =
  (* Printf.printf "free_vars: %s\n%!" (to_string t); *)
  let u fv1 fv2 = fv1@fv2 in
  let fv = free_vars in
  match t.desc with
  | Arr (a, t) -> List.fold_left (fun v (_,(t,_)) -> u (fv t) v) (fv t) a
  | Var { contents = Link t } -> fv t
  | Var v -> [v]
  | EVar { contents = Some t } -> fv t
  | EVar _ -> []
  | Ref t -> fv t
  | Array t -> fv t
  | Record (r,v) ->
    let fv = (List.fold_left (fun f (x,(t,o)) -> u (fv t) f) [] r) in
    (
      match v with
      | Some v -> v::fv
      | None -> fv
    )
  | Int | Float | String | Bool | Ident _ -> []

(** Update the level of variables by lowering them to [l]. *)
let rec update_level l t =
  let rec aux t =
    let update_var v =
      match !v with
      | Link t -> aux t
      | FVar (_,l') -> l' := min l !l'
    in
    match t.desc with
    | Arr (a, t) -> aux t
    | Var v -> update_var v
    | EVar v -> (match !v with Some t -> aux t | None -> ())
    | Ref t -> aux t
    | Array t -> aux t
    | Record (r,v) ->
      List.iter (fun (x,(t,o)) -> aux t) r;
      (
        match v with
        | Some v -> update_var v
        | None -> ()
      )
    | Int | Float | String | Bool | Ident _ -> ()
  in
  aux t

exception Cannot_unify

let subtype defs t1 t2 =
  let def l = List.assoc l defs in
  let rec ( <: ) t1 t2 =
    (* Printf.printf "unify: %s with %s\n%!" (to_string t1) (to_string t2); *)
    let t1 = unvar t1 in
    let t2 = unvar t2 in
    match t1.desc, t2.desc with
    | Var v1, Var v2 when v1 == v2 -> ()
    | Var ({ contents = FVar (_,l) } as v1), _ ->
      if List.memq v1 (free_vars t2) then
        raise Cannot_unify
      else
        (
          update_level !l t2;
          v1 := Link t2
        )
    | _, Var ({ contents = FVar (_,l) } as v2) ->
      if List.memq v2 (free_vars t1) then
        raise Cannot_unify
      else
        (
          update_level !l t1;
          v2 := Link t1
        )
    | EVar v1, EVar v2 when v1 == v2 -> ()
    | Ident a, Ident b when b = a -> ()
    | Ident a, _ -> (try def a <: t2 with Not_found -> raise Cannot_unify)
    | _, Ident b -> (try t1 <: def b with Not_found -> raise Cannot_unify)
    | Arr (t1', t1''), Arr (t2', t2'') ->
      t1'' <: t2'';
      let a2 = ref t2' in
      List.iter
        (fun (l,(t1,o1)) ->
          try
            let t2,o2 = List.assoc l !a2 in
            a2 := List.remove_assoc l !a2;
            if o1 <> o2 then raise Cannot_unify;
            t2 <: t1
          with
          | Not_found ->
            (* TODO: it this really safe? *)
            if not o1 then raise Cannot_unify
        ) t1'
    | Ref t1, Ref t2 -> t1 <: t2
    | Bool, Bool -> ()
    | Int, Int -> ()
    | Float, Float -> ()
    | String, String -> ()
    | Array t1, Array t2 -> t1 <: t2
    | Variant, Variant -> ()
    | Record (r1,v1), Record (r2,v2) ->
      let r1old = r1 in
      let r1 = ref r1 in
      let r1' = ref [] in
      (* TODO: the problem with records with optional types and "intuitive"
         subtyping is that we can have (a=1,b=2) : (a:int,b:int) <
         (a:int,b:?int) < (a:int) < (a:int,b:?string). We have to think harder
         about this. *)
      List.iter
        (fun (x,(t2,o2)) ->
          try
            let t1,o1 = List.assoc x !r1 in
            r1 := List.remove_assoc x !r1;
            if o1 && not o2 then raise Cannot_unify;
            t1 <: t2
          with
          | Not_found ->
            if v1 = None then
              raise Cannot_unify
            else
              r1' := (x,(t2,o2)) :: !r1'
        ) r2;
      let r1' = List.rev !r1' in
      if r1' <> [] then
        (
          match v1 with
          | None -> raise Cannot_unify
          | Some v ->
            let v1' = fresh_invar () in
            v := Link (make (Record (r1',Some v1')))
        );
      let r1,v1 = Record.canonize (r1old,v1) in
      (
        match v1,v2 with
        | None,None -> ()
        | Some v1,None -> ()
        | None,Some v2 -> v2 := Link (make (Record ([],None)))
        | Some v1,Some v2 -> if v1 != v2 then v1 := Link (make (Var v2))
      )
    | _, _ -> raise Cannot_unify
  in
  try
    t1 <: t2;
    true
  with
  | Cannot_unify -> false

(* let subtype defs t1 t2 = *)
(* let ans = subtype defs t1 t2 in *)
(* Printf.printf "subtype %s and %s : %B\n%!" (to_string t1) (to_string t2) ans; *)
(* ans *)

let generalize t : scheme =
  let current_level = !current_level in
  (* Printf.printf "generalize %s at %d\n%!" (to_string t) current_level; *)
  let rec aux t =
    let generalize_var v =
      match !v with
      | FVar (name,level) -> if !level > current_level then [name] else []
      | Link _ -> assert false
    in
    match (unvar t).desc with
    | Var v -> generalize_var v
    | Arr (a, t) ->
      let a = List.concat_map (fun (l,(t,o)) -> aux t) a in
      (aux t)@a
    | Ref t -> aux t
    | Array t -> aux t
    | Record (r,v) ->
      let r = List.concat_map (fun (l,(t,o)) -> aux t) r in
      let v =
        match v with
        | Some v -> generalize_var v
        | None -> []
      in
      v@r
    | EVar _ | Int | Float | String | Bool | Ident _ -> []
  in
  aux t, t

let instantiate ((g,t):scheme) =
  let s = List.map (fun name -> name, fresh_invar ()) g in
  let rec aux t =
    let ivar v =
      match !v with
      | FVar (name,_) -> (try List.assoc name s with Not_found -> v)
      | Link _ -> assert false
    in
    let desc =
      match (unvar t).desc with
      | Var v -> Var (ivar v)
      | Arr (a, t) ->
        let a = List.map (fun (l,(t,o)) -> l,(aux t,o)) a in
        let t = aux t in
        Arr (a, t)
      | Ref t -> Ref (aux t)
      | Array t -> Array (aux t)
      | Record (r, v) ->
        let r = List.map (fun (l,(t,o)) -> l,(aux t,o)) r in
        let v =
          match v with
          | Some v -> Some (ivar v)
          | None -> None
        in
        Record (r, v)
      | EVar _ | Int | Float | String | Bool | Ident _ as t -> t
    in
    { desc }
  in
  aux t

let int = make Int

let float = make Float

let string = make String

let bool = make Bool

let ident s = make (Ident s)

let array a =
  make (Array a)

let record ?(row=false) r =
  let row = if row then Some (fresh_invar ()) else None in
  check_record r;
  make (Record (r,row))

let record_with_row t row =
  match (unvar t).desc with
  | Record(r,_) -> { t with desc = Record(r,row) }
  | _ -> assert false

let unit = record []

let ref t = make (Ref t)

let variant () = make (Variant)

(* TODO: is_* should be implemented with subtyping because of type aliases. *)
let is_unit t =
  match (unvar t).desc with
  | Record ([],None) -> true
  | _ -> false

let is_int t =
  match (unvar t).desc with
  | Int -> true
  | _ -> false

let is_float t =
  match (unvar t).desc with
  | Float -> true
  | _ -> false

let is_record t =
  match (unvar t).desc with
  | Record _ -> true
  | _ -> false

let rec arity t =
  match (unvar t).desc with
  | Arr (a, _) ->
    (* TODO: also handle nested arrows *)
    List.length a
  | _ -> 0

let is_arr t =
  match (unvar t).desc with
  | Arr _ -> true
  | _ -> false

let split_arr t =
  match (unvar t).desc with
  | Arr (a,t) -> a, unvar t
  | _ -> assert false

let monad state t =
  let r =
    [
      "alloc", arr [] state;
      "loop", arr ["init",(bool,true); "",(state,false)] t;
    ]
  in
  let r = List.map (fun (l,t) -> l,(t,false)) r in
  record r

let monad_state t =
  match (unvar t).desc with
  | Record (r,_) ->
    let a,_ = List.assoc "alloc" r in
    let _, t = split_arr a in
    t
  | _ -> assert false

let set_evar evar t =
  match (unvar evar).desc with
  | EVar v ->
    assert (!v = None);
    v := Some t
  | _ -> assert false

(** Emit a type. This should not be used directly but rather E.emit_type. *)
let rec emit t =
  (* Printf.printf "T.emit: %s\n" (to_string t); *)
  match (unvar t).desc with
  | _ when is_unit t -> B.T.Unit
  | Float -> B.T.Float
  | Int -> B.T.Int
  | String -> B.T.String
  | Bool -> B.T.Bool
  | Ref t -> emit t
  | Record (r,_) ->
    let r = List.may_map (fun (l,(t,o)) -> assert (not o); if not (is_arr t) then Some (emit t) else None) r in
    let r = Array.of_list r in
    B.T.Record r
  | Array t -> B.T.Array (emit t)
  | Var _ -> failwith "Trying to emit type for an universal variable."
  | Arr _ -> failwith "Internal error: cannot emit functional types."
  | Ident t -> failwith (Printf.sprintf "Cannot emit type identifier %s." t)
  | EVar _ -> failwith "Cannot emit existential type."
