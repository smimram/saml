(** Internal representation of the language and operations to manipulate it
    (typechecking, reduction, etc.). *)

(* TODO: check that no dt occurs at toplevel *)
(* TODO: think about partial evaluation *)
(* TODO: functions can be curryfied as usual now that we have records with
   optional types. *)
(* TODO: for i = a to b do e done should be compiled to for(a,b,fun(i)->e)
   otherwise we get nasty capture of variables... *)
(* TODO: in records we should let ... otherwise {x = !r} does get propagated *)

open Stdlib
open Common

module B = Backend

module Type = struct
  type t =
    {
      desc : desc;
      (** Whether the expression allocates memory, in which case it will be
          global. *)
      alloc : bool;
      (** Whether the value is statically known at compile-time. *)
      static : bool;
    }
  and desc =
  | Ident of string
  (** A universal variable (if [None]) or a link to another type [t] (if [Some t]). *)
  | Var of var
  | Int
  | Float
  | String
  | Bool
  | Arr of (string * (t * bool)) list * t
  | Ref of t
  | Array of t
  (** Records may have optional types and have optional row type variables which
      might point to other records. *)
  | Record of ((string * (t * bool)) list * var option)
  (** Internal state of a subprogram. The integer is to ensure that two states
      will be different. *)
  | State of int
  and var = (t option) ref

  let make ?pos ?(alloc=false) ?(static=false) t =
    {
      desc = t;
      alloc;
      static;
    }

  let allocates t = t.alloc

  let arr a r = make (Arr (a, r))

  let arrnl a r =
    let a = List.map (fun t -> "",(t,false)) a in
    arr a r

  let check_record r =
    (* TODO: check that we don't have multiply defined labels, some being
       optional. *)
    List.iter (fun (l,(t,o)) -> if l = "" then assert (not o)) r

  (** Canonize the members of records. *)
  let rec canonize_record (r,v) =
    let r', v =
      let rec aux v =
        match v with
        | None -> [], None
        | Some v ->
          match !v with
          | Some t ->
            (
              match t.desc with
              | Record (r,v) -> canonize_record (r,v)
              | Var v -> aux (Some v)
            )
          | None -> [], Some v
      in
      aux v
    in
    let r = r@r' in
    check_record r;
    r, v

  let unvar t =
    let rec aux t =
      match t.desc with
      | Var { contents = Some t } -> aux t
      | Record r -> { t with desc = Record (canonize_record r) }
      | _ -> t
    in
    aux t

  let is_var t =
    match (unvar t).desc with
    | Var v -> assert (!v = None); true
    | _ -> false

  let to_string t =
    let un = univ_namer () in
    let pa p s = if p then Printf.sprintf "(%s)" s else s in
    (* When p is false we don't need parenthesis. *)
    let rec to_string p t =
      match (unvar t).desc with
      | Ident s -> s
      | Var v ->
        (
          match !v with
          | Some t -> Printf.sprintf "[%s]" (to_string false t)
          | None -> un v
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
        let r, v = canonize_record r in
        let v = if v = None then "" else ">" in
        Printf.sprintf "{%s %s }" v
          (String.concat_map "; "
             (fun (x,(t,o)) ->
               let x = if x = "" then "" else x ^ " : " in
               Printf.sprintf "%s%s%s" x (if o then "?" else "") (to_string false t)
             ) r)
      | State n -> Printf.sprintf "state%d" n
    in
    to_string false t

  let fresh_invar () = ref None

  let fresh_var () =
    make (Var (fresh_invar ()))

  let get_var t =
    match t.desc with
    | Var v -> v
    | _ -> assert false

  let static t =
    { t with static = true }

  let is_static t =
    t.static

  (* TODO: use multiplicities *)
  let rec free_vars ?(multiplicities=false) t =
    (* Printf.printf "free_vars: %s\n%!" (to_string t); *)
    let u fv1 fv2 = fv1@fv2 in
    let fv = free_vars in
    match t.desc with
    | Arr (a, t) -> List.fold_left (fun v (_,(t,_)) -> u (fv t) v) (fv t) a
    | Var v -> [v]
    | Ref t -> fv t
    | Array t -> fv t
    | Record (r,v) ->
      let fv = (List.fold_left (fun f (x,(t,o)) -> u (fv t) f) [] r) in
      (
        match v with
        | Some v -> v::fv
        | None -> fv
      )
    | Int | Float | String | Bool | State _ -> []

  exception Cannot_unify

  let subtype defs t1 t2 =
    let def l =
      try
        List.assoc l defs
      with
      | Not_found -> failwith (Printf.sprintf "Type identifier \"%s\" not unknown." l)
    in
    let rec ( <: ) t1 t2 =
      (* Printf.printf "unify: %s with %s\n%!" (to_string t1) (to_string t2); *)
      let t1 = unvar t1 in
      let t2 = unvar t2 in
      if is_static t2 && not (is_static t1) && not (is_var t1) && not (is_var t2) then
        (
          Printf.printf "not static...\n%!";
          raise Cannot_unify
        );
      match t1.desc, t2.desc with
      | Ident a, _ -> def a <: t2
      | _, Ident b -> t1 <: def b
      | Var v1, Var v2 when v1 == v2 -> ()
      | Var v1, _ ->
        if List.memq v1 (free_vars t2) then
          raise Cannot_unify
        else
          v1 := Some t2
      | _, Var v2 when !v2 = None ->
        if List.memq v2 (free_vars t1) then
          raise Cannot_unify
        else
          v2 := Some t1
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
              v := Some (make (Record (r1',Some v1')))
          );
        let r1,v1 = canonize_record (r1old,v1) in
        (
          match v1,v2 with
          | None,None -> ()
          | Some v1,None -> ()
          | None,Some v2 -> v2 := Some (make (Record ([],None)))
          | Some v1,Some v2 -> if v1 != v2 then v1 := Some (make (Var v2))
        )
      | State m, State n ->
        if m <> n then raise Cannot_unify
      | _, _ -> raise Cannot_unify
    in
    try
      t1 <: t2;
      true
    with
    | Cannot_unify -> false

  (* let unify t1 t2 = *)
    (* let ans = unify t1 t2 in *)
    (* Printf.printf "unify %s and %s : %B\n%!" (to_string t1) (to_string t2) ans; *)
    (* ans *)

  (* TODO: use levels for generalizing *)
  let generalize t =
    let m = mapperq (fun _ -> fresh_var ()) in
    let rec aux t =
      let t' =
        match (unvar t).desc with
        | Var v -> (m v).desc
        | Arr (a, t) ->
          let a = List.map (fun (l,(t,o)) -> l,(aux t,o)) a in
          Arr (a, aux t)
        | Ref t -> Ref (aux t)
        | Array t -> Array (aux t)
        | Record (r,v) ->
          let v =
            match v with
            | Some v -> Some (get_var (m v))
            | None -> None
          in
          Record (List.map (fun (x,(t,o)) -> x,(aux t,o)) r, v)
        | Int | Float | String | Bool | State _ as t -> t
      in
      { t with desc = t' }
    in
    aux (unvar t)

  let int = make Int

  let float = make Float

  let string = make String

  let bool = make Bool

  let ident s = make (Ident s)

  let state =
    let n = ref (-1) in
    fun () ->
      incr n;
      make (State !n)

  let array ?alloc ?static a =
    make ?alloc ?static (Array a)

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
    | Record (r,None) ->
      let r = List.may_map (fun (l,(t,o)) -> assert (not o); if not (is_arr t) then Some (emit t) else None) r in
      let r = Array.of_list r in
      if Array.length r = 1 then r.(0) else B.T.Record r
    | Array t -> B.T.Array (emit t)
    | Var _ -> failwith "Trying to emit type for an universal variable."
    | Arr _ -> failwith "Internal error: cannot emit functional types."
    | State _ -> failwith "Don't know how to emit state, E.emit_type should be used instead..."
end

module T = Type

module Expr = struct
  type t =
    {
      desc : desc;
      pos : pos;
      mutable t : Type.t option; (** Infered type. *)
    }
  and desc =
  | Ident of string
  | Fun of (string * (string * t option)) list * t
  | Let of let_t
  | App of t * (string * t) list
  | Cst of constant
  (** An internal procedure (generated by the emit command). *)
  | Proc of string * (B.T.t list * B.T.t)
  | External of extern
  | Coerce of t * T.t
  | Ref of t
  | Array of t list
  | Record of (string * t) list
  (** Modules are basically the same as records except that members can use
      previously defined values, e.g. { a = 5; b = 2*a }. *)
  | Module of (string * t) list
  | Field of t * string
  (** Replace or add some fields in a record. If the bool is true, the value is
      optional and replaces the value only if not already present. *)
  | Replace_fields of t * (string * (t * bool)) list
  | For of string * t * t * t
  and constant =
  (** Dummy value used internally to declare references. *)
  | Bot
  | Int of int
  | Float of float
  | Bool of bool
  | String of string
  | Get
  | Set
  | If (* takes 3 arguments : "",then,?else *)
  and extern =
    {
      (** Name of the external as useable in scripts. *)
      ext_name : string;
      (** Type given the type of its arguments. *)
      ext_t : (string * T.t) list -> T.t;
      (** Backend implementation depending on its type. *)
      ext_backend : T.t -> Backend.Builder.t -> Backend.expr array -> Backend.Builder.t * Backend.expr;
      (** Implementation. *)
      ext_implem : subst:(string * t) list -> state:reduce_state -> (string * t) list -> reduce_state * t;
    }
  (** State for beta-reduction. *)
  and reduce_state =
      {
        (** Let declarations (optionally recursive). *)
        rs_let : (string * t) list;
        (** Fresh variable generator. *)
        rs_fresh : int;
        (** Procedures generated. *)
        rs_procs : (string * B.proc) list;
        (** Types declared. *)
        rs_types : (string * T.t) list;
      }
  and let_t =
    {
      recursive : bool;
      var : string;
      def : t;
      body : t
    }

  let reduce_state_empty = { rs_let = []; rs_fresh = -1; rs_procs = []; rs_types = [] }

  (** Raised by ext_implems when it is not implemented. *)
  exception Cannot_reduce

  let make ?(pos=dummy_pos) ?t e =
    {
      desc = e;
      pos = pos;
      t = t;
    }

  let backend_get = ref (fun (_:string) -> (assert false : t))

  let to_string e =
    let pa p s = if p then Printf.sprintf "(%s)" s else s in
    let rec to_string p e =
      match e.desc with
      | Ident x -> x
      | Fun (a, e) ->
        let a =
          String.concat_map ", "
            (fun (l,(x,d)) ->
              let l = if l = "" || l = x then "" else l ^ ":" in
              let d = match d with None -> "" | Some d -> "=" ^ to_string false d in
              Printf.sprintf "%s%s%s" l x d
            ) a
        in
        pa p (Printf.sprintf "fun (%s) -> %s" a (to_string false e))
      | App (e, a) ->
        let a = String.concat_map ", " (fun (l,e) -> (if l = "" then "" else (l ^ "=")) ^ to_string false e) a in
        pa p (Printf.sprintf "%s(%s)" (to_string true e) a)
      | Let l ->
        pa p (Printf.sprintf "let%s %s = %s in\n%s" (if l.recursive then " rec" else "") l.var (to_string false l.def) (to_string false l.body))
      | Ref e ->
        Printf.sprintf "ref %s" (to_string true e)
      | External ext -> Printf.sprintf "'%s'" ext.ext_name
      | Cst c ->
        (
          match c with
          | Bot -> Printf.sprintf "⊥"
          | Int n -> string_of_int n
          | Float f -> string_of_float f
          | Bool b -> string_of_bool b
          | String s -> Printf.sprintf "\"%s\"" s
          | Get -> "get"
          | Set -> "set"
          | If -> "if"
        )
      | Coerce (e,t) ->
        Printf.sprintf "(%s : %s)" (to_string false e) (T.to_string t)
      | For(i,b,e,f) ->
        pa p (Printf.sprintf "for %s = %s to %s do %s done" i (to_string false b) (to_string false e) (to_string false f))
      | Array a ->
        let a = String.concat_map ", " (to_string false) a in
        Printf.sprintf "[%s]" a
      | Module r | Record r ->
        Printf.sprintf "( %s )" (String.concat_map "; " (fun (x,v) -> Printf.sprintf "%s = %s" x (to_string false v)) r)
      | Field (r,x) -> Printf.sprintf "%s.%s" (to_string true r) x
      | Replace_fields (r,l) ->
        Printf.sprintf "( %s with %s )" (to_string true r) (String.concat_map ", " (fun (l,(e,o)) -> Printf.sprintf "%s =%s %s" l (if o then "?" else "") (to_string false e)) l)
      | Proc (name,_) -> Printf.sprintf "+%s" name
    in
    to_string false e

  let typ e =
    match e.t with
    | Some t -> T.unvar t
    | None -> failwith (Printf.sprintf "Couldn't get type for %s." (to_string e))

  let rec fct ?(pos=dummy_pos) ?t args e = make ~pos ?t (Fun (args, e))

  let quote ?pos e =
    let t =
      match e.t with
      | None -> None
      | Some t -> Some (T.arr [] (T.unvar t))
    in
    fct ?pos ?t [] e

  let unquote e =
    match e.desc with
    | Fun ([], e) -> e
    | _ -> assert false

  let app ?(pos=dummy_pos) ?t e args =
    make ~pos ?t (App (e, args))

  let ident ?pos ?t x =
    make ?pos ?t (Ident x)

  let is_ident e =
    match e.desc with
      | Ident _ -> true
      | _ -> false

  let int ?pos n =
    let t = T.static T.int in
    make ?pos ~t (Cst (Int n))

  let float ?pos ?(t=T.float) x =
    make ?pos ~t (Cst (Float x))

  let letin ?pos ?t ?(recursive=false) x e1 e2 =
    let t =
      match t with
      | Some t -> Some t
      | None -> e2.t
    in
    let l =
      {
        recursive = recursive;
        var = x;
        def = e1;
        body = e2;
      }
    in
    make ?pos ?t (Let l)

  let record ?pos ?t r =
    make ?pos ?t (Record r)

  let unit ?pos ?t () =
    record ?pos ?t []

  let seq ?pos ?t e1 e2 =
    let t =
      match t with
      | Some t -> Some t
      | None -> e2.t
    in
    letin ?pos ?t "_" e1 e2

  let rec seqs = function
    | [e] -> e
    | e::l -> seq e (seqs l)
    | [] -> unit ()

  let bot ?pos ~t () =
    make ~t (Cst Bot)

  let array ?pos ?t a =
    make ?pos ?t (Array a)

  let field ?pos ?t e l =
    make ?pos ?t (Field (e, l))

  let reference ?pos ?t e =
    let t =
      match t with
      | Some t -> Some t
      | None ->
        (
          match e.t with
          | Some t -> Some (T.ref t)
          | None -> None
        )
    in
    make ?pos ?t (Ref e)

  let get_ref ?t r =
    app ?t (make (Cst Get)) ["",r]

  let set_ref r e =
    app ~t:T.unit (make (Cst Set)) ["",r; "",e]

  let proc ~t ?pos (name,bt) =
    make ~t ?pos (Proc (name,bt))

  let fresh_var =
    let n = ref 0 in
    fun ?(name="tmp") () ->
      incr n;
      Printf.sprintf "_%s%d" name !n

  (** Split the bool / then / else in the arguments of an if. *)
  let bte args =
    List.assoc "" args,
    List.assoc "then" args,
    List.assoc "else" args

  let emit_type e =
    (* Printf.printf "emit_type: %s:%s\n%!" (to_string e) (T.to_string (typ e)); *)
    match e.desc with
    | App({ desc = Proc (_,(ta,t)) },args) ->
      (* Printf.printf "%d vs %d\n" (List.length ta) (List.length args); *)
      assert (List.length ta = List.length args);
      t
    | _-> T.emit (typ e)

  module FV = struct
    include Set.Make (struct type t = string let compare = compare end)

    (** Free variables of an expression. *)
    let rec of_expr e =
      (* Printf.printf "free_vars: %s\n%!" (to_string e); *)
      let fv = of_expr in
      match e.desc with
        | Ident x -> singleton x
        | Cst _ -> empty
        | External _ -> empty
        | App (e, a) -> union (fv e) (List.fold_left (fun v (l,e) -> union (fv e) v) empty a)
        | Record r -> List.fold_left (fun v (l,e) -> union (fv e) v) empty r
        | Fun (a, e) -> List.fold_left (fun fv (_,(x,_)) -> remove x fv) (fv e) a
  end

  (** Raised by SAML implementations when reduction is not possible. *)
  exception Cannot_reduce

  (** Typing error. *)
  exception Typing of pos * string

  (** Infer the type of an expression. *)
  let rec infer_type ?(annot=fun e -> ()) defs env e =
    (* Printf.printf "infer_type: %s\n%!" (to_string e); *)
    let infer_type ?(defs=defs) = infer_type defs in
    let (<:) = T.subtype defs in

    (* let infer_type env e = *)
    (* let e = infer_type env e in *)
    (* Printf.printf "inferred: %s : %s\n%!" (to_string e) (T.to_string (typ e)); *)
    (* e *)
    (* in *)

    (** Try to coerce e into a value of type t. *)
    let coerce e t =
      let is_unary_record t =
        match (T.unvar t).T.desc with
        | T.Record (["",_],None) -> true
        | _ -> false
      in
      (* Printf.printf "...coerce: %s : %s\n%!" (to_string e) (T.to_string t); *)
      let rec test e t =
        (* Printf.printf "test: %s : %s <: %s\n%!" (to_string e) (T.to_string (typ e)) (T.to_string t); *)
        let te = typ e in
        if te <: t then
          e
        else if !Config.Compiler.coerce then
          (
            let pos = e.pos in
            (* Try to perform some simple coercions. *)
            match te.T.desc with
            (* Apply unit to functions. *)
            | T.Arr (a, t') when List.for_all (fun (l,(x,o)) -> o) a ->
              if not (T.is_arr t') && not (T.is_arr t) then
                test (app ~pos ~t:t' e []) t
              else if T.is_arr t then
                (* TODO: generalize this to all functions. *)
                let ta, tr = T.split_arr t in
                let e = test (app ~pos ~t:t' e []) tr in
                test (quote e) t
              else
                raise Exit
            (* Records with one non-labeled member can be coerced to it. *)
            | T.Record (r,None) when !Config.Compiler.Coerce.records && List.count (fun (l,_) -> l = "") r = 1 ->
              let t',o = List.assoc "" r in
              assert (not o);
              test (field ~pos ~t:t' e "") t
            (* Convert ints into floats. *)
            | T.Int when T.is_float t ->
              (
                match e.desc with
                | Cst (Int n) -> test (float ~pos (float_of_int n)) t
                | _ -> raise Exit
              )
            (* Convert values to unary records. *)
            (* | _ when not (T.is_record te) && is_unary_record t -> *)
            (* test (record ~t:(T.record ["",(te,false)]) ["",e]) t *)
            | _ -> raise Exit
          )
        else
          raise Exit
      in
      try
        test e t
      with
      | Exit ->
        let te = typ e in
        raise (Typing (e.pos, Printf.sprintf "This expression has type %s but expected to be of type %s." (T.to_string te) (T.to_string t)))
    in

    let ret desc t = { e with desc = desc; t = Some t } in
    let ans =
      let expr = e in
      match e.t with
      | Some t -> e
      | None ->
        let desc = e.desc in
        match desc with
        | Ident "dt" -> ret desc T.float
        | Ident x ->
          (
            try
              let t = List.assoc x env in
              (* TODO: proper generalization with levels... *)
              let t = if T.is_arr t then T.generalize t else t in
              ret desc t
            with
            | Not_found ->
              raise (Typing (e.pos, Printf.sprintf "Unbound value %s." x))
          )
        | Fun (a, e) ->
          let a =
            List.map
              (fun (l,(x,d)) ->
                let d,t =
                  match d with
                  | Some d ->
                    let d = infer_type env d in
                    Some d, typ d
                  | None ->
                    None, T.fresh_var ()
                in
                let o = d <> None in
                (l,(x,d)), (l,x,t,o)
              ) a
          in
          let a, ta = List.split a in
          let env' = List.map (fun (l,x,t,o) -> x,t) ta in
          let env = env'@env in
          let e = infer_type env e in
          let ta = List.map (fun (l,x,t,o) -> l,(t,o)) ta in
          ret (Fun (a, e)) (T.arr ta (typ e))
        | App (e, a) ->
          let a = List.map (fun (l,e) -> l,(infer_type env e)) a in
          let e =
            match e.desc with
            | External ext ->
              (* Printf.printf "external app: %s\n%!" (to_string expr); *)
              let a = List.map (fun (l,e) -> l, typ e) a in
              let t = ext.ext_t a in
              let t = T.generalize t in
              ret e.desc t
            | _ -> infer_type env e
          in
          let t = typ e in
          (* TODO: this is a hack, we should do proper unification *)
          (
            match (T.unvar t).T.desc with
            | T.Var v ->
              let a = List.map (fun (l,e) -> l,(typ e,false)) a in
              let t = T.fresh_var () in
              v := Some (T.arr a t)
            | _ -> ()
          );
          if not (T.is_arr t) then
            raise (Typing (e.pos, Printf.sprintf "This expression of type %s is not a function; it cannot be applied." (T.to_string t)));
          let u,v = T.split_arr t in
          let u = ref u in
          let expr = e in
          let a =
            List.map
              (fun (l,e) ->
                let tu,_ =
                  try
                    List.assoc l !u
                  with
                  | Not_found ->
                    if l = "" then
                      raise (Typing (expr.pos, Printf.sprintf "The expression has type %s. It cannot be applied to this many arguments." (T.to_string t)))
                    else
                      raise (Typing (expr.pos, Printf.sprintf "The function applied to this argument has type %s. This argument cannot be applied with label %s." (T.to_string t) l))
                in
                u := List.remove_assoc l !u;
                let e = coerce e tu in
                l,e
              ) a
          in
          let t =
            if List.for_all (fun (l,(t,o)) -> o) !u then v
            else
              (* T.arr !u v *)
              failwith "Partial application."
          in
          let e =
            let ret () = ret (App (e, a)) t in
            if e.desc = Cst If then
              (* If the return value of the if is not unit, use a reference. We have
                 to do this because the backend cannot handle return values for
                 ifs. *)
              let t = typ (List.assoc "then" a) in
              let _, t = T.split_arr t in
              if not (T.is_unit t) then
                let r = reference (bot ~t ()) in
                let tret = t in
                let b,t,e = bte a in
                (* TODO: can we avoid a globally generated fresh name? *)
                let x = fresh_var  ~name:"ifref" () in
                let t = quote (set_ref (ident ~t:(T.ref tret) x) (unquote t)) in
                let e = quote (set_ref (ident ~t:(T.ref tret) x) (unquote e)) in
                let ite = app (make (Cst If)) ["",b; "then",t; "else",e] in
                let e = letin x r (seq ite (get_ref (ident ~t:(T.ref tret) x))) in
                infer_type env e
              else
                ret ()
            else
              ret ()
          in
          e
        | Let l ->
          if l.recursive then
            let x = l.var in
            assert (x <> "dt");
            let t = T.fresh_var () in
            let env = (x,t)::env in
            let def = infer_type env l.def in
            if not ((typ def) <: t) then
              failwith "ERROR (TODO) in let rec";
            if not (T.free_vars (typ def) = []) then
              raise (Typing (l.def.pos, Printf.sprintf "Expression has type %s but free variables are not allowed in recursive definitions." (T.to_string (typ def))));
            let env = (x,typ def)::(List.tl env) in
            let body = infer_type env l.body in
            ret (Let { l with def; body }) (typ body)
          else
            let def = infer_type env l.def in
            let def = if l.var = "dt" then coerce def T.float else def in
            let env = (l.var,typ def)::env in
            let body = infer_type env l.body in
            ret (Let { l with def; body }) (typ body)
        | Cst c ->
          (
            let ret t = ret (Cst c) t in
            match c with
            | Int _ -> ret T.int
            | Float _ -> ret T.float
            | Bool _ -> ret T.bool
            | String _ -> ret T.string
            | Get ->
              let a = T.fresh_var () in
              let t = T.arrnl [T.ref a] a in
              ret t
            | Set ->
              let a = T.fresh_var () in
              let t = T.arrnl [T.ref a; a] T.unit in
              ret t
            | If ->
              let a = T.fresh_var () in
              let arg = T.arr [] a in
              let t = T.arr ["",(T.bool,false); "then",(arg,false); "else",(arg,false)] a in
              ret t
          )
        | Coerce (e, t) ->
          let e = infer_type env e in
          let e = coerce e t in
          e
        | Ref e ->
          let e = infer_type env e in
          if T.is_arr (typ e) then
            raise (Typing (e.pos, Printf.sprintf "This expression has type %s but references are only allowed on data types." (T.to_string (typ e))));
          let t = typ e in
          let t = T.ref t in
          ret (Ref e) t
        | External ext ->
          ret desc (T.generalize (ext.ext_t []))
        | Array a ->
          let t = T.fresh_var () in
          let a =
            List.map
              (fun e ->
                let e =infer_type env e in
                let te = typ e in
                if not (t <: te) then
                  raise (Typing (e.pos, Printf.sprintf "This expression has type %s but %s was expected." (T.to_string te) (T.to_string t)));
                e
              ) a
          in
          ret (Array a) (T.array ~static:true t)
        | Record r ->
          let r = List.map (fun (l,e) -> l, infer_type env e) r in
          let tr = List.map (fun (l,e) -> l,(typ e,false)) r in
          ret (Record r) (T.record tr)
        | Module r ->
          let env, r =
            List.fold_map
              (fun env (l,e) ->
                let e = infer_type env e in
                let t = typ e in
                let env = (l,t)::env in
                env, (l,e)
              ) env r
          in
          let tr = List.map (fun (l,e) -> l,(typ e,false)) r in
          ret (Module r) (T.record tr)
        | Field (r, l) ->
          let r = infer_type env r in
          let tr = typ r in
          if not (tr <: (T.record ~row:true [])) then
            raise (Typing (r.pos, Printf.sprintf "This expression has type %s but expected to be a record." (T.to_string (typ r))));
          let t = T.fresh_var () in
          if not (tr <: (T.record ~row:true [l,(t,false)])) then
            raise (Typing (r.pos, Printf.sprintf "This record does not have a member %s." l));
          ret (Field (r,l)) t
        | Replace_fields (r, l) ->
          let r = infer_type env r in
          let tr = typ r in
          let l = List.map (fun (l,(e,o)) -> l,(infer_type env e,o)) l in
          if not (tr <: (T.record ~row:true [])) then
            raise (Typing (r.pos, Printf.sprintf "This expression has type %s but expected to be a record." (T.to_string (typ r))));
          (* TODO: we could indicate optional fields by subtyping *)
          let t =
            match (typ r).T.desc with
            | T.Record(r,row) ->
              let r = ref r in
              List.iter
                (fun (l,(e,o)) ->
                  Printf.printf "tr: %s\n%!" (T.to_string tr);
                  if o then assert (tr <: (T.record ~row:true [l,(typ e,true)]));
                  (* TODO: this is actually much more subtle when we have
                     optional values, but it will do for now. *)
                  r := List.remove_all_assoc l !r;
                  r := (!r)@[l,(typ e,false)]
                ) l;
              let t = T.record !r in
              T.record_with_row t row
            | _ -> assert false
          in
          ret (Replace_fields(r,l)) t
        | For(i,b,e,f) ->
          let b = infer_type env b in
          let e = infer_type env e in
          let f = infer_type ((i,T.int)::env) f in
          let b = coerce b T.int in
          let e = coerce e T.int in
          let f = coerce f (T.arrnl [] T.unit) in
          ret (For(i,b,e,f)) T.unit
    in
    annot ans; ans

  let split_fun e =
    match e.desc with
    | Fun (a,e) -> a,e
    | _ -> assert false

  (** A value is something that can be substituted. *)
  let is_value e =
    match e.desc with
      | Ident _ | Fun _ | Cst _ | External _ | Record _ | Array _ -> true
      | _ -> false

  module BB = B.Builder

  (** Emit the programs, optionally allowing free variables and generating a
      state. *)
  let rec emit ~subst ~state ?(free_vars=false) ?prog expr =
    (* Printf.printf "emit: %s\n\n" (to_string expr); *)
    let rec aux ~subst ~state ~free_vars prog expr =
      (* Printf.printf "emit: %s\n\n" (to_string expr); *)
      let emit ?(subst=subst) ~state prog expr = aux ~subst ~state ~free_vars prog expr in
      let emit_eqs ?(subst=subst) ~state  prog expr =
        let prog = BB.push prog in
        let state, prog = emit ~subst ~state prog expr in
        let prog, e = BB.pop prog in
        state, prog, e
      in
      let etyp e = emit_type e in
      let rec emit_expr ?(subst=subst) ~state prog expr =
        (* Printf.printf "emit_expr: %s\n\n%!" (to_string expr); *)
        match expr.desc with
        | Ident x ->
          let prog, v =
            if free_vars then
              BB.var_create prog x (etyp expr)
            else
              prog, BB.var prog x
          in
          state, prog, B.Var v
        | App ({ desc = Cst Get }, ["", { desc = Ident x }]) -> state, prog, B.Var (BB.var prog x)
        | App ({ desc = External e } as ext, a) ->
          let (state, prog), a =
            List.fold_map
              (fun (state,prog) (l,e) ->
                assert (l = "");
                let state, prog, e = emit_expr ~state prog e in
                (state,prog), e
              ) (state,prog) a
          in
          let a = Array.of_list a in
          let prog, e = e.ext_backend (typ ext) prog a in
          state, prog, e
        (* prog, B.Op (op,a) *)
        | App ({ desc = Cst If }, a) ->
          let b,t,e = bte a in
          let t = unquote t in
          let e = unquote e in
          let state, prog, b = emit_expr ~state prog b in
          let state, prog, t = emit_eqs ~state prog t in
          let state, prog, e = emit_eqs ~state prog e in
          state, prog, B.If (b,t,e)
        | For (i,b,e,f) ->
          let f = unquote f in
          let state, prog, b = emit_expr ~state prog b in
          let state, prog, e = emit_expr ~state prog e in
          let prog = BB.alloc prog i B.T.Int in
          let state, prog, f = emit_eqs ~state prog f in
          state, prog, B.For(BB.var prog i,b,e,f)
        | App ({ desc = Proc(p,_)}, a) ->
          let a = List.map snd a in
          let (state,prog), a =
            List.fold_map
              (fun (state,prog) e ->
                let state, prog, e = emit_expr ~state prog e in
                (state,prog), e
              ) (state,prog) a
          in
          let a = Array.of_list a in
          state, prog, B.Op (B.Call p, a)
        | Cst c ->
          (
            match c with
            | String s -> state, prog, B.String s
            | Float x -> state, prog, B.Float x
            | Int x -> state, prog, B.Int x
            | Bool b -> state, prog, B.Bool b
          )
        | External e ->
          (* For constants such as pi. *)
          let prog, e = e.ext_backend (typ expr) prog [||] in
          state, prog, e
        | Record [] ->
          state, prog, B.unit
        | Record r ->
          (* Printf.printf "emit record: %s : %s\n%!" (to_string expr) (T.to_string (typ expr)); *)
          (* Records are handled in a (very) special way: functional fields are
             actually function declarations. If there is only one data field left
             then the return value is not a 1-uple but the value itself. *)
          let decls = ref [] in
          (* TODO: we should filter according to the type because some fields
             might be hidden, or coercions could remove those... *)
          let r = List.filter (fun (l,e) -> if T.is_arr (typ e) then (decls := (l,e) :: !decls; false) else true) r in
          let decls = List.rev !decls in
          if List.length r = 1 then
            let l,e = List.hd r in
            (* This is where we need emit to take and return subst and state... *)
            (* TODO: emit decls *)
            let state, prog =
              List.fold_left
                (fun (state,prog) (l,e) ->
                  let ea, er = split_fun e in
                  let ta, t = T.split_arr (typ e) in
                  (* Arguments should be ordered according to type (this is
                     important for labeled arguments). *)
                  let args =
                    let ea = ref ea in
                    let arg l =
                      let ans = List.assoc l !ea in
                      ea := List.remove_assoc l !ea;
                      ans
                    in
                    let n = ref (-1) in
                    let ans = List.map (fun (l,(t,_)) -> let x,_ = arg l in incr n; l,x,t,!n) ta in
                    assert (!ea = []);
                    ans
                  in
                  let state, e = reduce_quote ~subst ~state e (List.map (fun (l,x,t,n) -> l, ident ~t x) args) in
                  let prog = BB.push prog in
                  let prog = List.fold_left (fun prog (l,x,t,n) -> BB.eq_alloc prog x (T.emit t) (B.Arg n)) prog args in
                  let state, prog = emit ~subst ~state prog e in
                  let prog, e = BB.pop prog in
                  let targs = List.map (fun (l,x,t,n) -> T.emit t) args in
                  let prog = BB.proc prog l targs (T.emit t) e in
                  state, prog
                ) (state,prog) decls
            in
            (* Printf.printf "emit_expr record: %s\n%!" (to_string e); *)
            emit_expr ~state prog e
          else
            failwith "TODO: emit records"
        | Array _ ->
          failwith "Trying to emit constructed array."
      in
      (* Printf.printf "emit: %s\n\n%!" (to_string expr); *)
      match expr.desc with
      | Let ({ def = { desc = Ref v } } as l) ->
        let prog = BB.alloc prog l.var (etyp v) in
        let state, prog =
          (* Bot is only used for declaring the reference. *)
          if v.desc = Cst Bot then
            state, prog
          else
            let state, prog, v = emit_expr ~state prog v in
            let prog = BB.eq prog ~init:true l.var v in
            state, prog
        in
        emit ~state prog l.body
      | Let ({ def = { desc = App ({ desc = Cst Set }, ["", { desc = Ident x }; "", e]) } } as l) ->
        let state, prog, e = emit_expr ~state prog e in
        let prog = BB.eq prog x e in
        emit ~state prog l.body
      | Let l ->
        assert (l.var <> "dt");
        let t = etyp l.def in
        (*
          if l.recursive then
          let prog = BB.alloc prog l.var t in
          let prog, def = emit_expr prog l.def in
          let prog = BB.eq prog l.var def in
          emit prog l.body
          else
        *)
        assert (not l.recursive);
        let state, prog, def = emit_expr ~state prog l.def in
        let prog = BB.eq_alloc prog ~init:(T.allocates (typ l.def)) l.var t def in
        emit ~state prog l.body
      | Record [] ->
        (* This case is used for return values (which have to be unit) of
           subprograms (if, while, etc). *)
        state, prog
      | _ when T.is_unit (typ expr) ->
        let e = expr in
        let state, x = fresh_var state in
        let e = letin x e (unit ()) in
        emit ~state prog e
      | _ ->
        let e = expr in
        let t = typ e in
        (* Printf.printf "emit output: %s\n%!" (to_string e); *)
        let state, prog, e = emit_expr ~state prog e in
        let prog = BB.output prog (T.emit t) e in
        state, prog
    in
    let prog =
      match prog with
      | Some prog -> prog
      | None -> BB.create (emit_type expr)
    in
    (* let prog = BB.alloc ~free:true prog "dt" (B.T.Float) in *)
    aux ~subst ~state ~free_vars prog expr

  (** Normalize an expression by performing beta-reductions and
      builtins-reductions. *)
  and reduce ~subst ~state expr =
    (* Printf.printf "reduce: %s\n\n%!" (to_string expr); *)
    let reduce ?(subst=subst) ~state expr = reduce ~subst ~state expr in

    (** Perform a substitution. *)
    let rec substs ss e =
      let d =
        match e.desc with
        | Ident x ->
          let rec aux = function
            | (y,e)::ss when y = x -> (substs ss e).desc
            | (y,e)::ss -> aux ss
            | [] -> e.desc
          in
          aux ss
        | Fun (x,e) ->
          let bv = List.map (fun (l,(x,o)) -> x) x in
          let ss = List.remove_all_assocs bv ss in
          Fun (x, substs ss e)
        | Let l ->
          (* l.var is supposed to be already alpha-converted so that there is no
             capture. *)
          let ss' = List.remove_all_assoc l.var ss in
          let def = substs (if l.recursive then ss' else ss) l.def in
          let ss = ss' in
          let body = substs ss l.body in
          Let { l with def; body }
        | App (e, a) ->
          let a = List.map (fun (l,e) -> l, substs ss e) a in
          App (substs ss e, a)
        | Ref e ->
          Ref (substs ss e)
        | Array a ->
          let a = List.map (substs ss) a in
          Array a
        | Record r ->
          let r = List.map (fun (l,e) -> l, substs ss e) r in
          Record r
        | Field (e, l) ->
          let e = substs ss e in
          Field (e, l)
        | Replace_fields (r,l) ->
          let r = substs ss r in
          let l = List.map (fun (l,(e,o)) -> l,(substs ss e,o)) l in
          Replace_fields (r, l)
        | Cst _ | External _ | Proc _ as e -> e
        | Module _ -> assert false
        | For (i,b,e,f) ->
          let s = substs ss in
          For (i, s b, s e, s f)
      in
      { e with desc = d }
    in
    let s = substs subst in
    let state, e =
      match expr.desc with
      | Ident x -> state, s expr
      | Fun (a, e) ->
        (* We have to substitute optionals and rename variables for substitution
           to avoid captures. *)
        let state, a =
          List.fold_map
            (fun state (l,(x,o)) ->
              let o = may s o in
              let state, y = fresh_var state in
              state, ((x,ident y), (l,(y,o)))
            ) state a
        in
        let s, a = List.split a in
        let subst = s@subst in
        let s = substs subst in
        state, fct a (s e)
      | App (e, args) ->
        let state, e = reduce ~state e in
        let state, args = List.fold_map (fun state (l,e) -> let state, e = reduce ~state e in state, (l,e)) state args in
        (
          match e.desc with
          | Fun (a,e) ->
            let rec aux a e = function
              | ((l:string),v)::args ->
                let (x,_),a = List.assoc_rm l a in
                let e = letin x v e in
                aux a e args
              | [] ->
                (* Printf.printf "app: %s\n%!" (to_string expr); *)
                if List.for_all (fun (l,(x,o)) -> o <> None) a then
                  List.fold_left (fun e (l,(x,o)) -> letin x (get_some o) e) e a
                else
                  fct a e
            in
            reduce ~state (aux a e args)
          | Cst If ->
            let b,th,el =
              List.assoc "" args,
              List.assoc "then" args,
              List.assoc "else" args
            in
            let state, b = reduce ~subst ~state b in
            let state, th = reduce_quote ~subst ~state th [] in
            let state, el = reduce_quote ~subst ~state el [] in
            state, app e ["",b; "then", quote th; "else", quote el]
          (*
            | External ext when ext.ext_name = "print" ->
            let s = String.concat_map "; " (fun (x,v) -> Printf.sprintf "%s/%s" (to_string v) x) subst) in
            Printf.printf "print: %s [ %s ]\n" (to_string (List.assoc "" args)) s;
            state, app e args
          *)
          | External ext when ext.ext_name = "play" || ext.ext_name = "save" ->
            Printf.printf "PLAY\n%!";
            let prog = List.assoc "" args in
            let state, prog = reduce_quote ~subst ~state prog [] in
            file_out "out/output.prog" (to_string prog ^ "\n");
            let state, prog = emit ~subst ~state prog in
            let sr = 44100 in
            let dt = 1. /. (float_of_int sr) in
            let prog = BB.eq prog ~init:true "dt" (B.Float dt) in
            let prog = BB.prog prog in
            (* This is a test. *)
            (* let prog = B.pack_state prog "state" in *)
            file_out "out/output.saml" (B.to_string prog);
            (* Emit OCaml. *)
            if true then
              (
                let ml = B.OCaml.emit prog in
                let cmd = ext.ext_name in
                let cmd = if cmd = "save" then "save \"output.wav\"" else cmd in
                let ml = Printf.sprintf "%s\n\nlet () = Samlib.%s %d (program ())\n" ml cmd sr in
                file_out "out/output.ml" ml;
              );
            (* Emit SAML. *)
            if true then
              (
                Printf.printf "%s\n%!" (B.to_string prog);
                let prog = B.SAML.emit prog in
                let prog () = B.V.get_float (prog ()) in
                (if ext.ext_name = "save" then Samlib.save "output.wav" else Samlib.play) 44100 prog;
              );
            state, unit ()
          | External ext when not (T.is_arr (typ expr)) ->
            (* Printf.printf "EXT %s\n%!" (to_string expr); *)
            (* TODO: better when and reduce partial applications. *)
            (
              try
                let state, e = ext.ext_implem ~subst ~state args in
                reduce ~subst ~state e
              with
              | Cannot_reduce -> state, app e args
            )
          | _ -> state, app e args
        )
      | For(i,b,e,f) ->
        let state, i' = fresh_var state in
        let subst = (i,ident i')::subst in
        let i = i' in
        let state, b = reduce ~subst ~state b in
        let state, e = reduce ~subst ~state e in
        let state, f = reduce_quote ~subst ~state f [] in
        (
          match b.desc, e.desc with
          (* | Cst (Int b), Cst (Int n) when n-b <= 10 -> *)
          (* Inline statically known for loops. *)
          (* TODO: this is really ugly since if f contains free variables it
             can override them... (but this is actually useful for
             prevn...) Maybe should we introduce a meta-for... *)
          (* let e = List.init (n-b+1) (fun k -> letin i (int (b+k)) f) in *)
          (* let e = seqs e in *)
          (* reduce ~state e *)
          | _ ->
            let f = quote f in
            state, make (For(i,b,e,f))
        )
      | Let l ->
        if l.recursive then
          (* Create a reference (on bot) for the recursive value. *)
          let t = typ l.def in
          let tref = T.ref t in
          let r = bot ~t:t () in
          let r = reference ~t:tref r in
          let state, rx = fresh_var state in
          let irx = ident ~t:tref rx in
          let state = { state with rs_let = (rx,r)::state.rs_let } in
          let def = l.def in
          let state, def = reduce ~subst:((l.var,get_ref ~t irx)::subst) ~state def in
          let body = l.body in
          let body = letin l.var (get_ref ~t irx) body in
          let e = seq (set_ref irx def) body in
          (* Printf.printf "RECURSIVE: %s\n=>\n%s\n%!" (to_string expr) (to_string e); *)
          reduce ~subst ~state e
        else
          let state, def = reduce ~subst ~state l.def in
          if is_value def && l.var <> "dt" then
            let subst = (l.var,def)::subst in
            reduce ~subst ~state l.body
          else
            (* We have to rename x in order for substitution to be capture-free. *)
            let state, y = fresh_var state in
            let subst = (l.var,ident y)::subst in
            let state = { state with rs_let = (y,def)::state.rs_let } in
            reduce ~subst ~state l.body
      | Ref e ->
        let state, e = reduce ~state e in
        state, reference e
      | Array a ->
        let state, a = List.fold_map (fun state e -> reduce ~state e) state a in
        state, array a
      | Record r ->
        let state, r = List.fold_map (fun state (v,e) -> let state, e = reduce ~state e in state,(v,e)) state r in
        state, record r
      | Module m ->
        (* TODO: this is a hack... *)
        (* TODO: remove duplicate labels. *)
        let beg = ref [] in
        let r =
          List.map
            (fun (l,e) ->
              let lete = List.fold_left (fun v (l,e) -> letin l e v) e !beg in
              beg := (l,e) :: !beg;
              l,lete
            ) m
        in
        reduce ~state (record ~t:(typ expr) r)
      | Field (r, l) ->
        let state, r = reduce ~state r in
        (
          match r.desc with
          | Record r ->
            (* The value should aleardy be reduced at this point *)
            state, List.assoc l r
          | _ -> failwith (Printf.sprintf "Cannot reduce field \"%s\" of %s : %s." l (to_string r) (T.to_string (typ r)))
        )
      | Replace_fields (r, l) ->
        let state, r = reduce ~state r in
        (
          match r.desc with
          | Record r ->
            let r = ref r in
            List.iter
              (fun (l,(e,o)) ->
                if o && List.mem_assoc l !r then () else
                  (
                    r := List.remove_all_assoc l !r;
                    r := (!r)@[l,e]
                  )
              ) l;
            reduce ~state (record ~t:(typ expr) !r)
          | _ -> assert false
        )
      | Cst _ | External _ | Proc _ -> state, expr
    in
    (* Printf.printf "reduce: %s\n=>\n%s\n\n%!" (to_string expr) (to_string e); *)
    (* Ensure that types and locations are preserved. *)
    state, { expr with desc = e.desc }

  (** Reduce a quote (of type (args) -> 'a). *)
  and reduce_quote ~subst ~state prog args =
    let oldstate = state in
    let state = { reduce_state_empty with rs_fresh = state.rs_fresh; rs_types = state.rs_types } in
    let t = snd (T.split_arr (typ prog)) in
    let prog = app ~t prog args in
    let state, prog = reduce ~subst ~state prog in
    let prog = List.fold_left (fun e (x,v) -> letin x v e) prog state.rs_let in
    let state = { rs_let = oldstate.rs_let; rs_fresh = state.rs_fresh; rs_procs = oldstate.rs_procs@state.rs_procs; rs_types = oldstate.rs_types } in
    state, prog

  (** Emit a quote. *)
  and emit_quote ~subst ~state prog e args =
    let state, e = reduce_quote ~subst ~state e args in
    let prog = BB.push prog in
    let state, prog = emit ~subst ~state ~free_vars:true ~prog e in
    let prog, e = BB.pop prog in
    (state, prog), e

  (** Generate a fresh variable name. *)
  and fresh_var state =
    let state = { state with rs_fresh = state.rs_fresh + 1 } in
    (* Printf.printf "fresh var: _x%d\n%!" state.rs_fresh; *)
    state, Printf.sprintf "_x%d" state.rs_fresh


  (** Generate .annot file with type annotations. *)
  let rec annot fname e =
    let ans = ref "" in
    let annot_type (p1,p2) t =
      let a =
        Printf.sprintf "\"%s\" %d %d %d \"%s\" %d %d %d\n%s(\n  %s\n)\n"
          fname
          p1.Lexing.pos_lnum
          p1.Lexing.pos_bol
          p1.Lexing.pos_cnum
          fname
          p2.Lexing.pos_lnum
          p2.Lexing.pos_bol
          p2.Lexing.pos_cnum
          "type"
          (T.to_string t)
      in
      if p1.Lexing.pos_lnum > 0 then
        ans := !ans ^ a
    in
    let rec aux e =
      (* Printf.printf "annot: %s\n%!" (to_string e); *)
      (match e.desc with Cst Set | Proc _ -> () | _ -> annot_type e.pos (typ e));
      match e.desc with
      | Let l -> aux l.def; aux l.body
      | App (e,a) -> aux e; List.iter (fun (l,e) -> aux e) a
      | Fun (_,e) -> aux e
      | Array a -> List.iter aux a
      | Record r | Module r -> List.iter (fun (l,e) -> aux e) r
      | For(_,b,e,f) -> aux b; aux e; aux f
      | Ref e -> aux e
      | Field(e,_) -> aux e
      | Replace_fields(r,l) -> aux r; List.iter (fun (l,(e,o)) -> aux e) l
      | Coerce (e,_) -> aux e
      | Ident _ | External _ | Cst _ -> ()
    in
    aux e;
    !ans
end

module E = Expr

module Module = struct
  type instr =
    | Decl of string * E.t
    | Expr of E.t
    | Type of string * T.t

  type t = instr list

  let to_string = function
    | Decl (x,e) -> Printf.sprintf "%s = %s" x (E.to_string e)
    | Expr e -> Printf.sprintf "%s" (E.to_string e)
    | Type (l,t) -> Printf.sprintf "type %s = %s" l (T.to_string t)

  let to_string m =
    String.concat_map "\n\n" to_string m

  let infer_type ?annot ?(env=[]) m =
    let annotations = ref "" in
    let annot, annot_final =
      match annot with
      | Some fname ->
        let annot_type (p1,p2) t =
          let a =
            Printf.sprintf "\"%s\" %d %d %d \"%s\" %d %d %d\n%s(\n  %s\n)\n"
              fname
              p1.Lexing.pos_lnum
              p1.Lexing.pos_bol
              p1.Lexing.pos_cnum
              fname
              p2.Lexing.pos_lnum
              p2.Lexing.pos_bol
              p2.Lexing.pos_cnum
              "type"
              (T.to_string t)
          in
          if p1.Lexing.pos_lnum > 0 then
            annotations := !annotations ^ a
        in
        (fun e -> annot_type e.E.pos (E.typ e)),
        (fun () -> Common.file_out (Filename.chop_extension fname ^ ".annot") !annotations)
      | None ->
        (fun _ -> ()), (fun () -> ())
    in
    let env = ref env in
    let aux defs = function
      | Decl (x,e) ->
        let e = E.infer_type ~annot defs !env e in
        let t = E.typ e in
        Printf.printf "%s : %s\n\n%!" x (T.to_string t);
        env := (x,t) :: !env;
        defs, Decl (x, e)
      | Expr e ->
        let e = E.infer_type ~annot defs !env e in
        defs, Expr e
      | Type (l,t) ->
        (l,t)::defs, Type (l,t)
    in
    try
      let defs, m = List.fold_map aux [] m in
      annot_final ();
      m
    with
    | e -> annot_final (); raise e

  let reduce ?(subst=[]) ?(state=E.reduce_state_empty) m =
    let emit_let state =
      { state with E.rs_let = [] }, List.map (fun (x,e) -> Decl (x, e)) (List.rev state.E.rs_let)
    in
    let aux subst state = function
      | Decl (x, e) ->
        (* let expr = e in *)
        let state, e = E.reduce ~subst ~state e in
        let state, m = emit_let state in
        let subst =
          if E.is_value e then
            (x,e)::subst
          else
            subst
        in
        (* if !Config.Debug.reduce then *)
        (* Printf.printf "reduce %s: %s\n=>\n%s\n\n%!" x (E.to_string expr) (E.to_string e); *)
        (subst, state), m@[Decl (x, e)]
      | Expr e ->
        let state, e = E.reduce ~subst ~state e in
        let state, m = emit_let state in
        (subst, state), m@[Expr e]
      | Type (l,t) ->
        let state = { state with E. rs_types = (l,t)::state.E.rs_types } in
        (subst, state), m
    in
    let _, m = List.fold_map (fun (subst,state) d -> aux subst state d) (subst,state) m in
    let m = List.concat m in
    m
end

module M = Module
