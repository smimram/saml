(** Internal representation of the language and operations to manipulate it
    (typechecking, reduction, etc.). *)

(* TODO: check that no dt occurs at toplevel by propagating whether we use the
   monad in types. *)
(* TODO: think about partial evaluation *)
(* TODO: functions can be curryfied as usual now that we have records with
   optional types. *)
(* TODO: in records we should let ... otherwise {x = !r} does get propagated *)

open Stdlib
open Common

module B = Backend

module T = Lang_types

(** Operations on expressions. *)
module Expr = struct
  (** Special identifiers. *)
  module Ident = struct
    type t = string

    (** Prefix for special variables, also called meta-variables (prefixed
        variables are guaranteed not to occur in saml files). *)
    let prefix = "#"

    (** Is a variable a meta-variable? *)
    let is_meta x = x.[0] = '#'

    (** Dt meta-variable. *)
    let dt = prefix ^ "dt"

    (** Boolean meta-variable indicating whether we are on first round. *)
    let init = prefix ^ "init"

    (** Meta-variable for state record. *)
    let state =
      let n = ref (-1) in
      fun () ->
        incr n; Printf.sprintf "%sstate%d" prefix !n
  end

  (** An expression. *)
  type t =
    {
      desc : desc; (** The expression. *)
      pos : pos; (** Position in source file. *)
      mutable t : T.t option; (** Infered type. *)
    }
  and desc =
  | Ident of Ident.t
  | Fun of (string * (string * t option)) list * t
  (** A function. Arguments are labelled (or not if the label is ""), have a
      variable, and optionally a default value. *)
  | Let of let_t
  | App of t * (string * t) list
  | Cst of constant
  | External of extern
  | Coerce of t * T.t
  | Ref of t (** A static reference. *)
  | Array of t list
  | Record of (string * t) list
  | Module of (string * t) list
  (** Modules are basically the same as records except that members can use
      previously defined values, e.g. \{ a = 5; b = 2*a \}. *)
  | Field of t * string
  | Replace_fields of t * (string * (t * bool)) list
  (** Replace or add some fields in a record. If the bool is true, the value is
      optional and replaces the value only if not already present. *)
  | Variant of string * t
  | For of string * t * t * t
  | While of t * t
  (** A value at initialization, and another one at other times. *)
  | Alloc of T.t
  (** Dynamically a value. *)
  and constant =
  | Bot
  (** Dummy value used internally to declare references. *)
  | Int of int
  | Float of float
  | Bool of bool
  | String of string
  | Get
  | Set
  | If
  (** Conditional branching. Takes 3 arguments : "", then, ?else. *)
  | Expand (** Expand the monad implementation. *)
  (** External values. *)
  and extern =
    {
      ext_name : string;
      (** Name of the external as useable in scripts. *)
      ext_t : (string * T.t) list -> T.t;
      (** Type given the type of its arguments. *)
      ext_backend : T.t -> Backend.Builder.t -> Backend.expr array -> Backend.Builder.t * Backend.expr;
      (** Backend implementation depending on its type. *)
      ext_implem : (string * t) list -> t;
    (** Implementation. *)
    }
  (** Let declarations. *)
  and let_t =
    {
      recursive : bool;
      var : string;
      def : t;
      body : t
    }

  (** Raised by ext_implems when it is not implemented. *)
  exception Cannot_reduce

  (** Create an expression. *)
  let make ?(pos=dummy_pos) ?t e =
    {
      desc = e;
      pos = pos;
      t = t;
    }

  (** String representation of an expression. *)
  let to_string e =
    let pa p s = if p then Printf.sprintf "(%s)" s else s in
    let rec to_string ~tab p e =
      let tabs ?(tab=tab) () = String.make (2*tab) ' ' in
      let tabss () = tabs ~tab:(tab+1) () in
      match e.desc with
      | Ident x -> x
      | Fun (a, e) ->
        let a =
          String.concat_map ", "
            (fun (l,(x,d)) ->
              let l = if l = "" || l = x then "" else l ^ ":" in
              let d = match d with None -> "" | Some d -> "=" ^ to_string ~tab:(tab+1) false d in
              Printf.sprintf "%s%s%s" l x d
            ) a
        in
        let e = to_string ~tab:(tab+1) false e in
        pa p (Printf.sprintf "fun (%s) ->%s%s" a (if String.contains e '\n' then ("\n"^(tabs ~tab:(tab+1) ())) else " ") e)
      | App ({ desc = Cst If }, a) ->
        let b = List.assoc "" a in
        let t = List.assoc "then" a in
        let e = List.assoc "else" a in
        let b = to_string ~tab:(tab+1) false b in
        let t = to_string ~tab:(tab+1) true t in
        let e = to_string ~tab:(tab+1) true e in
        let break = String.contains t '\n' || String.contains e '\n' in
        if break then
          pa p (Printf.sprintf "if %s then\n%s%s\n%selse\n%s%s" b (tabss()) t (tabs()) (tabss()) e)
        else
          pa p (Printf.sprintf "if %s then %s else %s" b t e)
      | App (e, a) ->
        let a = String.concat_map ", " (fun (l,e) -> (if l = "" then "" else (l ^ "=")) ^ to_string ~tab:(tab+1) false e) a in
        pa p (Printf.sprintf "%s(%s)" (to_string ~tab true e) a)
      | Let l ->
        let def = to_string ~tab:(tab+1) false l.def in
        let def =
          if String.contains def '\n' then
            Printf.sprintf "\n%s%s\n%s" (tabs ~tab:(tab+1) ()) def (tabs())
          else
            Printf.sprintf " %s " def
        in
        pa p (Printf.sprintf "let%s %s =%sin\n%s%s" (if l.recursive then " rec" else "") l.var def (tabs()) (to_string ~tab false l.body))
      | Ref e ->
        Printf.sprintf "ref %s" (to_string ~tab true e)
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
          | Expand -> "expand"
        )
      | Alloc t -> Printf.sprintf "alloc[%s]" (T.to_string t)
      | Coerce (e,t) ->
        Printf.sprintf "(%s : %s)" (to_string ~tab false e) (T.to_string t)
      | For(i,b,e,f) ->
        pa p (Printf.sprintf "for %s = %s to %s do\n%s%s\n%sdone" i (to_string ~tab false b) (to_string ~tab false e) (tabs ()) (to_string ~tab:(tab+1)false f) (tabs ()))
      | While(b,e) ->
        pa p (Printf.sprintf "while %s do\n%s%s\n%sdone" (to_string ~tab false b) (tabs ~tab:(tab+1) ()) (to_string ~tab:(tab+1) false e) (tabs()))
      | Array a ->
        let a = String.concat_map ", " (to_string ~tab false) a in
        Printf.sprintf "[%s]" a
      | Module r | Record r ->
        if r = [] then "()" else
          let r = List.map (fun (x,v) -> Printf.sprintf "%s%s = %s;" (tabss()) x (to_string ~tab:(tab+1) false v)) r in
          let r = String.concat "\n" r in
          Printf.sprintf "(\n%s\n%s)" r (tabs())
      | Field (r,x) -> Printf.sprintf "%s.%s" (to_string ~tab true r) x
      | Replace_fields (r,l) ->
        Printf.sprintf "( %s with %s )" (to_string ~tab true r) (String.concat_map ", " (fun (l,(e,o)) -> Printf.sprintf "%s =%s %s" l (if o then "?" else "") (to_string ~tab false e)) l)
      | Variant (l,e) -> Printf.sprintf "`%s(%s)" l (to_string ~tab false e)
    in
    to_string ~tab:0 false e

  (** Type of an expression. Types should have been infered before using
      this. *)
  let typ e =
    match e.t with
    | Some t -> T.unvar t
    | None -> failwith (Printf.sprintf "Couldn't get type for %s." (to_string e))

  (** Create a function. *)
  let rec fct ?(pos=dummy_pos) ?t args e =
    let t =
      match t with
      | Some _ -> t
      | None ->
        if args = [] then
          (
            match e.t with
            | Some _ -> Some (T.arr [] (typ e))
            | None -> None
          )
        else
          None
    in
    make ~pos ?t (Fun (args, e))

  (** Quote an expression: transforms e into fun () -> e. *)
  let quote ?pos e =
    let t =
      match e.t with
      | None -> None
      | Some t -> Some (T.arr [] (T.unvar t))
    in
    fct ?pos ?t [] e

  (** Unquote an expression: transforms e into e (). *)
  let unquote e =
    match e.desc with
    | Fun ([], e) -> e
    | _ -> assert false

  (** Apply a function to labeled arguments. *)
  let app ?(pos=dummy_pos) ?t e args =
    make ~pos ?t (App (e, args))

  let ident ?pos ?t x =
    make ?pos ?t (Ident x)

  let is_ident e =
    match e.desc with
      | Ident _ -> true
      | _ -> false

  let int ?pos n =
    let t = T.int in
    make ?pos ~t (Cst (Int n))

  let float ?pos ?(t=T.float) x =
    make ?pos ~t (Cst (Float x))

  let bool ?pos b =
    make ?pos ~t:T.bool (Cst (Bool b))

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

  let variant ?pos l e =
    make ?pos (Variant (l,e))

  let unit ?pos () =
    let t = T.unit in
    record ?pos ~t []

  let string ?pos ?t s =
    let t = maybe T.string t in
    make ?pos ~t (Cst (String s))

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

  let bot ?pos ?t () =
    make ?t (Cst Bot)

  let array ?pos ?t a =
    make ?pos ?t (Array a)

  let field ?pos ?t e l =
    make ?pos ?t (Field (e, l))

  let coerce ~t e =
    make (Coerce (e, t))

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

  let alloc ?pos t =
    make ?pos ~t (Alloc t)

  let get_ref ?t r =
    app ?t (make (Cst Get)) ["",r]

  let set_ref r e =
    app ~t:T.unit (make (Cst Set)) ["",r; "",e]

  (** Build a conditional. *)
  let cond ?t b ?el th =
    let t =
      if th.t <> None then
        let t = typ th in
        Some (snd (T.split_arr t))
      else
        None
    in
    let el =
      match el with
      | None -> ["else",fct [] (unit ())]
      | Some el -> ["else",el]
    in
    app ?t (make (Cst If)) (["",b; "then",th]@el)

  (**  *)
  let init e0 e =
    let b = ident ~t:T.bool Ident.init in
    let e0 = quote e0 in
    let e = quote e in
    cond b e0 ~el:e

  (** Create a fresh (temporary) variable. *)
  let fresh_var =
    let counter = ref [] in
    fun ?(name="tmp") () ->
      let n = ref (-1) in
      let rec aux = function
        | (x,k)::t when x = name -> n := k; (x,k+1)::t
        | xk::t -> xk::(aux t)
        | [] -> aux [name,0]
      in
      counter := aux !counter;
      Printf.sprintf "_%s%d" name !n

  (** Execute a program. *)
  let run e =
    let e = app (make (Cst Expand)) ["",quote e] in
    let x = fresh_var () in
    let state = fresh_var () in
    let run = app (field (ident x) "loop") ["init", bool true; "", ident state] in
    let run = letin state (app (field (ident x) "alloc") []) run in
    let e = letin x e run in
    e

  (** Split the bool / then / else in the arguments of an if. *)
  let bte args =
    List.assoc "" args,
    List.assoc "then" args,
    List.assoc "else" args

  let emit_type e =
    (* Printf.printf "emit_type: %s:%s\n%!" (to_string e) (T.to_string (typ e)); *)
    T.emit (typ e)

  (** Operations on free variables. *)
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

  (** {2 Type inference} *)

  (** Typing error. *)
  exception Typing of pos * string

  let rec infer_type ?(annot=fun e -> ()) env e =
    (* Printf.printf "infer_type:\n%s\n\n\n%!" (to_string e); *)
    let infer_type = infer_type ~annot in

    (* let infer_type env e = *)
      (* let ans = infer_type env e in *)
      (* Printf.printf "infer_type:\n%s\n=>\n%s\n:\n%s\n\n\n%!" (to_string e) (to_string ans) (T.to_string (typ ans)); *)
      (* ans *)
    (* in *)

    (* let infer_type env e = *)
    (* let e = infer_type env e in *)
    (* Printf.printf "inferred: %s : %s\n%!" (to_string e) (T.to_string (typ e)); *)
    (* e *)
    (* in *)

    let infer_type ?(level=false) env e =
      if level then
        (
          T.enter_level ();
          let ans = infer_type env e in
          T.leave_level ();
          ans
        )
      else
        infer_type env e
    in
    let (<:) = T.subtype (T.Env.defs env) in
    let type_error e s =
      Printf.ksprintf (fun s -> annot e; raise (Typing (e.pos, s))) s
    in
    (** Try to coerce e into a value of type t. *)
    let coerce e t =
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
        type_error e "This expression has type %s but expected to be of type %s." (T.to_string te) (T.to_string ~env t)
    in

    let ret desc t = { e with desc = desc; t = Some t } in
    let ans =
      (* match e.t with *)
      (* | Some t -> e *)
      (* | None -> *)
      let desc = e.desc in
      match desc with
      | Ident "#dt" -> ret desc T.float
      | Ident "#init" -> ret desc T.bool
      | Ident x ->
        (
          try
            let t = T.instantiate (T.Env.typ env x) in
            ret desc t
          with
          | Not_found -> type_error e "Unbound value %s." x
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
        let env' = List.map (fun (l,x,t,o) -> x,([],t)) ta in
        let env = T.Env.merge env' env in
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
            if T.is_closed t then
              ret e.desc t
            else
              infer_type env e
          | _ -> infer_type env e
        in
        let t = typ e in
        (* TODO: this is a hack, we should do proper unification *)
        (
          match (T.unvar t).T.desc with
          | T.Var v ->
            let a = List.map (fun (l,e) -> l,(typ e,false)) a in
            let t = T.fresh_var () in
            v := T.Link (T.arr a t)
          | _ -> ()
        );
        if not (T.is_arr t) then
          type_error e "This expression of type %s is not a function; it cannot be applied." (T.to_string t);
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
                    type_error expr "The expression has type %s. It cannot be applied to this many arguments." (T.to_string t)
                  else
                    type_error expr "The function applied to this argument has type %s. This argument cannot be applied with label %s." (T.to_string t) l;
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
            (* failwith "Partial application." *)
            type_error e "Partial application not handled (yet)."
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
              let r = reference (make (Coerce (bot (), t))) in
              let tret = t in
              let b,t,e = bte a in
              (* TODO: can we avoid a globally generated fresh name? *)
              let x = fresh_var ~name:"ifref" () in
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
          assert (not (Ident.is_meta x));
          let t = T.fresh_var () in
          let def =
            (* TODO: is this the proper level? *)
            let env = T.Env.add_t env x t in
            infer_type ~level:true env l.def
          in
          if not ((typ def) <: t) then
            failwith "ERROR (TODO) in let rec";
          if not (T.free_vars (typ def) = []) then
            type_error l.def "Expression has type %s but free variables are not allowed in recursive definitions." (T.to_string (typ def));
          let env = T.Env.add env x (T.generalize (typ def)) in
          let body = infer_type env l.body in
          ret (Let { l with def; body }) (typ body)
        else
          let def = infer_type ~level:true env l.def in
          if !Config.Debug.Typing.show_decl_types then Printf.printf "%s : %s\n\n%!" l.var (T.to_string (typ def));
          let def = if l.var = "#dt" then coerce def T.float else def in
          let env = T.Env.add env l.var (T.generalize (typ def)) in
          let body = infer_type env l.body in
          ret (Let { l with def; body }) (typ body)
      | Cst c ->
        (
          let ret t = ret (Cst c) t in
          match c with
          | Bot -> ret (T.fresh_var ~level:(-1) ())
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
          | Expand ->
            let a = T.fresh_var () in
            let s = T.fresh_evar () in
            let m = T.monad s a in
            let arg = T.arr [] a in
            let t = T.arr ["",(arg,false)] m in
            ret t
        )
      | Alloc t ->
        (*
        (* We don't want this variable to be generalized, ever. Or do we? We
           should at least lower the level so that the variable doesn't immediately
           get generalized. *)
        let t = T.fresh_var ~level:(-1) () in
        ret (Alloc t) t
        *)
         ret (Alloc t) t
      | Coerce (e, t) ->
        let e = infer_type env e in
        let t = T.expand env t in
        let e = coerce e t in
        e
      | Ref e ->
        let e = infer_type env e in
        if T.is_arr (typ e) then
          type_error e "This expression has type %s but references are only allowed on data types." (T.to_string (typ e));
        let t = typ e in
        let t = T.ref t in
        ret (Ref e) t
      | External ext ->
        ret (External ext) (ext.ext_t [])
      | Array a ->
        let t = T.fresh_var () in
        let a =
          List.map
            (fun e ->
              let e = infer_type env e in
              let te = typ e in
              if not (t <: te) then
                type_error e "This expression has type %s but %s was expected." (T.to_string te) (T.to_string t);
              e
            ) a
        in
        ret (Array a) (T.array t)
      | Record r ->
        let r = List.map (fun (l,e) -> l, infer_type env e) r in
        let tr = List.map (fun (l,e) -> l,(typ e,false)) r in
        ret (Record r) (T.record tr)
      | Module r ->
        let env, r =
          List.fold_map
            (fun env (l,e) ->
              let e = infer_type ~level:true env e in
              let t = typ e in
              let env = T.Env.add env l (T.generalize t) in
              env, (l,e)
            ) env r
        in
        let tr = List.map (fun (l,e) -> l,(typ e,false)) r in
        ret (Module r) (T.record tr)
      | Field (r, l) ->
        let r = infer_type env r in
        let tr = typ r in
        if not (tr <: (T.record ~row:true [])) then
          type_error r "This expression has type %s but expected to be a record." (T.to_string (typ r));
        let t = T.fresh_var () in
        if not (tr <: (T.record ~row:true [l,(t,false)])) then
          type_error r "This record does not have a member %s." l;
        ret (Field (r,l)) t
      | Replace_fields (r, l) ->
        let r = infer_type env r in
        let tr = typ r in
        let l = List.map (fun (l,(e,o)) -> l,(infer_type env e,o)) l in
        if not (tr <: (T.record ~row:true [])) then
          type_error r "This expression has type %s but expected to be a record." (T.to_string (typ r));
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
      | While(b,e) ->
        let b = infer_type env b in
        let b = coerce b T.bool in
        let e = infer_type env e in
        let e = coerce e (T.arrnl [] T.unit) in
        ret (While(b,e)) T.unit
      | For(i,b,e,f) ->
        let b = infer_type env b in
        let e = infer_type env e in
        let f =
          let env = T.Env.add_t env i T.int in
          infer_type env f
        in
        let b = coerce b T.int in
        let e = coerce e T.int in
        let f = coerce f (T.arrnl [] T.unit) in
        ret (For(i,b,e,f)) T.unit
      | Variant(l,e) ->
        let t = T.variant () in
        ret (Variant(l,e)) t
    in
    (
      match ans.desc with
      | Let _ -> ()
      | _ -> annot ans
    );
    ans

  (** Infer the type of an expression. *)
  let infer_type ?(annot=false) ?(env=T.Env.empty) e =
    let annotations = ref [] in
    let out fname x =
      annotations := List.map_assoc ~d:"" (fun y -> y ^ x) fname !annotations
    in
    let annot_type (p1,p2) t =
      let fname = p2.Lexing.pos_fname in
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
      if p1.Lexing.pos_lnum > 0 then out fname a
    in
    let annot, annot_final =
      if annot then
        (fun e -> try annot_type e.pos (typ e) with _ -> ()),
        (fun () ->
          List.iter
            (fun (fname,x) ->
              if fname <> "" then
                Common.file_out (Filename.chop_extension fname ^ ".annot") x
            ) !annotations)
      else
        (fun _ -> ()), (fun () -> ())
    in
    try
      let e = infer_type ~annot env e in
      annot_final ();
      e
    with
    | e -> annot_final (); raise e

  (** {2 Reduction} *)

  let split_fun e =
    match e.desc with
    | Fun (a,e) -> a,e
    | _ -> assert false

  (** A value is something that can be substituted. *)
  let rec is_value e =
    (* Printf.printf "is_value: %s\n%!" (to_string e); *)
    match e.desc with
      | Ident x -> not (Ident.is_meta x)
      | Fun _ | Cst _ | External _ -> true
      | Record r ->
        (* TODO *)
        (* assert (List.for_all (fun (l,e) -> is_value e) r); *)
        true
      | Array a ->
        (* TODO *)
        assert (List.for_all is_value a);
        true
      | Field (e, l) -> is_value e
      | _ -> false

  module BB = B.Builder

  (** State for beta-reduction. All lists are in "reversed" order, i.e. most
      recent declaration at the top (including [rs_let]). *)
  type reduce_state =
    {
      rs_let : (string * t) list;
      (** Let declarations. *)
      rs_fresh : int;
      (** Fresh variable generator. *)
      rs_refs : (t * (string * T.t) list);
      (** State identifier, and references allocated in the state. *)
    }

  module RS = struct
    type t = reduce_state

    (** Empty state for beta-reduction. *)
    let create () =
      let rs_refs =
        let t = T.fresh_evar () in
        let s = ident ~t (Ident.state ()) in
        (s, [])
      in
      {
        rs_let = [];
        rs_fresh = -1;
        rs_refs;
      }

    (** Generate a fresh variable name. *)
    let fresh_var ?(name="x") state =
      let state = { state with rs_fresh = state.rs_fresh + 1 } in
      (* Printf.printf "fresh var: _%s%d\n%!" name state.rs_fresh; *)
      state, Printf.sprintf "_%s%d" name state.rs_fresh

    let state rs =
      let state, _ = rs.rs_refs in
      rs, state

    (** Add a reference to a state. *)
    let add_state rs r t =
      let state, refs = rs.rs_refs in
      let refs = (r,t)::refs in
      { rs with rs_refs = (state,refs) }
  end

  (** Add the let declarations of a state to a program. *)
  let expand_let state prog =
    let prog = List.fold_left (fun e (x,v) -> letin x v e) prog state.rs_let in
    let state = { state with rs_let = [] } in
    state, prog

  (** Normalize an expression by performing beta-reductions and
      builtins-reductions. *)
  let rec reduce ~subst ~state expr =
    (* Printf.printf "reduce:\n%s\n\n%!" (to_string expr); *)
    (* Printf.printf "subst: %s\n\n%!" (String.concat_map ", " (fun (x,e) -> if List.mem x ["#dt";"_meta0";"_meta1"] then Printf.sprintf "%s <- %s" x (to_string e) else "") subst); *)
    let reduce ?(subst=subst) ~state expr = reduce ~subst ~state expr in

    (** Meta-variables get added at the end of substitutions. This is really
        weired but I think this is the right way... *)
    let subst_add_meta ss x e =
      let rec aux l =
        match l with
        | (y,_)::_ when Ident.is_meta y -> (x,e)::l
        | s::t -> s::(aux t)
        | [] -> [x,e]
      in
      aux ss
    in

    (** Perform a substitution. *)
    let rec substs ss e =
      let desc =
        (* Printf.printf "subst: %s\n%!" (to_string e); *)
        match e.desc with
        | Ident x ->
          let rec aux = function
            | (y,e)::ss when y = x -> (substs ss e).desc
            | (y,e)::ss -> aux ss
            | [] -> e.desc
          in
          aux ss
        | Fun (x,e) ->
          let x = List.map (fun (l,(x,o)) -> l,(x,Option.map (substs ss) o)) x in
          let xsx = List.map (fun (l,(x,o)) ->
            let x' = fresh_var ~name:"l" () in
            (l,(x',o)),(x,ident x')) x
          in
          let x, sx = List.split xsx in
          let ss = sx@ss in
          Fun (x, substs ss e)
(*
        | Fun (x,e) ->
          let x = List.map (fun (l,(x,o)) -> l,(x,Option.map (substs ss) o)) x in
          let bv = List.map (fun (l,(x,o)) -> x) x in
          let ss = List.remove_all_assocs bv ss in
          Fun (x, substs ss e)
*)
        | Let l ->
          if l.recursive then
            let var = fresh_var ~name:"l" () in
            let ss = (l.var,ident var)::ss in
            let def = substs ss l.def in
            let body = substs ss l.body in
            Let { l with var; def; body }
          else
            let def = substs ss l.def in
            if Ident.is_meta l.var then
              let ss = List.remove_all_assoc l.var ss in
              let body = substs ss l.body in
              Let { l with def; body }
            else
              let var = fresh_var ~name:"l" () in
              let ss = (l.var,ident var)::ss in
              let body = substs ss l.body in
              Let { l with var; def; body }
(*
        | Let l ->
          (* l.var is supposed to be already alpha-converted so that there is no
             capture. *)
          let ss' = List.remove_all_assoc l.var ss in
          let def = substs (if l.recursive then ss' else ss) l.def in
          let ss = ss' in
          let body = substs ss l.body in
          Let { l with def; body }
*)
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
        | Alloc _ | Cst _ | External _ as e -> e
        | Module m ->
          let m = List.map (fun (l,e) -> l, substs ss e) m in
          Module m
        | For (i,b,e,f) ->
          (* TODO: refresh i *)
          let ss = List.remove_all_assoc i ss in
          let s = substs ss in
          For (i, s b, s e, s f)
        | While (b,e) ->
          While (substs ss b, substs ss e)
      in
      { e with desc }
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
              let state, y = RS.fresh_var state in
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
            (
              match b.desc with
              | Cst (Bool true) -> reduce ~subst ~state (app th [])
              | Cst (Bool false) -> reduce ~subst ~state (app el [])
              | _ ->
                let state, th = reduce_quote ~subst ~state th [] in
                let state, el = reduce_quote ~subst ~state el [] in
                state, app e ["",b; "then", quote th; "else", quote el]
            )
          | Cst Expand ->
            let f = List.assoc "" args in
            let mstate = RS.create () in
            let mstate = { state with rs_refs = mstate.rs_refs } in
            let mstate, f = reduce_quote ~subst ~state:mstate f [] in
            (* Fill in types. *)
            let mstate, mstate_ident = RS.state mstate in
            let mstate_evar = typ mstate_ident in
            let mstate_ident = match mstate_ident.desc with Ident s -> s | _ -> assert false in
            let mstate_evar' =
              let t = snd (T.split_arr (typ e)) in
              T.monad_state t
            in
            T.set_evar mstate_evar' mstate_evar;
            let mstate_t =
              let refs = snd mstate.rs_refs in
              T.record (List.map (fun (x,t) -> x,(t,false)) refs)
            in
            Printf.printf "State type: %s\n\n%!" (T.to_string mstate_t);
            T.set_evar mstate_evar mstate_t;
            (* Update state. *)
            let state = { mstate with rs_refs = state.rs_refs } in
            (* Oscillator functions. *)
            let f_alloc = fct [] (alloc mstate_t) in
            let f_loop = fct ["init",(Ident.init,Some (bool false)); "",(mstate_ident,None)] f in
            let ans = record ["alloc", f_alloc; "loop", f_loop] in
            (* Printf.printf "<<<\nexpand:\n%s\nexpanded:\n%s\n>>>\n\n%!" (to_string f) (to_string ans); *)
            state, ans
          | External ext when not (T.is_arr (typ expr)) ->
            (* Printf.printf "EXT %s\n%!" (to_string expr); *)
            (* TODO: better when and reduce partial applications. *)
            (
              try
                let e = ext.ext_implem args in
                reduce ~subst ~state e
              with
              | Cannot_reduce -> state, app e args
            )
          | _ -> state, app e args
        )
      | While(b,e) ->
        let state, b = reduce ~subst ~state b in
        let state, e = reduce_quote ~subst ~state e [] in
        let e = quote e in
        state, make (While(b,e))
      | For(i,b,e,f) ->
        let state, i' = RS.fresh_var state in
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
          (
            assert (not (Ident.is_meta l.var));
            (* TODO: think hard about this *)
            let _ = assert false in
            (* Create a reference (on bot) for the recursive value. *)
            let t = typ l.def in
            let tref = T.ref t in
            let r = bot ~t:t () in
            let r = reference ~t:tref r in
            let state, rx = RS.fresh_var state in
            let irx = ident ~t:tref rx in
            let state = { state with rs_let = (rx,r)::state.rs_let } in
            let def = l.def in
            let state, def = reduce ~subst:((l.var,get_ref ~t irx)::subst) ~state def in
            let body = l.body in
            let body = letin l.var (get_ref ~t irx) body in
            let e = seq (set_ref irx def) body in
            (* Printf.printf "RECURSIVE: %s\n=>\n%s\n%!" (to_string expr) (to_string e); *)
            reduce ~subst ~state e
          )
        else
          if Ident.is_meta l.var then
            if is_value l.def then
              (* let () = Printf.printf "*** META:\n%s\n\n%!" (to_string expr) in *)
              let state, def = reduce ~subst ~state l.def in
              let subst = List.remove_all_assoc l.var subst in
              let state' = { state with rs_let = [] } in
              let state', body = reduce ~subst ~state:state' l.body in
              let state', body = expand_let state' body in
              let state = { state' with rs_let = state.rs_let } in
              (* let () = Printf.printf "*** META let:\n%s\n\n%!" (to_string body) in *)
              let state, ans = reduce ~subst:[l.var,def] ~state body in
              (* Printf.printf "*** META ans:\n%s\n\n%!" (to_string (snd (expand_let state ans))); *)
              state, ans
            else
              (* TODO: use state *)
              let var = fresh_var ~name:"meta" () in
              let e = letin l.var (ident var) l.body in
              let e = letin var l.def e in
              (* Printf.printf "*** META:\n%s\n\n%!" (to_string e); *)
              (* let state, ans = reduce ~subst ~state e in *)
              (* Printf.printf "*** META ans:\n%s\n\n%!" (to_string (snd (expand_let state ans))); *)
              (* state, ans *)
              reduce ~subst ~state e
          else
            let state, def = reduce ~subst ~state l.def in
            if is_value def then
              let subst = (l.var,def)::subst in
              reduce ~subst ~state l.body
            else
              let state, var = RS.fresh_var state in
              let state = { state with rs_let = (var,def)::state.rs_let } in
              let subst = (l.var,ident var)::subst in
              reduce ~subst ~state l.body
      | Ref e ->
        let t = typ e in
        let pos = e.pos in
        let state, s = RS.state state in
        let state, sr = RS.fresh_var ~name:"ref" state in
        let state = RS.add_state state sr t in
        let r = field ~pos ~t s sr in
        let e = init (set_ref r e) (unit ()) in
        let e = seq ~pos e r in
        reduce ~state e
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
          | _ ->
            (* let s = String.concat_map "\n" (fun (l,e) -> Printf.sprintf "*** %s = %s" l (to_string e)) subst in *)
            (* Printf.printf "%s\n%!" s; *)
            (* failwith (Printf.sprintf "Cannot reduce field \"%s\" of %s : %s." l (to_string r) (T.to_string (typ r))) *)
            state, field ~t:(typ expr) r l
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
      | Variant(l,e) ->
        let state, e = reduce ~state e in
        state, variant l e
      | Alloc _ | Cst _ | External _ -> state, expr
    in
    (* Printf.printf "reduce: %s\n=>\n%s\n\n%!" (to_string expr) (to_string e); *)
    (* Ensure that types and locations are preserved. *)
    state, { expr with desc = e.desc }

  (** Reduce a quote (of type (args) -> 'a). *)
  and reduce_quote ~subst ~state prog args =
    let old_let = state.rs_let in
    let state = { state with rs_let = [] } in
    let t = snd (T.split_arr (typ prog)) in
    let prog = app ~t prog args in
    let state, prog = reduce ~subst ~state prog in
    let state, prog = expand_let state prog in
    let state = { state with rs_let = old_let } in
    state, prog

  (** Reduce a program. *)
  let reduce ?(subst=[]) ?(state=RS.create ()) e =
    let state, e = reduce ~subst ~state e in
    let state, e = expand_let state e in
    e

  let rec emit prog expr =
    (* Printf.printf "emit:\n%s\n\n" (to_string expr); *)
    let rec aux prog expr =
      (* Printf.printf "emit:\n%s\n\n" (to_string expr); *)
      let emit prog expr = aux prog expr in
      let emit_eqs prog expr =
        let prog = BB.push prog in
        let prog = emit prog expr in
        let prog, e = BB.pop prog in
        prog, e
      in
      let etyp e = emit_type e in
      let rec emit_expr prog expr =
        (* Printf.printf "emit_expr:\n%s\n\n%!" (to_string expr); *)
        (* Printf.printf "of type: %s\n\n%!" (T.to_string (typ expr)); *)
        match expr.desc with
        | Ident x ->
          prog, BB.var prog x
        | App ({ desc = Cst Get }, ["",x]) ->
          let prog, x = emit_expr prog x in
          prog, B.E.get x
        | App ({ desc = Cst Set }, ["",x; "",e]) ->
          let prog, x = emit_expr prog x in
          let prog, e = emit_expr prog e in
          prog, B.E.set x e
        | App ({ desc = External e } as ext, a) ->
          let prog, a =
            List.fold_map
              (fun prog (l,e) ->
                assert (l = "");
                let prog, e = emit_expr prog e in
                prog, e
              ) prog a
          in
          let a = Array.of_list a in
          e.ext_backend (typ ext) prog a
        | Alloc t ->
          prog, B.E.alloc (T.emit t)
        | App ({ desc = Cst If }, a) ->
          let b,t,e = bte a in
          let t = unquote t in
          let e = unquote e in
          let prog, b = emit_expr prog b in
          let prog, t = emit_eqs prog t in
          let prog, e = emit_eqs prog e in
          prog, B.If (b,t,e)
        | While (b,e) ->
          let e = unquote e in
          let prog, b = emit_expr prog b in
          let prog, e = emit_eqs prog e in
          prog, B.While (b,e)
        | For (i,b,e,f) ->
          let f = unquote f in
          let prog, b = emit_expr prog b in
          let prog, e = emit_expr prog e in
          let prog = BB.alloc prog i B.T.Int in
          let prog, f = emit_eqs prog f in
          let i =
            match BB.var prog i with
            | B.Var i -> i
            | _ -> assert false
          in
          prog, B.For(i,b,e,f)
        | Cst c ->
          (
            match c with
            | String s -> prog, B.Val (B.V.string s)
            | Float x -> prog, B.Val (B.V.float x)
            | Int x -> prog, B.Val (B.V.int x)
            | Bool b -> prog, B.Val (B.V.bool b)
            | Bot -> prog, B.Val B.V.bot
          )
        | External e ->
          (* For constants such as pi. *)
          e.ext_backend (typ expr) prog [||]
        | Ref e ->
          emit_expr prog e
        | Record [] ->
          prog, B.E.unit
        | Record r ->
          (* TODO: cleanly handle commutativity and subtyping... *)
          let t = etyp expr in
          let t = B.T.get_record t in
          let prog, r = List.fold_map (fun prog (l,e) -> emit_expr prog e) prog r in
          prog, B.E.build_record t r
        | Field (e, l) ->
          (* Printf.printf "field: %s.%s : %s\n%!" (to_string e) l (T.to_string (typ e)); *)
          let l =
            let r =
              match (T.unvar (typ e)).T.desc with
              | T.Record (r,_) -> r
              | _ -> assert false
            in
            (* TODO: ensure in some way that this numbering won't be broken by
               polymorphism... *)
            List.index_pred (fun (l',_) -> l' = l) r
          in
          let t = B.T.get_record (T.emit (typ e)) in
          let prog, e = emit_expr prog e in
          prog, B.E.field t e l
        | Array _ ->
          failwith "Trying to emit constructed array."
      in
      (* Printf.printf "emit: %s\n\n%!" (to_string expr); *)
      match expr.desc with
      | Let ({ def = { desc = External _ } } as l)
      | Let ({ def = { desc = Fun _ } } as l) ->
        Printf.printf "Ignoring function %s...\n%!" l.var;
        emit prog l.body
      | Let ({ def = { desc = Record _ } } as l) ->
        Printf.printf "Ignoring record %s...\n%!" l.var;
        emit prog l.body
      | Let ({ def = { desc = Module _ } } as l) ->
        Printf.printf "Ignoring module %s...\n%!" l.var;
        emit prog l.body
      | Let l ->
        assert (l.var <> Ident.dt);
        (*
          if l.recursive then
          let prog = BB.alloc prog l.var t in
          let prog, def = emit_expr prog l.def in
          let prog = BB.eq prog l.var def in
          emit prog l.body
          else
        *)
        assert (not l.recursive);
        let prog, def = emit_expr prog l.def in
        let prog =
          if T.is_unit (typ l.def) then
            BB.cmd prog def
          else
            let prog = BB.alloc prog l.var (etyp l.def) in
            BB.eq prog (BB.var prog l.var) def
        in
        emit prog l.body
      | Record [] ->
        (* This case is used for return values (which have to be unit) of
           subprograms (if, while, etc). *)
        prog
      | _ ->
        let e = expr in
        let t = typ e in
        let prog, e = emit_expr prog e in
        let e = if T.is_unit t then e else B.E.return e in
        BB.cmd prog e
    in
    aux prog expr

  (** Emit a program: generate backend code. *)
  let emit ?(builder=BB.create ()) e =
    emit builder e
end

module E = Expr

(** Operations on modules. *)
module Module = struct
  type instr =
  | Decl of string * E.t
  | Expr of E.t
  | Type of string * T.t
  | Variant of string * T.t

  type t = instr list

  let to_string = function
    | Decl (x,e) -> Printf.sprintf "%s = %s" x (E.to_string e)
    | Expr e -> Printf.sprintf "%s" (E.to_string e)
    | Type (l,t) -> Printf.sprintf "type %s = %s" l (T.to_string t)
    | Variant (e,t) -> Printf.sprintf "variant `%s of %s" e (T.to_string t)

  let to_string m =
    String.concat_map "\n\n" to_string m

  (* This is registered later in order to break cyclic dependencies. *)
  let parse_file_fun : (string -> t) ref = ref (fun _ -> assert false)
  let parse_file f = !parse_file_fun f

  let to_expr m =
    let n = ref (-1) in
    let fresh () = incr n; Printf.sprintf "_m%d" !n in
    List.fold_left
      (fun ee e ->
        match e with
        | Expr e -> E.letin (fresh ()) e ee
        | Decl (x, e) -> E.letin x e ee
        | Type _ -> ee
        | Variant _ -> ee
      ) (E.unit ()) (List.rev m)
end

module M = Module
