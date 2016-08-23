(** Internal representation of the language and operations to manipulate it
    (typechecking, reduction, etc.). *)

(* TODO: propagate mutability of records in types *)
(* TODO: propagate effects in types *)

open Common
open Stdlib

module T = Type

(** Special identifiers. *)
module Ident = struct
  type t = string

  (** Prefix for special variables, also called meta-variables (prefixed
        variables are guaranteed not to occur in saml files). *)
  let prefix = "#"

  (** Is a variable a meta-variable? *)
  let is_meta x = x.[0] = '#'

  (** Dt meta-variable. *)
  let dt = "#dt"

  (** Boolean meta-variable indicating whether we are on first round. *)
  (* let init = "#init" *)

  (** Meta-variable for state record. *)
  let state = "#state"
end

(** A value. *)
type value =
  | Unit
  | Int of int
  | Float of float
  | Bool of bool
  | String of string

(** An expression. *)
type t =
  {
    desc : desc; (** The expression. *)
    pos : pos; (** Position in source file. *)
  }
 (** Contents of an expression. *)
 and desc =
   | Value of value (** A value. *)
   | Ident of Ident.t (** A variable. *)
   | Fun of (string * (string * t option)) list * t
   (** A function. Arguments are labelled (or not if the label is ""), have a
      variable, and optionally a default value. *)
   | Let of let_t (** A variable declaration. *)
   | App of t * (string * t) list
   | Seq of t * t
   | External of extern
   | Array of t array
   | Record of bool * (string * t) list (** A record, optionally mutable. *)
   | Module of (string * t) list
   (** Modules are basically the same as records except that members can use
      previously defined values, e.g. \{ a = 5; b = 2*a \}. *)
   | Field of t * string (** Field of a record or a module. *)
   | ReplaceField of t * string * t (** Replace a field of a record. *)
   | SetField of t * string * t (** Modify a field in a pointed record. *)
   | For of string * t * t * t
   | While of t * t
   (* | If of t * t * t *)
   | AddressOf of t
   | Alloc of T.t (** Dynamically allocate a value. *)
   | Monadic of monadic (** A monadic operation. *)
 (** Monadic operations. *)
 and monadic =
   | Dt (** dt *)
   | DtFun of t (** Abstract dt. *)
   | Ref of t (** A static reference. *)
   | RefGet of t (** Retrieve the value of a reference. *)
   | RefSet of t * t (** Set the value of a reference. *)
   | RefFun of t (** Abstract references. *)
 (** External values. *)
 and extern =
   {
     ext_name : string; (** Name of the external as useable in scripts. *)
     ext_type : T.t; (** Type. *)
     (* The mutable is to be able to fill in when there is no reduction. It
       should not be mutated otherwise. *)
     mutable ext_reduce : (string * t) list -> t; (** Reduction. *)
     ext_run : t array -> t; (** Execution. *)
   }
 (** Let declarations. *)
 and let_t =
   {
     var : string;
     def : t;
     body : t
   }
type expr = t

(** Create an expression. *)
let make ?(pos=dummy_pos) e =
  {
    desc = e;
    pos = pos;
  }

let ident ?pos s =
  make ?pos (Ident s)

let value ?pos v =
  make ?pos (Value v)

let fct ?pos args e =
  make ?pos (Fun (args, e))

let app ?pos e l =
  make ?pos (App (e, l))

let seq ?pos e1 e2 =
  make ?pos (Seq (e1, e2))

let unit ?pos () =
  make ?pos (Value Unit)

let letin ?pos var def body =
  let l = { var; def; body } in
  make ?pos (Let l)

let record ?pos is_mutable l =
  make ?pos (Record (is_mutable,l))

let field ?pos e x =
  make ?pos (Field (e, x))

(** String representation of an expression. *)
let to_string e : string =
  let pa p s = if p then Printf.sprintf "(%s)" s else s in
  let rec to_string ~tab p e =
    let tabs ?(tab=tab) () = String.make (2*tab) ' ' in
    let tabss () = tabs ~tab:(tab+1) () in
    match e.desc with
    | Ident x -> x
    | Value Unit -> "()"
    | Value (Int n) -> string_of_int n
    | Value (Float f) -> string_of_float f
    | Value (Bool b) -> string_of_bool b
    | Value (String s) -> Printf.sprintf "%S" s
    | Fun (a, e) ->
       let a =
         String.concat_map
           ", "
           (fun (l,(x,d)) ->
             let l = if l = "" || l = x then "" else l ^ ":" in
             let d = match d with None -> "" | Some d -> "=" ^ to_string ~tab:(tab+1) false d in
             Printf.sprintf "%s%s%s" l x d
           ) a
       in
       let e = to_string ~tab:(tab+1) false e in
       pa p (Printf.sprintf "fun (%s) ->%s%s" a (if String.contains e '\n' then ("\n"^(tabs ~tab:(tab+1) ())) else " ") e)
    | App (e, a) ->
       let a = String.concat_map ", " (fun (l,e) -> (if l = "" then "" else (l ^ "=")) ^ to_string ~tab:(tab+1) false e) a in
       pa p (Printf.sprintf "%s(%s)" (to_string ~tab true e) a)
    | Seq (e1, e2) ->
       let e1 = to_string ~tab false e1 in
       let e2 = to_string ~tab false e2 in
       pa p (Printf.sprintf "%s\n%s%s" e1 (tabs ()) e2)
    | Let l ->
       let def = to_string ~tab:(tab+1) false l.def in
       let def =
         if String.contains def '\n' then
           Printf.sprintf "\n%s%s" (tabss ()) def
         else
           Printf.sprintf " %s " def
       in
       let body = to_string ~tab false l.body in
       pa p (Printf.sprintf "%s =%s\n%s%s" l.var def (tabs ()) body)
    | While (c, e) ->
       let c = to_string ~tab false c in
       let e = to_string ~tab:(tab+1) false e in
       pa p (Printf.sprintf "while %s do\n%s%s\n%sdone" c (tabss()) e (tabs()))
    | For (i, a, b, e) ->
       let a = to_string ~tab false a in
       let b = to_string ~tab false b in
       let e = to_string ~tab:(tab+1) false e in
       pa p (Printf.sprintf "for %s = %s to %s do\n%s%s\n%sdone" i a b (tabss()) e (tabs()))
    | AddressOf e ->
       let e = to_string ~tab true e in
       Printf.sprintf "&%s" e
    | Alloc t -> Printf.sprintf "alloc[%s]" (T.to_string t)
    | Array a ->
       let a = Array.to_list a in
       let a = String.concat_map " , " (to_string ~tab:(tab+1) false) a in
       Printf.sprintf "[%s]" a
    | Record (m,r) ->
       if r = [] then "{}" else
         let r = List.map (fun (x,v) -> Printf.sprintf "%s%s = %s" (tabss()) x (to_string ~tab:(tab+1) false v)) r in
         let r = String.concat "\n" r in
         Printf.sprintf "{%s\n%s\n%s}" (if m then "mutable" else "") r (tabs())
    | Module r ->
       if r = [] then "module end" else
         let r = List.map (fun (x,v) -> Printf.sprintf "%s%s = %s" (tabss()) x (to_string ~tab:(tab+1) false v)) r in
         let r = String.concat "\n" r in
         Printf.sprintf "module\n%s\n%send" r (tabs())
    | Field (r,x) ->
       let r = to_string ~tab true r in
       Printf.sprintf "%s.%s" r x
    | ReplaceField (r,x,e) ->
       let r = to_string ~tab true r in
       let e = to_string ~tab false e in
       Printf.sprintf "{ %s with %s = %s }" r x e
    | SetField (r,x,e) ->
       let r = to_string ~tab true r in
       let e = to_string ~tab false e in
       Printf.sprintf "%s.%s <- %s" r x e
    | External e -> "`"^e.ext_name^"`"
    | Monadic Dt -> "dt"
    | Monadic (DtFun e) ->
       let e = to_string ~tab false e in
       pa p (Printf.sprintf "λdt(%s)" e)
    | Monadic (Ref e) ->
       let e = to_string ~tab false e in
       pa p (Printf.sprintf "ref(%s)" e)
    | Monadic (RefGet r) ->
       let r = to_string ~tab true r in
       pa p (Printf.sprintf "!%s" r)
    | Monadic (RefSet (r, e)) ->
       let r = to_string ~tab true r in
       let e = to_string ~tab false e in
       pa p (Printf.sprintf "%s := %s" r e)
    | Monadic (RefFun e) ->
       let e = to_string ~tab false e in
       pa p (Printf.sprintf "λref(%s)" e)
  in
  to_string ~tab:0 false e

let rec free_vars e =
  (* Printf.printf "free_vars: %s\n%!" (to_string e); *)
  let u fv1 fv2 = fv1@fv2 in
  let fv = free_vars in
  match e.desc with
  | Ident x -> [x]
  | Value _ -> []

(** {2 Type inference} *)

(** Typing error. *)
exception Typing of pos * string

(** Infer the type of an expression. *)
let rec infer_type env e =
  (* Printf.printf "infer_type:\n%s\n\n\n%!" (to_string e); *)
  (* Printf.printf "env: %s\n\n" (String.concat_map " , " (fun (x,(_,t)) -> x ^ ":" ^ T.to_string t) env.T.Env.t); *)
  let (<:) = T.subtype env in
  let type_error e s =
    Printf.ksprintf (fun s -> raise (Typing (e.pos, s))) s
  in
  let ensure e t t' =
    if not (t <: t') then
      type_error e "This expression has type %s but %s is expected." (T.to_string t) (T.to_string t');
  in
  let var env = T.var (T.Env.level env) in
  match e.desc with
  | Value Unit -> T.unit ()
  | Value (Bool _) -> T.bool ()
  | Value (Int _) -> T.int ()
  | Value (Float _) -> T.float ()
  | Value (String _) -> T.string ()
  | Ident x ->
     let t = try T.Env.typ env x with Not_found -> type_error e "Unbound variable %s." x in
     T.instantiate t
  | Seq (e1, e2) ->
     let t1 = infer_type env e1 in
     ensure e1 t1 (T.unit ());
     infer_type env e2
  | Let l ->
     let td =
       let env = T.Env.enter env in
       infer_type env l.def
     in
     let env = T.Env.bind env l.var (T.generalize (T.Env.level env) td) in
     infer_type env l.body
  | Fun (a,e) ->
     let a =
       List.map
         (fun (l,(x,d)) ->
           let d,t =
             match d with
             | Some d ->
                let dt = infer_type env d in
                Some d, dt
             | None ->
                None, var env
           in
           let o = d <> None in
           (l,(x,d)), (l,x,t,o)
         ) a
     in
     let a, ta = List.split a in
     let env' = List.map (fun (l,x,t,o) -> x,([],t)) ta in
     let env = T.Env.binds env env' in
     let te = infer_type env e in
     let ta = List.map (fun (l,x,t,o) -> l,(t,o)) ta in
     T.arr ta te
  | App (e, a) ->
     let ta = List.map (fun (l,e) -> l,(infer_type env e,false)) a in
     let te = infer_type env e in
     let tr = var env in
     let te' = T.arr ta tr in
     ensure e te te';
     tr
  | While (c,e) ->
     let tc = infer_type env c in
     ensure c tc (T.bool ());
     let te = infer_type env e in
     ensure e te (T.unit ());
     T.unit ()
  | For (i,a,b,e) ->
     let ta = infer_type env a in
     ensure a ta (T.int ());
     let tb = infer_type env b in
     ensure b tb (T.int ());
     let env = T.Env.bind env i (T.generalize (T.Env.level env) (T.int ())) in
     let te = infer_type env e in
     ensure e te (T.unit ());
     T.unit ()
  | Module l | Record (_,l) ->
     let l = List.map (fun (x,e) -> x, infer_type env e) l in
     T.record l
  | Field (e, x) ->
     let te = infer_type env e in
     let t = var env in
     let te' = T.record [x, t] in
     ensure e te te';
     t
  | SetField (r,x,e) ->
     let tr = infer_type env r in
     let te = infer_type env e in
     ensure r tr (T.record [x,te]);
     T.unit ()
  | External ext -> T.instantiate (T.generalize 0 ext.ext_type)
  | Monadic Dt -> T.float ()
  | Monadic (DtFun e) ->
     let t = infer_type env e in
     T.arrnl [T.float ()] t
  | Monadic (Ref e) ->
     let t = infer_type env e in
     T.reference t
  | Monadic (RefGet e) ->
     let t = infer_type env e in
     let t' = var env in
     ensure e t (T.reference t');
     t'
  | Monadic (RefSet(r,e)) ->
     let tr = infer_type env r in
     let t' = var env in
     ensure r tr (T.reference t');
     let t = infer_type env e in
     ensure e t t';
     T.unit ()
  | Monadic (RefFun(e)) ->
     let t = infer_type env e in
     let s = T.make (EVar (ref None)) in
     T.record
       [
         "init", s;
         "run", T.arrnl [s] t
       ]

let infer_type e = infer_type T.Env.empty e

(** {2 Reduction} *)

(** Expressions which should be inlined. *)
let rec inlinable e =
  match e.desc with
  | Value _ | Fun _ | External _ -> true
  | Ident x ->
     (* TODO: we should not inline them to avoid capture with
     abstraction. However, this causes problems because refs do not reduce
     propely... We should probably remove them from the substitution when around
     a RefFun. *)
     (* not (Ident.is_meta x) *)
     true
  | Record (m,l) -> not (m && List.for_all (fun (x,e) -> inlinable e) l)
  | AddressOf { desc = Field (r,x) } -> inlinable r
  | _ -> false

(** Monadic reduction state. *)
module RS = struct
  type t =
    {
      var : int; (** Counter for fresh variables. *)
      cell : int; (** Counter for cells. *)
      cells : (string * expr) list; (** Allocated memory cells. *)
      context : expr -> expr; (** Reduction context (declarations, sequences, etc.). *)
    }

  let empty =
    {
      var = 0;
      cell = 0;
      cells = [];
      context = id
    }

  (** Generate a fresh variable name. *)
  let var ?(name="x") state =
    let n = state.var in
    let state = { state with var = state.var + 1 } in
    state, Printf.sprintf "_%s%d" name n

  (** Generate a fresh variable name. *)
  let cell ?(name="r") state =
    let n = state.cell in
    let state = { state with cell = state.cell + 1 } in
    state, Printf.sprintf "_%s%d" name n

  let add_cell state r e =
    (* TODO: assert that e is closed *)
    { state with cells = (r,e)::state.cells }
      
  let context state = state.context

  let add_context state f =
    { state with context = fun e -> state.context (f e) }
end

(** Normalize an expression by performing
      beta-reductions and builtins-reductions. *)
let rec reduce ~subst ~state expr =
  let reduce ?(subst=subst) ~state expr = reduce ~subst ~state expr in

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
      | App (e, a) ->
         let a = List.map (fun (l,e) -> l, substs ss e) a in
         App (substs ss e, a)
      | Seq (e1, e2) ->
         let e1 = substs ss e1 in
         let e2 = substs ss e2 in
         Seq (e1, e2)
      | Let l ->
         let def = substs ss l.def in
         let ss = List.remove_all_assocs [l.var] ss in
         let body = substs ss l.body in
         let l = { l with def; body } in
         Let l
      | Value _ | External _ -> e.desc
      | Fun (x,e) ->
         let x = List.map (fun (l,(x,o)) -> l,(x,Option.map (substs ss) o)) x in
         let bv = List.map (fun (l,(x,o)) -> x) x in
         let ss = List.remove_all_assocs bv ss in
         Fun (x, substs ss e)
      | AddressOf e ->
         let e = substs ss e in
         AddressOf e
      | Record (m,l) ->
         let l = List.map (fun (x,e) -> x, substs ss e) l in
         Record (m,l)
      | Field (r,x) ->
         let r = substs ss r in
         Field (r,x)
      | ReplaceField(r,x,e) ->
         let r = substs ss r in
         let e = substs ss e in
         ReplaceField(r,x,e)
      | SetField(r,x,e) ->
         let r = substs ss r in
         let e = substs ss e in
         SetField(r,x,e)
      | Monadic Dt -> e.desc
      | Monadic (DtFun e) ->
         (* TODO: dt could occur as free variable of some substitution... *)
         let e = substs ss e in
         Monadic (DtFun e)
      | Monadic (Ref e) ->
         let e = substs ss e in
         Monadic (Ref e)
      | Monadic (RefGet e) ->
         let e = substs ss e in
         Monadic (RefGet e)
      | Monadic (RefSet(r,e)) ->
         let r = substs ss r in
         let e = substs ss e in
         Monadic (RefSet(r,e))
      | Monadic (RefFun e) ->
         (* TODO: think harder about variable capture in this case... *)
         assert false;
         let ss = List.remove_all_assocs [Ident.state] ss in
         let e = substs ss e in
         Monadic (RefFun e)
                 (* | _ -> failwith ("Implement substitution in " ^ to_string e) *)
    in
    { e with desc }
  in
  let s = substs subst in
  let reduce_block ?(allow_refs=false) ~subst ~state e =
    let cells = state.RS.cells in
    let context = state.RS.context in
    let state = { state with RS.context = id } in
    let state, e = reduce ~subst ~state e in
    let e = state.RS.context e in
    let state = { state with RS.context } in
    if not allow_refs then assert (List.length cells = List.length state.RS.cells);
    state, e
  in
  (* Printf.printf "reduce:\n%s\n\n%!" (to_string expr); *)
  let state, e =
    match expr.desc with
    | Ident x -> state, s expr
    | Fun (a, e) ->
       (* We have to substitute optionals and rename variables for
           substitution to avoid captures. *)
       let state, a =
         List.fold_map
           (fun state (l,(x,o)) ->
             let o = Option.map s o in
             let state, y = RS.var state in
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
       begin
         match e.desc with
         | Fun (a,e) ->
            let rec aux a e = function
              | (l,v)::args ->
                 let (x,_), a = List.assoc_rm l a in
                 let e = letin x v e in
                 aux a e args
              | [] ->
                 (* Printf.printf "app: %s\n%!" (to_string expr); *)
                 if List.for_all (fun (l,(x,o)) -> o <> None) a then
                   (* All remaining arguments are optional *)
                   List.fold_left (fun e (l,(x,o)) -> letin x (Option.get o) e) e a
                 else
                   (* Partial application *)
                   fct a e
            in
            reduce ~state (aux a e args)
         | External ext -> state, ext.ext_reduce args
         | _ -> state, app e args
       end
    | Seq (e1, e2) ->
       let state, e1 = reduce ~subst ~state e1 in
       let state =
         begin
           match e1.desc with
           | Value Unit -> state
           | _ -> RS.add_context state (fun e -> seq e1 e)
         end
       in
       reduce ~subst ~state e2
    | Let l ->
       let state, def = reduce ~subst ~state l.def in
       if inlinable def then
         let subst = (l.var,def)::subst in
         reduce ~subst ~state l.body
       else
         let state, var = RS.var state in
         let state = RS.add_context state (fun e -> letin var def e) in
         let subst = (l.var,ident var)::subst in
         reduce ~subst ~state l.body
    | While (c,e) ->
       let state, c = reduce ~subst ~state c in
       let state, e = reduce_block ~subst ~state e in
       state, make (While (c,e))
    | For (i,a,b,e) ->
       let state, a = reduce ~subst ~state a in
       let state, b = reduce ~subst ~state b in
       let state, e = reduce_block ~subst ~state e in
       state, make (For(i,a,b,e))
    | Value _ | External _ -> state, expr
    | AddressOf e ->
       let state, e = reduce ~subst ~state e in
       state, make (AddressOf e)
    | Module m ->
       (* TODO: this is a hack *)
       (* TODO: handle duplicate labels... *)
       let ctx = List.fold_left (fun ctx (l,e) e' -> ctx (letin l e e')) id m in
       let m = List.map (fun (l,e) -> l, ident l) m in
       reduce ~subst ~state (ctx (record false m))
    | Record (m,l) ->
       let state, l =
         List.fold_map
           (fun state (x,e) ->
             let state, e = reduce ~subst ~state e in
             state, (x,e))
           state l
       in
       state, make (Record (m,l))
    | Field (e, x) ->
       let state, e = reduce ~subst ~state e in
       begin
         match e.desc with
         | Record (_,l) -> state, List.assoc x l
         | _ -> state, field e x
       end
    | ReplaceField (r,x,e) ->
       let state, r = reduce ~subst ~state r in
       let state, e = reduce ~subst ~state e in
       state,
       begin
         match r.desc with
         | Record (m,l) ->
            let l = List.remove_assoc x l in
            let l = (x,e)::l in
            record m l
         | _ -> make (ReplaceField (r,x,e))
       end
    | SetField (r,x,e) ->
       let state, r = reduce ~subst ~state r in
       let state, e = reduce ~subst ~state e in
       state, make (SetField (r,x,e))
    | Monadic Dt -> state, make (Ident Ident.dt)
    | Monadic (DtFun e) ->
       let context = state.RS.context in
       let state = { state with RS.context = id } in
       let state, e = reduce ~subst ~state e in
       let e = RS.context state e in
       let e = fct ["",(Ident.dt,None)] e in
       let state = { state with RS.context } in
       state, e
    | Monadic (Ref e) ->
       let state, x = RS.cell state in
       (* assert (free_vars e = []); *)
       let state = RS.add_cell state x e in
       let e = field (ident (Ident.state)) x in
       let e = make (AddressOf e) in
       reduce ~subst ~state e
    | Monadic (RefGet r) ->
       let state, r = reduce ~subst ~state r in
       begin
         match r.desc with
         | AddressOf e -> state, e
         | _ ->
            (* TODO: this should not happen... *)
            (* state, make (Monadic (RefGet r)) *)
            assert false
       end
    | Monadic (RefSet (r, e)) ->
       let state, r = reduce ~subst ~state r in
       begin
         match r.desc with
         | AddressOf { desc = Field (r, x) } ->
            reduce ~subst ~state (make (SetField (r, x, e)))
         | _ ->
            (* TODO: this should not happen... *)
            (* state, make (Monadic (RefSet (r, e))) *)
            assert false
       end
    | Monadic (RefFun e) ->
       let cells = state.RS.cells in
       let context = state.RS.context in
       let state = { state with RS.cells = []; context = id } in
       let state, e = reduce ~subst ~state e in
       let e = state.RS.context e in
       let init = record true state.RS.cells in
       let f = fct ["",(Ident.state,None)] e in
       let e = record false ["init", init; "run", f] in
       let state = { state with cells; context } in
       state, e
  in
  (* Printf.printf "REDUCE\n%s\nTO\n%s\n\n" (to_string expr) (to_string (RS.context state e)); *)
  state, e

let reduce e =
  let subst = [] in
  let state = RS.empty in
  let state, e = reduce ~subst ~state e in
  RS.context state e

(** Run state. *)
module Run = struct
  (* We should only use value expressions. *)
  type value = t
  
  type t = (string, value) Hashtbl.t

  let empty () = Hashtbl.create 100

  let get env x = Hashtbl.find env x
  (* let get env x = let ans = get env x in Printf.printf "get %s is %s\n%!" x (to_string ans); ans *)

  let set env x v = Hashtbl.replace env x v
  (* let set env x v = Printf.printf "set %s to %s\n%!" x (to_string v); set env x v *)

  exception Error of string

  let to_error t e =
    let s = Printf.sprintf "got %s but a %s is expected" (to_string e) t in
    raise (Error s)

  let to_bool e =
    match e.desc with
    | Value (Bool n) -> n
    | _ -> to_error "bool" e

  let to_int e =
    match e.desc with
    | Value (Int n) -> n
    | _ -> to_error "int" e

  let to_float e =
    match e.desc with
    | Value (Float n) -> n
    | _ -> to_error "float" e

  let to_string e =
    match e.desc with
    | Value (String s) -> s
    | _ -> to_error "string" e

  let to_array e =
    match e.desc with
    | Array a -> a
    | _ -> to_error "array" e
end

let is_unit e =
  match e.desc with
  | Value Unit -> true
  | _ -> false

let rec run env e =
  let run = run env in
  (* Printf.printf "running:\n%s\n\n" (to_string e); *)
  match e.desc with
  | Seq (e1, e2) ->
     let v = run e1 in
     assert (is_unit v);
     run e2
  | Let l ->
     Run.set env l.var (run l.def);
     run l.body
  | App ({ desc = External ext }, a) ->
     let a = List.map (fun (l,v) -> assert (l = ""); run v) a in
     let a = Array.of_list a in
     ext.ext_run a
  | While (c,e') ->
     let c = Run.to_bool (run c) in
     if c then
       let e = seq e' e in
       run e
     else
       unit ()
  | For (i,a,b,e) ->
     let a = run a in
     let b = run b in
     for k = Run.to_int a to Run.to_int b do
       let e = letin i (value (Int k)) e in
       let ans = run e in
       assert (is_unit ans) 
     done;
     unit ()
  | Ident x -> Run.get env x
  | Value _ -> e
  | Record _ -> e

let run e = ignore (run (Run.empty ()) e)

(* This wil be filled later on. *)
let parse_file_ctx_fun = ref ((fun _ -> failwith "Parse file function should have been filled") : string -> t -> t)

let parse_file_ctx f = !parse_file_ctx_fun f
