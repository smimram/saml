(** Internal representation of the language and operations to manipulate it
    (typechecking, reduction, etc.). *)

open Common
open Extralib

module T = Type

(** An expression. *)
type t =
  {
    desc : desc; (** The expression. *)
    pos : pos; (** Position in source file. *)
    mutable t : T.t; (** Type. *)
  }
(** Contents of an expression. *)
and desc =
  | Bool of bool
  | Int of int
  | Float of float
  | String of string
  | Var of string (** A variable. *)
  | Fun of pattern * t (** A function. *)
  | Let of pattern * t * t (** A variable declaration. *)
  | App of t * t
  | Seq of t * t
  | Record of bool * (string * t) list (** A record, the boolean indicates whether it is recursive (= a module) or not. *)
  | If of t * t * t
and pattern =
  | PVar of string
  | PRecord of (string * t option) list
type expr = t

(** Create an expression. *)
let make ?(pos=dummy_pos) ?t e =
  let t =
    match t with
    | Some t -> t
    | None -> T.evar ()
  in
  {
    desc = e;
    pos;
    t
  }

let var ?pos s =
  make ?pos (Var s)

let bool ?pos b =
  make ?pos (Bool b)

let float ?pos x =
  make ?pos (Float x)

let fct ?pos args e =
  make ?pos (Fun (args, e))

let app ?pos f x =
  make ?pos (App (f, x))

let seq ?pos e1 e2 =
  make ?pos (Seq (e1, e2))

let letin ?pos pat def body =
  make ?pos (Let (pat, def, body))

let record ?pos r l =
  make ?pos (Record (r, l))

(** String representation of an expression. *)
let rec to_string ~tab p e =
  let pa p s = if p then Printf.sprintf "(%s)" s else s in
  let tabs ?(tab=tab) () = String.make (2*tab) ' ' in
  let tabss () = tabs ~tab:(tab+1) () in
  match e.desc with
  | Var x -> x
  | Bool b -> string_of_bool b
  | Int n -> string_of_int n
  | Float f -> string_of_float f
  | String s -> Printf.sprintf "%S" s
  | Fun (pat, e) ->
     let pat = string_of_pattern ~tab pat in 
     let e = to_string ~tab:(tab+1) false e in
     pa p (Printf.sprintf "fun %s ->%s%s" pat (if String.contains e '\n' then ("\n"^(tabs ~tab:(tab+1) ())) else " ") e)
  | App (e, a) ->
     let e = to_string ~tab true e in
     let a = to_string ~tab:(tab+1) true a in
     pa p (Printf.sprintf "%s %s" e a)
  | Seq (e1, e2) ->
     let e1 = to_string ~tab false e1 in
     let e2 = to_string ~tab false e2 in
     pa p (Printf.sprintf "%s\n%s%s" e1 (tabs ()) e2)
  | Let (pat, def, body) ->
     let pat = string_of_pattern ~tab pat in
     let def = to_string ~tab:(tab+1) false def in
     let def =
       if String.contains def '\n' then Printf.sprintf "\n%s%s" (tabss ()) def
       else Printf.sprintf " %s " def
     in
     let body = to_string ~tab false body in
     pa p (Printf.sprintf "%s =%s\n%s%s" pat def (tabs ()) body)
  | If (c, e1, e2) ->
     let c = to_string ~tab false c in
     let e1 = to_string ~tab:(tab+1) false e1 in
     let e2 = to_string ~tab:(tab+1) false e2 in
     pa p (Printf.sprintf "if %s then\n%s%s\n%selse\n%s%s\n%send" c (tabss()) e1 (tabs()) (tabss()) e2 (tabs()))
  | Record (r,l) ->
     let l = List.map (fun (x,v) -> Printf.sprintf "%s%s = %s" (tabss()) x (to_string ~tab:(tab+1) false v)) l in
     let l = String.concat "\n" l in
     if r then Printf.sprintf "module\n%s\n%send" l (tabs())
     else Printf.sprintf "{\n%s\n%s}" l (tabs())
and string_of_pattern ~tab = function
  | PVar x -> x
  | PRecord l ->
     let l =
       List.map
         (fun (x,v) ->
           let v =
             match v with
             | Some v -> "="^to_string ~tab:(tab+1) false v
             | None -> ""
           in
           x^v) l
     in
     let l = String.concat ", " l in
     Printf.sprintf "(%s)" l

let to_string e = to_string ~tab:0 false e

let rec free_vars e =
  (* Printf.printf "free_vars: %s\n%!" (to_string e); *)
  let u fv1 fv2 = fv1@fv2 in
  let fv = free_vars in
  match e.desc with
  | Var x -> [x]
  | _ -> assert false

(** {2 Type inference} *)

(** Typing error. *)
exception Typing of pos * string

let type_error e s =
  Printf.ksprintf (fun s -> raise (Typing (e.pos, s))) s

(** Check the type of an expression. *)
let rec check env e =
  (* Printf.printf "infer_type:\n%s\n\n\n%!" (to_string e); *)
  (* Printf.printf "env: %s\n\n" (String.concat_map " , " (fun (x,(_,t)) -> x ^ ":" ^ T.to_string t) env.T.Env.t); *)
  let (<:) e1 e2 = assert (T.( <: ) env e1 e2) in
  let (>:) e2 e1 = assert (T.( <: ) env e2 e1) in
  let check_pattern env pat t =
    (* let env = T.Env.bind env l.var (T.generalize (T.Env.level env) td) in *)
    failwith "TODO"
  in
  match e.desc with
  | Bool _ -> e.t >: T.bool ()
  | Int _ -> e.t >: T.int ()
  | Float _ -> e.t >: T.float ()
  | String _ -> e.t >: T.string ()
  | Var x ->
     let t = try T.Env.typ env x with Not_found -> type_error e "Unbound variable %s." x in
     T.instantiate t
  | Seq (e1, e2) ->
     check env e1;
     e1.t <: T.unit ();
     check env e2;
     e.t >: e2.t
  | Let (pat,def,body) ->
     check (T.Env.enter env) def;
     let env = check_pattern env pat def.t in
     check env body;
     e.t >: body.t
  | Fun (x,v) ->
     let a = T.uvar level in
     let env = T.Env.bind env x a in
     check env v;
     e.t >: T.arr a v.t
  | App (f, v) ->
     let b = T.uvar level in
     check env f;
     check env v;
     f.t <: T.arr v.t b;
     e.t >: b
  | If (c,e1,e2) ->
     check env c;
     c <: T.bool ();
     check env e1;
     check env e2;
     ensure c (infer_type env c) (T.bool ());
     let t = var env in
     ensure e1 (infer_type env e1) t;
     ensure e2 (infer_type env e2) t;
     t
  | Record (_,l) ->
     let l = List.map (fun (x,e) -> x, infer_type env e) l in
     T.record l

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
  | Record (m,l) -> (not m) && List.for_all (fun (x,e) -> inlinable e) l
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
      | While (c,e) ->
         let c = substs ss c in
         let e = substs ss e in
         While (c,e)
      | For (i,a,b,e) ->
         let a = substs ss a in
         let b = substs ss b in
         let e = substs ss e in
         For (i,a,b,e)
      | If (c,e1,e2) ->
         let c = substs ss c in
         let e1 = substs ss e1 in
         let e2 = substs ss e2 in
         If (c,e1,e2)
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
         (* We assume that dt will never occur in a substituted variable (it is
         not inlinable) *)
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
         (* TODO: think harder about variable capture in this case... State can
         be substituted because AddressOf is generated by references... *)
         (* let ss = List.remove_all_assocs [Ident.state] ss in *)
         let e = substs ss e in
         Monadic (RefFun e)
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
       let e = substs subst e in
       (* We cannot reduce here because references might escape then *)
       (* let state, e = reduce_block ~subst ~state ~allow_refs:true e in *)
       state, fct a e
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
                 (* Printf.printf "app: %s\n\n%!" (to_string expr); *)
                 if List.for_all (fun (l,(x,o)) -> o <> None) a then
                   (* All remaining arguments are optional *)
                   List.fold_left (fun e (l,(x,o)) -> letin x (Option.get o) e) e a
                 else
                   (* Partial application *)
                   (* fct a e *)
                   assert false
            in
            let e = aux a e args in
            (* Printf.printf "reduce app:\n%s\n\n%!" (to_string e); *)
            reduce ~state e
         | External ext ->
            let args = List.map (fun (l,e) -> assert (l = ""); e) args in
            let args = Array.of_list args in
            state, ext.ext_reduce args
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
    | If (c,e1,e2) ->
       let state, c = reduce ~subst ~state c in
       begin
         match c.desc with
         | Value (Bool b) -> reduce ~subst ~state (if b then e1 else e2)
         | _ ->
            let state, e1 = reduce_block ~subst ~state e1 in
            let state, e2 = reduce_block ~subst ~state e2 in
            state, make (If(c,e1,e2))
       end
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
    (*
    | Record (m,l) ->
       let state, l =
         List.fold_map
           (fun state (x,e) ->
             let state, e = reduce ~subst ~state e in
             state, (x,e))
           state l
       in
       state, make (Record (m,l))
     *)
    | Record (m,l) ->
       (* We have to letin the members because otherwise, if some of the are not
       inlinable, they prevent the whole record from being inlinable. *)
       let declared = ref false in
       let ctx = ref id in
       let state, l =
         List.fold_map
           (fun state (x,e) ->
             let state, e = reduce ~subst ~state e in
             (* Printf.printf "inlinable: %s\n%!" (to_string e); *)
             if inlinable e then
               state, (x,e)
             else
               let state, y = RS.var state in
               let ctx' =
                 let ctx = !ctx in
                 fun e' -> ctx (letin y e e')
               in
               ctx := ctx';
               declared := true;
               state, (x,ident y)
           )
           state l
       in
       let e = make (Record (m,l)) in
       (* Ensure that the declarations get reduced. *)
       if !declared then reduce ~subst ~state (!ctx e)
       else state, e
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
       let state, e = reduce ~subst ~state e in
       let state, x = RS.cell state in
       (* assert (free_vars e = []); *)
       (* Printf.printf "declare ref to\n%s\n\n%!" (to_string (RS.context state e)); *)
       let state = RS.add_cell state x e in
       let e = field (ident (Ident.state)) x in
       (* The AddressOf is used to ensure that the value will get inlined. *)
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
       reduce ~subst ~state e
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

  let is_unit e =
  match e.desc with
  | Value Unit -> true
  | _ -> false

  let is_float e =
    match e.desc with
    | Value Float _ -> true
    | _ -> false

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

  let to_record e =
    match e.desc with
    | Record (_,r) -> r
    | _ -> to_error "record" e
end

let rec run env e =
  let run = run env in
  (* Printf.printf "running:\n%s\n\n" (to_string e); *)
  match e.desc with
  | Seq (e1, e2) ->
     let v = run e1 in
     assert (Run.is_unit v);
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
       assert (Run.is_unit ans) 
     done;
     unit ()
  | If (c,e1,e2) ->
     let c = run c in
     let c = Run.to_bool c in
     run (if c then e1 else e2)
  | Ident x -> Run.get env x
  | Value _ -> e
  | Record _ -> e
  | Field (r, x) ->
     let r = Run.to_record (run r) in
     List.assoc x r
  | ReplaceField (r, x, e) ->
     let r = run r in
     begin
       match r.desc with
       | Record (m,l) ->
          let l = List.remove_assoc x l in
          let l = (x,e)::l in
          make (Record (m,l))
       | _ -> assert false
     end
  | SetField ({ desc = Ident r }, x, e) ->
     let e = run e in
     let rd = Run.get env r in
     let e = run (make (ReplaceField (rd, x, e))) in
     Run.set env r e;
     unit ()
  | Fun _ -> failwith "Cannot run a function."

let run e = ignore (run (Run.empty ()) e)

(* This wil be filled later on. *)
let parse_file_ctx_fun = ref ((fun _ -> failwith "Parse file function should have been filled") : string -> t -> t)
 
let parse_file_ctx f = !parse_file_ctx_fun f
