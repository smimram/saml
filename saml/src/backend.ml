(** We support various backend: interpreter, C, OCaml. *)

open Stdlib

(** A backend. *)
type backend =
| C
| OCaml
| LLVM

module Type = struct
  type t =
  | Int
  | Float
  | Bool
  | Unit
  | String
  | Ptr of t
  | Record of t array
  | Array of t

  let rec to_string = function
    | Int -> "int"
    | Float -> "float"
    | Bool -> "bool"
    | Unit -> "unit"
    | String -> "string"
    | Ptr t -> Printf.sprintf "*%s" (to_string t)
    | Record t ->
      let t = Array.to_list t in
      let t = String.concat_map ", " to_string t in
      Printf.sprintf "{ %s }" t
    | Array t -> Printf.sprintf "%s array" (to_string t)

  let is_ptr = function
    | Ptr _ -> true
    | _ -> false

  let rec unptr = function
    | Ptr t -> unptr t
    | t -> t
end

module T = Type

(** Values used by the internal interpreter. *)
module Value = struct
  type t =
  | F of float
  | I of int
  | B of bool
  | R of t array
  | S of string
  | U (** Unit *)
  | Z (** Bottom *)

  let rec to_string = function
    | U -> "unit"
    | S s -> s
    | B b -> Printf.sprintf "%B" b
    | I n -> Printf.sprintf "%d" n
    | F x -> Printf.sprintf "%F" x
    | R r ->
      let r = Array.to_list r in
      let r = String.concat_map ", " to_string r in
      Printf.sprintf "{ %s }" r
    | Z -> "⊥"

  (** Default value for a given type. The bot argument ensures that values are
      initialized to bot so that usages of uninitialized values are detected. *)
  let rec default ?(bot=false) t =
    let default = default ~bot in
    let bot v = if bot then Z else v in
    match t with
    | T.Float -> bot (F 0.)
    | T.Int -> bot (I 0)
    | T.Unit -> bot (U)
    | T.String -> bot (S "")
    | T.Bool -> bot (B false)
    | T.Record r -> R (Array.map default r)
    | T.Array _ -> bot (R [||])
    | t -> failwith (T.to_string t)

  let unit = U

  let bool b = B b

  let int n = I n

  let float x = F x

  let string s = S s

  let array n t =
    R (Array.init n (fun _ -> default t))

  let get_float = function
    | F x -> x
    | e -> failwith (Printf.sprintf "Backend expected a float but got %s." (to_string e))

  let get_int = function
    | I n -> n
    | e -> failwith (Printf.sprintf "Backend expected an int but got %s." (to_string e))

  let get_bool = function
    | B b -> b
    | _ -> assert false

  let get_string = function
    | S s -> s
    | _ -> assert false

  let get_record = function
    | R r -> r
    | e -> failwith (Printf.sprintf "Backend expected a record but got %s." (to_string e))

  let get_array = get_record
end
module V = Value

(** A variable. *)
type var = int

(** An external function along with its implementations in various languages. *)
type extern =
  {
    ext_name : string;
    ext_saml : V.t array -> V.t;
    ext_ocaml : unit -> string;
    ext_c : string array -> string;
  }

(** Operators. Non-prefixed operators operate on floats. *)
type op =
| Botop (** This value is used as a stub and should never occur. *)
| Add | Sub | Mul | Div
| Pi | Sin | Cos | Exp
| Le | Lt | Eq
| Print of T.t
| External of extern
| Alloc of T.t
(** Allocate a value. If an argument is given, it should be an integer and an
    array is then allocated otherwise a value is allocated. *)
| Realloc of T.t
(** Reallocate a value. *)
| Free
| Call of string (** Call an internal procedure. *)

(** Variable pointing to a record. *)
type rvar =
| RVar of var
| RState

type expr =
| Unit
| Bool of bool
| Int of int
| Float of float
| String of string
| Var of var
| Op of op * expr array
| If of expr * eqs * eqs
| For of var * expr * expr * eqs
| Field of rvar * int (** Field of a record. *)
| Cell of var * expr (** Cell of an array. *)
| Return of var (** Return a value. *)
| Arg of int
(** The n-th argument. In programs with state, the 0-th argument refers the
    first argument which is not the state (i.e. the second argument). *)
(** An equation of the form x = e. *)
and eq = loc * expr
(** A list of equations. *)
and eqs = eq list
(** A memory location (where things can be written). *)
and loc =
| LVar of var (** A variable. *)
| LField of rvar * int (** A field of a record. *)
| LCell of var * expr (** A cell of an array. *)

(** Unit value. *)
let unit = Unit

(** Create an external operator with given various implementations. *)
let extern ?saml ?ocaml ?c name =
  let saml = maybe (fun _ -> failwith ("TODO: saml implementation for " ^ name)) saml in
  let c = maybe (fun _ -> failwith ("TODO: C implementation for " ^ name)) c in
  let ocaml =
    match ocaml with
    | Some ocaml -> (fun () -> ocaml)
    | None -> (fun () -> failwith ("TODO: OCaml implementation for " ^ name))
  in
  External {
    ext_name = name;
    ext_saml = saml;
    ext_ocaml = ocaml;
    ext_c = c;
  }

let string_of_var n = Printf.sprintf "x%d" n
let string_of_rvar = function
  | RVar v -> string_of_var v
  | RState -> "state"
let string_of_arg n = Printf.sprintf "arg[%d]" n

(* TODO: many of them can go external (we only need those with partial
   application simplifications *)
let string_of_op = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Pi -> "π"
  | Sin -> "sin"
  | Cos -> "cos"
  | Le -> "≤"
  | Lt -> "<"
  | Eq -> "="
  | Exp -> "exp"
  | Print _ -> "print"
  | External ext -> Printf.sprintf "'%s'" ext.ext_name
  | Alloc t  -> Printf.sprintf "alloc[%s]" (T.to_string t)
  | Realloc t  -> Printf.sprintf "realloc[%s]" (T.to_string t)
  | Free -> "free"
  | Call s -> Printf.sprintf "+%s" s
  | Botop -> "⊥"

let rec string_of_expr ?(tab=0) e =
  let string_of_expr ?(tab=tab) = string_of_expr ~tab in
  let string_of_eqs ?(tab=tab) = string_of_eqs ~tab in
  match e with
  | Unit -> "⊤"
  | Bool b -> Printf.sprintf "%B" b
  | Int n -> Printf.sprintf "%d" n
  | Float f -> Printf.sprintf "%F" f
  | String s -> Printf.sprintf "\"%s\"" s
  | Var v -> string_of_var v
  | Arg n -> string_of_arg n
  | Field (x,i) -> Printf.sprintf "%s.%d" (string_of_rvar x) i
  | Cell (x,i) -> Printf.sprintf "%s[%s]" (string_of_var x) (string_of_expr i)
  | Op (o, a) ->
    if Array.length a = 0 then
      string_of_op o
    else
      let a = Array.to_list a in
      let a = List.map string_of_expr a in
      let a = String.concat ", " a in
      Printf.sprintf "%s(%s)" (string_of_op o) a
  | If(b,t,e) ->
    let b = string_of_expr b in
    (* let soeqs eqs = *)
    (* let s = List.map string_of_eq eqs in *)
    (* "{ " ^ String.concat "; " s ^ " }" *)
    (* in *)
    let soeqs eqs =
      (* if List.length eqs = 1 then *)
        (* let s = string_of_eqs ~tab:0 eqs in *)
        (* Printf.sprintf "{ %s }" s *)
      (* else *)
        let s = string_of_eqs ~tab:(tab+1) eqs in
        let stab = String.spaces (2*tab) in
        Printf.sprintf "{\n%s\n%s}" s stab
    in
    let t = soeqs t in
    if e = [] then
      Printf.sprintf "if %s then %s" b t
    else
      let e = soeqs e in
      Printf.sprintf "if %s then %s else %s" b t e
  | For(i,b,e,f) ->
    let soeqs eqs = String.concat_map "; " (fun eq -> string_of_eq eq) eqs in
    Printf.sprintf "for %s = %s to %s { %s }" (string_of_var i) (string_of_expr b) (string_of_expr e) (soeqs f)
  | Return v -> Printf.sprintf "return %s" (string_of_var v)

and string_of_eq ?(tab=0) (x,e) =
  Printf.sprintf "%s = %s" (string_of_loc x) (string_of_expr ~tab e)

and string_of_eqs ?(tab=0) eqs =
  let stab = String.spaces (2*tab) in
  let eqs = List.map (fun eq -> stab ^ string_of_eq ~tab eq) eqs in
  String.concat "\n" eqs

and string_of_loc = function
  | LVar v -> string_of_var v
  | LField (v,i) -> Printf.sprintf "%s.%d" (string_of_rvar v) i
  | LCell (v,i) -> Printf.sprintf "%s[%s]" (string_of_var v) (string_of_expr i)

(** A procedure. *)
type proc =
  {
    proc_vars : T.t array;
    (** Type of the variables of the procedure. *)
    proc_state : T.t option;
    (** Whether procedure takes the state as first argument (in which case we
        give the type of the state). *)
    proc_args : T.t list;
    (** Arguments. *)
    proc_eqs : eqs;
    (** Code. *)
    proc_ret : T.t;
    (** Return value. *)
  }

(** A program. *)
type prog =
  {
    procs : (string * proc) list; (** Global procedures. *)
    vars : T.t array; (** Type of variables. *)
    free_vars : (string * var) list; (** Allocated free variables. *)
    state : T.t option; (** Type of the sate. *)
    output : T.t; (** Type of the output. *)
    init : eqs; (** Initialization of variables. *)
    loop : eqs; (** Main program loop. *)
  }

let create t =
  {
    procs = [];
    vars = [||];
    free_vars = [];
    output = t;
    init = [];
    loop = [];
    state = None;
  }

type field =
| FField of int
| FCell of expr

let loc x field =
  match field with
  | Some (FField n) -> LField (RVar x,n)
  | Some (FCell e) -> LCell (x,e)
  | None -> LVar x

let free_var prog x = List.assoc x prog.free_vars

let alloc prog ?free t =
  let v = Array.length prog.vars in
  let prog = { prog with vars = Array.append prog.vars [|t|] } in
  let prog =
    match free with
    | Some x -> { prog with free_vars = (x,v)::prog.free_vars }
    | None -> prog
  in
  prog, v

let init prog x e =
  { prog with init = prog.init@[x,e] }
let prog_init = init

let eq prog x e =
  { prog with loop = prog.loop@[x,e] }

let init_free prog x ?field e =
  let x = List.assoc x prog.free_vars in
  init prog (loc x field) e

(** Type of the state of a program. *)
let state_t prog = get_some prog.state

(** Type of a loc *)
let rec typ prog x =
  (* Printf.printf "typ: %s\n%!" (string_of_loc x); *)
  match x with
  | LVar x -> prog.vars.(x)
  | LField (RVar x, n) ->
    (
      match T.unptr (typ prog (LVar x)) with
      | T.Record r -> r.(n)
      | _ -> assert false
    )
  | LField (RState, n) ->
    let t = T.unptr (state_t prog) in
    (
      match t with
      | T.Record r -> r.(n)
      | _ -> assert false
    )
  | LCell (x, _) ->
    (
      match typ prog (LVar x) with
      | T.Array t -> t
      | _ -> assert false
    )

let typ_rvar prog = function
  | RVar x -> typ prog (LVar x)
  | RState -> state_t prog

let to_string p =
  let ans = ref "" in
  let print s = ans := !ans ^ s in
  let vars = Array.mapi (fun i t -> Printf.sprintf "%s:%s" (string_of_var i) (T.to_string t)) p.vars in
  let vars = Array.to_list vars in
  let vars = String.concat ", " vars in
  print (Printf.sprintf "variables:\n  %s\n\n" vars);
  let fv = String.concat_map ", " (fun (x,v) -> Printf.sprintf "%s=x%d" x v) p.free_vars in
  print (Printf.sprintf "free variables:\n  %s\n\n" fv);
  (
    if p.procs <> [] then
      let procs =
        String.concat_map "\n\n"
          (fun (name,p) ->
            let tret = p.proc_ret in
            let tret = T.to_string tret in
            let args = List.map T.to_string p.proc_args in
            let args =
              match p.proc_state with
              | Some state ->
                let a = Printf.sprintf "%s state" (T.to_string state) in
                a::args
              | None ->
                args
            in
            let args = String.concat ", " args in
            let eqs = if p.proc_eqs = [] then "" else string_of_eqs ~tab:2 p.proc_eqs ^ "\n" in
            Printf.sprintf "  %s %s(%s) {\n%s  }" tret name args eqs
          ) p.procs
      in
      print (Printf.sprintf "procedures:\n%s\n\n" procs)
  );
  print (Printf.sprintf "output:\n  %s\n\n" (T.to_string p.output));
  let init = string_of_eqs ~tab:1 p.init in
  print (Printf.sprintf "init:\n%s\n\n" init);
  let loop = string_of_eqs ~tab:1 p.loop in
  print (Printf.sprintf "loop:\n%s\n\n" loop);
  !ans

(** Rename procedures of the program. *)
let map_proc_names prog f =
  let procs = List.map (fun (l,p) -> f l, p) prog.procs in
  { prog with procs }

(** Helper structure to compute free variables. *)
module FV = struct
  let create p =
    Array.create (Array.length p.vars) 0

  let get fv v = fv.(v)

  let has fv v = fv.(v) <> 0

  let to_string fv =
    let fv = Array.to_list fv in
    let fv = List.map string_of_int fv in
    String.concat "" fv

  let set fv v n =
    let fv = Array.copy fv in
    fv.(v) <- n;
    fv

  let incr fv v =
    set fv v (get fv v + 1)

  let hide fv v =
    set fv v 0

  let union fv1 fv2 =
    Array.map2 (+) fv1 fv2

  let max fv1 fv2 =
    Array.map2 max fv1 fv2

  let rec expr ?(masking=true) fv e =
    let expr = expr ~masking in
    (* let eq = eq ~masking in *)
    let eqs = eqs ~masking in
    match e with
    | Op (o,a) -> Array.fold_left expr fv a
    | If (b,t,e) -> union (expr fv b) (max (eqs fv t) (eqs fv e))
    | Var v -> incr fv v
    | Field (RVar x,_) -> incr fv x
    | Field (RState,_) -> fv
    | Cell (x,i) -> incr (expr fv i) x
    | Bool _ | Int _ | Float _ | String _ -> fv

  and eq ?(masking=true) fv (x,e) =
    let expr = expr ~masking in
    let fv =
      match x with
      | LVar x -> if masking then hide fv x else incr fv x
      | LField _ -> fv
      | LCell (x,i) -> if masking then expr fv i else incr (expr fv i) x
    in
    expr fv e

  and eqs ?(masking=true) fv eqs =
    List.fold_right (fun xe fv -> eq ~masking fv xe) eqs fv

  let written fv eqs =
    let aux fv = function
      | LVar x -> incr fv x
      | LField (RVar x,_) -> incr fv x
      | LField (RState,_) -> fv
      | LCell (x,_) -> incr fv x
    in
    List.fold_left (fun fv (x,e) -> aux fv x) fv eqs

  let bound prog =
    let bound = create prog in
    let bound = List.fold_left incr bound (List.map snd prog.free_vars) in
    bound

  let iter fv f =
    Array.iteri f fv
end


exception Substitution

let rec subst_expr ((x',e',fve') as s) e =
  (* Printf.printf "B.subst_expr: %s\n%!" (string_of_expr e); *)
  match e with
  | Var x -> if x = x' then e' else e
  | Field(RVar x,i) -> assert (x <> x'); Field (RVar x, i)
  | Field(RState,i) -> Field (RState, i)
  | Cell(x,i) -> assert (x <> x'); Cell (x, subst_expr s i)
  | Op(op,a) -> Op(op, Array.map (subst_expr s) a)
  | If(b,t,e) -> If(subst_expr s b, subst_eqs s t, subst_eqs s e)
  | Float _  | Int _ | String _ | Bool _ as e -> e

and subst_eqs ((x',e',fve') as s) = function
  | (x,e)::eqs ->
    let e = subst_expr s e in
    (
      match x with
      | LVar v ->
        if v = x' then
          (* Masking. *)
          (x,e)::eqs
        else if FV.has fve' v then
          (* This weired case is to avoid renaming. For instance if we want to
             perform [f(z)/x] on y=2; z=3; t=x the substitution cannot be performed
             (without renaming the variable z) and the result will be y=2; x=f(z);
             z=3; t=x. *)
          (x,e)::(LVar x',e')::eqs
        else
          (x,e)::(subst_eqs s eqs)
      (* TODO: LField *)
      | LCell (v,i) ->
        let i = subst_expr s i in
        let x = LCell(v,i) in
        if v = x' then
          assert false
        else if FV.has fve' v then
          (x,e)::(LVar x',e')::eqs
        else
          (x,e)::(subst_eqs s eqs)
    )
  | [] -> []

let subst_eqs prog (x,e) = subst_eqs (x,e,FV.expr (FV.create prog) e)

(** Optimizations on the code. *)
module Opt = struct
  (** Simple algebraic simplification of expressions. *)
  let simpl p =
    let rec simpl_expr = function
      | Op(op,a) ->
        let a = Array.map simpl_expr a in
        (
          match op,a with
          | Pi,[||] -> Float pi
          | Add,[|Float x; Float y|] -> Float (x +. y)
          | Sub,[|Float x; Float y|] -> Float (x -. y)
          | Mul,[|Float x; Float y|] -> Float (x *. y)
          | Div,[|Float x; Float y|] -> Float (x /. y)
          | Add,[|x; Float 0.|] -> x
          | Mul,[|x; Float 1.|] -> x
          | Mul,[|x; Float 0.|] -> Float 0.
          | Mul,[|Float 1.; x|] -> x
          | Eq,[|Float x;Float y|] -> Bool (x=y)
          | _ -> Op(op,a)
        )
      | If (b,t,e) ->
        let b = simpl_expr b in
        let t = simpl_eqs t in
        let e = simpl_eqs e in
        If (b,t,e)
      | e -> e

    and simpl_eqs eqs =
      List.map (fun (l,e) -> l, simpl_expr e) eqs
    in
    { p with
      init = simpl_eqs p.init;
      loop = simpl_eqs p.loop }

  (** Inline linearly used variables and eliminate dead code. *)
  (* TODO: inline the end first! *)
  let inline prog =
    let bound = FV.create prog in
    let bound = FV.eqs bound prog.loop in
    let bound = FV.union (FV.bound prog) bound in
    (* Printf.printf "bound: %s\n%!" (FV.to_string bound); *)
    let rec aux = function
      | (LVar x,Var y)::eqs when x = y -> aux eqs
      | ((LVar x,e) as eq)::eqs ->
        let fv = FV.eqs (FV.create prog) eqs in
        if FV.has bound x || typ prog (LVar x) = T.Unit then
          eq::(aux eqs)
        else
          if FV.get fv x = 0 then aux eqs
          else if FV.get fv x = 1 then aux (subst_eqs prog (x,e) eqs)
          else eq::(aux eqs)
      | ((LField _,_) as eq)::eqs ->
        eq::eqs
      | [] -> []
    in
    { prog with init = aux prog.init; loop = aux prog.loop }

  (* let inline prog = fixpoint inline prog *)

  let dead_code prog =
    let bound = FV.create prog in
    let bound = FV.eqs bound prog.loop in
    let bound = FV.union (FV.bound prog) bound in
    (* Printf.printf "DC: %s\n%!" (FV.to_string bound); *)
    let rec aux = function
      | (LVar x as l, e)::eqs when FV.get bound x = 0 && FV.get (FV.eqs (FV.create prog) eqs) x = 0 && not (typ prog l = T.Unit) -> aux eqs
      | eq::eqs -> eq::(aux eqs)
      | [] -> []
    in
    { prog with init = aux prog.init; loop = aux prog.loop }

  (* fv for loop could change if we remove unused variables... *)
  let dead_code = fixpoint dead_code

  (** Don't allocate unused variables. *)
  let compact prog =
    let fv_eq fv (x,e) =
      let x =
        match x with
        | LVar x -> x
        | LField (RVar x,_) -> x
      in
      FV.union (FV.incr fv x) (FV.expr ~masking:false (FV.create prog) e)
    in
    let fv_eqs = List.fold_left fv_eq in
    let fv = FV.bound prog in
    let fv = fv_eqs fv prog.init in
    let fv = fv_eqs fv prog.loop in
    (* Printf.printf "compact fv: %s\n" (FV.to_string fv); *)
    let used = Array.init (Array.length prog.vars) (fun i -> FV.get fv i <> 0) in
    let n = ref (-1) in
    let s =
      Array.map (fun u -> if u then (incr n; !n) else -1) used
    in
    let n = !n + 1 in
    let vars = Array.init n (fun i -> typ prog (LVar (Array.index i s))) in
    (* ( *)
    (* let vars = Array.mapi (fun i v -> if v = -1 then "" else Printf.sprintf "%s -> %s" (string_of_var i) (string_of_var v)) s in *)
    (* let vars = Array.to_list vars in *)
    (* let vars = String.concat ", " vars in *)
    (* Printf.printf "compact vars: %s\n%!" vars *)
    (* ); *)
    let rec subst_expr e =
      (* We cannot use regular substitution because we don't want masking here. *)
      match e with
      | Var v -> Var s.(v)
      (* | Field(x,i) -> Field (t, subst_expr e, i) *)
      (* | Cell(e,i) -> Cell (subst_expr e, subst_expr i) *)
      | Op(op,a) -> Op(op, Array.map subst_expr a)
      | If(b,t,e) ->
        let b = subst_expr b in
        let t = subst_eqs t in
        let e = subst_eqs e in
        If(b,t,e)
      | Bool _ | Float _ | Int _ | String _ as e -> e
    and subst_eq (x,e) =
      let x =
        match x with
        | LVar x -> LVar s.(x)
      (* | LField (x,i) -> LField (s.(x),i) *)
      in
      x, subst_expr e
    and subst_eqs eqs = List.map subst_eq eqs in
    assert (prog.procs = []);
    {
      vars;
      procs = prog.procs;
      free_vars = List.map (fun (l,v) -> l, s.(v)) prog.free_vars;
      output = prog.output;
      init = subst_eqs prog.init;
      loop = subst_eqs prog.loop;
      state = prog.state;
    }

(* TODO *)
(* Inline events. *)
(* Compute constant variables (so that we can let instead of := when emitting OCaml). *)
(* Move constant assignments from loop to init. *)
(* Explode records. *)
(* Merge common subexpressions. *)
end

(** {3 Operations on state.} *)

(* TODO: we should maybe define eqs = eq list * expr and remove Return... *)
let split_ret eqs =
  let rec aux h = function
    | [_, Return _] as eq -> h, eq
    | [eq] -> eq::h, []
    | eq::eqs -> aux (eq::h) eqs
    | [] -> assert false
  in
  let eqs, eq = aux [] eqs in
  List.rev eqs, eq

let proc prog ?(state=false) args t eqs =
  let state = if state then Some (state_t prog) else None in
  {
    proc_vars = prog.vars;
    proc_state = state;
    proc_args = args;
    proc_eqs = eqs;
    proc_ret = t;
  }

(* TODO: alloc and run should be handled as other procs. *)
let pack_state prog =
  let t = T.Record prog.vars in
  let n = Array.length prog.vars in
  let load = List.init n (fun i -> LVar i, Field(RState, i)) in
  let store = List.init n (fun i -> LField(RState, i), Var i) in
  let ls eqs =
    let eqs, ret = split_ret eqs in
    load@eqs@store@ret
  in
  let loop = ls prog.loop in
  let prog, init =
    let prog, x = alloc prog (T.Ptr t) in
    let prog, ret = alloc prog T.Unit in
    let written = FV.written (FV.create prog) prog.init in
    let store = List.may_init n (fun i -> if FV.has written i then Some (LField(RVar x,i), Var i) else None) in
    prog, [(LVar x), (Op(Alloc t,[||]))]@prog.init@store@[(LVar ret), Return x]
  in
  let proc_reset =
    {
      proc_vars = prog.vars;
      proc_state = Some t;
      proc_args = [];
      proc_eqs = prog.init;
      proc_ret = T.Unit;
    }
  in
  let procs = ("reset", proc_reset)::prog.procs in
  let procs =
    List.map
      (fun (l,p) ->
        l, { p with
          proc_eqs = ls p.proc_eqs;
          (* We add a lot of vars but it should be correct. *)
          proc_vars = prog.vars;
          proc_state = Some t }
      ) procs
  in
  let proc_unalloc =
    {
      proc_vars = prog.vars;
      proc_state = Some t;
      proc_args = [];
      proc_eqs = load; (* TODO *)
      proc_ret = T.Unit;
    }
  in
  let procs = ("unalloc", proc_unalloc)::procs in
  { prog with init; loop; state = Some t; procs }

(** Procedures. *)

(** Names for standard procedures. *)
module Proc_name = struct
  let alloc = "alloc"
  let unalloc = "unalloc"
  let init = "init"
  let loop = "loop"
end

let proc_alloc prog =
  let t = T.Ptr (state_t prog) in
  proc prog ~state:false [] t prog.init

let proc_run prog =
  proc prog ~state:true [] prog.output prog.loop

let procs prog =
  prog.procs

let map_fv prog f =
  List.map (fun (x,v) -> f x v) prog.free_vars

(** Helper functions to create programs. *)
module Builder = struct
  type t =
    {
      var_pos : (string * var) list;
      prog : prog;
      (** Stacks are used to temporarily emit instructions into a buffer instead of
          loop, for emitting if for instance. *)
      stack : eqs list;
    }

  (** Create a program with output of given type and initial value. *)
  let create t =
    {
      var_pos = [];
      prog = create t;
      stack = [];
    }

  let push b =
    { b with stack = []::b.stack }

  let pop b =
    { b with stack = List.tl b.stack }, List.hd b.stack

  let alloc_anon b t =
    let prog, v = alloc b.prog t in
    { b with prog }, v

  let alloc b ?(free=false) x t =
    (* Printf.printf "alloc: %s\n%!" x; *)
    (* In theory, we could have masking but in practice we rename all the
       variables, so it's safer this way for now. *)
    if List.exists (fun (y,_) -> x = y) b.var_pos then
      failwith (Printf.sprintf "Backend: trying to reallocate %s." x);
    let free = if free then Some x else None in
    let prog, v = alloc b.prog ?free t in
    { b with
      prog;
      var_pos = (x,v)::b.var_pos }

  let procs b procs =
    let prog = b.prog in
    let prog = { prog with procs = prog.procs@procs } in
    { b with prog }

  let var b ?(free=false) x =
    try
      List.assoc x (if free then b.prog.free_vars else b.var_pos)
    with
    | Not_found ->
      failwith (Printf.sprintf "Internal error: variable %s not found in backend builder." x)

  let var_create b x t =
    try
      b, var b x
    with
    | _ ->
      let b = alloc b ~free:true x t in
      b, free_var b.prog x

  let loc b x field =
    if x = "state" then
      let field = get_some field in
      let field =
        match field with
        | FField n -> n
        | _ -> assert false
      in
      LField (RState, field)
    else
      loc (var b x) field

  (* let init b x ?field e = *)
    (* let x = loc b x field in *)
    (* let prog = init b.prog x e in *)
    (* { b with prog } *)

  (* let init_alloc b x t e = *)
    (* let b = alloc b x t in *)
    (* init b x e *)

  let eq_anon b ?(init=false) x e =
    if init then
      let prog = prog_init b.prog x e in
      { b with prog }
    else
      match b.stack with
      | eqs::stack ->
        let eqs = eqs@[x,e] in
        let stack = eqs::stack in
        { b with stack }
      | [] ->
        let prog = eq b.prog x e in
        { b with prog }

  let eq b ?init x ?field e =
    let x = loc b x field in
    eq_anon b ?init x e

  let eq_alloc b ?init x t e =
    let b = alloc b x t in
    eq b ?init x e

  let eq_alloc_anon b ?init t e =
    let b, x = alloc_anon b t in
    eq_anon b ?init (LVar x) e, x

  (** Perform a command. *)
  let cmd ?init b e =
    let b, x = alloc_anon b T.Unit in
    eq_anon ?init b (LVar x) e

  let return b t e =
    let b, x = alloc_anon b t in
    let b = eq_anon b (LVar x) e in
    cmd b (Return x)

  let output b t e =
    return b t e

  (** Add a procedure. *)
  let proc b name args ret e =
    let prog = b.prog in
    let p = proc prog args ret e in
    let prog = { prog with procs = prog.procs@[name,p] } in
    { b with prog }

  (** Produce the resulting program. *)
  let prog ?(state=false) b =
    let prog = b.prog in
    (* Optimize the program. *)
    let prog =
      if !Config.Compiler.optimize then
        let prog = Opt.simpl prog in
        let prog = Opt.dead_code prog in
        let prog = Opt.inline prog in
        let prog = Opt.simpl prog in
        (* let prog = compact prog in *)
        prog
      else
        prog
    in
    (* Emit the state. *)
    let prog = if state then pack_state prog else prog in
    prog
end

(** {2 Backends} *)

module SAML = struct
  let default_value t = V.default ~bot:true t

  module State = struct
    type state =
      {
        (** Main memory. *)
        state_mem : V.t array;
        (** Arguments (for functions). *)
        state_args : V.t array;
        (** Output (for functions). *)
        mutable state_out : V.t;
      }

    let to_string state =
      let mem = String.concat_map ", " V.to_string (Array.to_list state.state_mem) in
      Printf.sprintf "%s [%s]" (V.to_string state.state_out) mem

    let create prog =
      {
        state_mem = Array.map default_value prog.vars;
        state_out = V.U;
        state_args = [||];
      }

    let of_t ?(args=[||]) t =
      let t =
        match t with
        | T.Record t -> t
        | _ -> assert false
      in
      {
        state_mem = Array.map default_value t;
        state_out = V.U;
        state_args = args;
      }

    let of_record ?(args=[||]) r =
      let r = V.get_record r in
      {
        state_mem = r;
        state_out = V.U;
        state_args = args;
      }

    let to_record state =
      V.R state.state_mem

    let set state x v =
      let mem = state.state_mem in
      (* let mem = *)
        (* We have to do this because in init the allocated state is outside the
           state. *)
        (* if x >= Array.length mem then *)
        (* ( *)
        (* Printf.printf "Interpreter: extending state for %s...\n%!" (string_of_var x); *)
        (* Array.init (x+1) (fun i -> if i < Array.length mem then mem.(i) else V.Z) *)
        (* ) *)
        (* else *)
        (* mem *)
      (* in *)
      (* state.state_mem <- mem; *)
      mem.(x) <- v

    let get state x =
      state.state_mem.(x)

    let get_out state =
      state.state_out

    let get_arg state n =
      state.state_args.(n)

    let set_out state v =
      state.state_out <- v
  end

  let rec eval_expr prog state e =
    (* Printf.printf "SAML.eval_expr: %s\n" (string_of_expr e); *)
    match e with
    | Var v -> State.get state v
    | Arg n -> State.get_arg state n
    | Field (v,i) ->
      let v =
        match v with
        | RVar v -> State.get state v
        | RState -> State.to_record state
      in
      (V.get_record v).(i)
    | Cell (v,i) ->
      let v = State.get state v in
      let i = eval_expr prog state i in
      let i = V.get_int i in
      (V.get_record v).(i)
    | Op(op,a) ->
      let a = Array.map (eval_expr prog state) a in
      let gf n = V.get_float (a.(n)) in
      let f = V.float in
      let b = V.bool in
      (
        match op with
        | Add -> f ((gf 0) +. (gf 1))
        | Sub -> f ((gf 0) -. (gf 1))
        | Mul -> f ((gf 0) *. (gf 1))
        | Div -> f ((gf 0) /. (gf 1))
        | Sin -> f (sin (gf 0))
        | Le -> b ((gf 0) <= (gf 1))
        | Eq -> b (a.(0) = a.(1))
        | Exp -> f (exp (gf 0))
        | Pi -> f pi
        | Print T.String ->
          let s = V.get_string a.(0) in
          (* Convert \n into newlines, etc. *)
          let s = Scanf.sscanf (Printf.sprintf "\"%s\"" s) "%S" id in
          Printf.printf "%s%!" s;
          V.unit
        | Print T.Int ->
          let n = V.get_int a.(0) in
          Printf.printf "%d%!" n;
          V.unit
        | Print T.Float ->
          let x = V.get_float a.(0)in
          Printf.printf "%f%!" x;
          V.unit
        | External ext -> ext.ext_saml a
        | Alloc t ->
          if Array.length a = 0 then
            default_value t
          else
            V.array (V.get_int a.(0)) t
        | Realloc t ->
          if Array.length a = 1 then
            (* TODO: we should keep the existing value *)
            (* default_value t *)
            assert false
          else
            let old = V.get_array a.(0) in
            let a = V.array (V.get_int a.(1)) t in
            let arr = V.get_array a in
            for i = 0 to min (Array.length old) (Array.length arr) - 1 do
              arr.(i) <- old.(i)
            done;
            a
        | Call s ->
          (* Printf.printf "call %s\n%!" s; *)
          let p = List.assoc s prog.procs in
          (* Printf.printf "len: %d\n%!" (Array.length a); *)
          let args =
            let n = Array.length a - 1 in
            if n < 0 then [||] else Array.init (Array.length a-1) (fun i -> a.(i+1))
          in
          let tmp_state =
            match p.proc_state with
            | Some _ ->
              let state = State.of_record ~args a.(0) in
              (* Printf.printf "call: %s\n  B: %s\n" s (State.to_string state); *)
              eval prog state p.proc_eqs;
              (* Printf.printf "  A: %s\n" (State.to_string state); *)
              state
            | None ->
              let state = State.of_t ~args (T.Record p.proc_vars) in
              eval prog state p.proc_eqs;
              state
          in
          State.get_out tmp_state
      )
    | If(b,t,e) ->
      let b = eval_expr prog state b in
      if V.get_bool b then eval prog state t else eval prog state e;
      V.unit
    | For(i,b,e,f) ->
      let b = eval_expr prog state b in
      let b = V.get_int b in
      let e = eval_expr prog state e in
      let e = V.get_int e in
      for k = b to e do
        State.set state i (V.int k);
        eval prog state f
      done;
      V.unit
    | Float x -> V.float x
    | Int n -> V.int n
    | Bool b -> V.bool b
    | String s -> V.string s
    | Unit -> V.unit
    | Return x ->
      let x = State.get state x in
      State.set_out state x;
      V.unit

  and eval_eq prog state (x,e) =
    let e = eval_expr prog state e in
    match x with
    | LVar x ->
      (* Printf.printf "eval_eq var: %s\n%!" (string_of_var x); *)
      State.set state x e
    | LField (RVar x,i) ->
      (* Printf.printf "eval_eq field: %s\n%!" (string_of_var x); *)
      let r = V.get_record (State.get state x) in
      r.(i) <- e
    | LField (RState,i) ->
      State.set state i e
    | LCell (x,i) ->
      (* Printf.printf "eval_eq field: %s\n%!" (string_of_var x); *)
      let r = V.get_record (State.get state x) in
      let i = V.get_int (eval_expr prog state i) in
      r.(i) <- e

  and eval prog state eqs =
    List.iter (eval_eq prog state) eqs

  let emit prog =
    let state = State.create prog in
    eval prog state prog.init;
    (* let store = free_var prog "state" in *)
    (* let store = state.(store) in *)
    fun () ->
      (* Printf.printf "store: %s\n%!" (string_of_val store); *)
      let ans = State.get_out state in
      eval prog state prog.loop;
      ans
end

module OCaml = struct
  let emit_op = function
    | Add -> "( +. )"
    | Sub -> "( -. )"
    | Mul -> "( *. )"
    | Div -> "( /. )"
    | Sin -> "sin"
    | Pi -> "(4. *. atan 1.)"
    | Le -> "( <= )"
    | Lt -> "( < )"
    | Eq -> "( = )"
    | Exp -> "exp"
    | Print t ->
      (
        match t with
        | T.Float -> "Printf.printf \"%F\\n%!\""
        | T.Int -> "Printf.printf \"%d\n%!\""
        | T.String -> "Printf.printf \"%s%!\""
      )
    | External ext -> ext.ext_ocaml ()
    | op -> failwith (Printf.sprintf "TODO: OCaml.emit_op for %s." (string_of_op op))

  let rec emit_type = function
    | T.Int -> "int"
    | T.Float -> "float"
    | T.Unit -> "unit"

  let rec emit_expr prog e =
    (* Printf.printf "B.OCaml.emit_expr: %s\n%!" (string_of_expr e); *)
    match e with
    | Int n -> Printf.sprintf "(%d)" n
    | Float f -> Printf.sprintf "(%F)" f
    | Bool b -> Printf.sprintf "%b" b
    | String s -> Printf.sprintf "\"%s\"" s
    | Var n -> Printf.sprintf "(!%s)" (string_of_var n)
    | Op (op, args) ->
      let args = Array.to_list args in
      let args = List.map (emit_expr prog) args in
      let args = String.concat " " args in
      Printf.sprintf "(%s %s)" (emit_op op) args
    | If (b,t,e) ->
      let b = emit_expr prog b in
      let emit_eqs prog eqs = "(" ^ String.concat "; " (List.map (emit_eq prog) eqs) ^ ")" in
      let t = emit_eqs prog t in
      let e =
        match e with
        | [_,Unit] -> ""
        | _ -> " else " ^ emit_eqs prog e
      in
      Printf.sprintf "(if %s then %s%s)" b t e
    | Return x -> emit_expr prog (Var x)

  and emit_eq prog (x,e) =
    (* if static then Printf.sprintf "let %s = %s in" (string_of_var x) (emit_expr prog e) else *)
    if typ prog x = T.Unit then
      Printf.sprintf "%s" (emit_expr prog e)
    else
      Printf.sprintf "%s := %s" (string_of_loc x) (emit_expr prog e)

  and emit_eqs prog eqs =
    String.concat ";\n" (List.map (emit_eq prog) eqs)

      (*
  (** Get names for fields of a record of a given type. *)
  let record =
    let n = ref (-1) in
    let r = ref [] in
    fun tr ->
      try
        List.assoc tr !r
      with
      | Not_found ->
        let fields = Array.map (fun
      *)

  let default_value t =
    match t with
    | T.Unit -> "()"
    | T.Int -> "0"
    | T.Bool -> "false"
    | T.Float -> "0."
    (* | T.Record r -> *)

  let emit prog =
    let vars = Array.to_list prog.vars in
    let vars =
      List.may_mapi
        (fun i t ->
          if t = T.Unit then
            None
          else
            Some (Printf.sprintf "let %s = ref %s in" (string_of_var i) (default_value t))
        ) vars
    in
    let vars = String.concat "\n" vars in
    let init = Printf.sprintf "let init () =\n%s\nin" (emit_eqs prog prog.init) in
    let loop =  Printf.sprintf "let loop () =\n%s\nin" (emit_eqs prog prog.loop) in
    Printf.sprintf "let program () =\n\n%s\n\n%s\n\n%s\n\nlet first = ref true in\nfun () -> if !first then (first := false; init ()) else loop()" vars init loop
end

module C =
struct
  type t =
    {
      (** Currently processed program. *)
      prog : prog;
      (** Already defined types. *)
      types : (T.t * string) list;
    }

  let create prog =
    {
      prog;
      types = [];
    }

  let rec emit_type c ?(noderef=false) ?(state=false) ?(full=false) t =
    (* Printf.printf "C.emit_type %B: %s\n%!" state (T.to_string t); *)
    match t with
    | T.Int -> c, "int"
    | T.Float -> c, "double"
    | T.Unit -> c, "void"
    | T.Bool -> c, "int"
    | T.Ptr t ->
      let c, t = emit_type c ~noderef ~state ~full t in
      c, t^"*"
    | T.Record r ->
      if full then
        let c, l = emit_type c ~noderef:true t in
        let c = ref c in
        let ans =
          Array.mapi
            (fun i t ->
              if t = T.Unit then "" else
                let c', t = emit_type !c (T.unptr t) in
                c := c';
                Printf.sprintf "%s %s_%d;" t l i
            ) r
        in
        let ans = Array.to_list ans in
        !c, String.concat " " ans
      else
        let c, typ =
          try
            c, List.assoc t c.types
          with
          | Not_found ->
            (* Printf.printf "didn't find type\n%!"; *)
            let l = if state then "state" else Printf.sprintf "type%d" (List.length c.types) in
            let c = { c with types = (t,l)::c.types } in
            c, l
        in
        c, typ

  let tab n = String.spaces (2*n)

  let rec emit_loc c ~decl ~tabs x =
    match x with
    | LVar x -> c, string_of_var x
    | LField (RVar a,i) ->
      let t = typ c.prog (LVar a) in
      let c, t = emit_type c ~noderef:true (T.unptr t) in
      c, Printf.sprintf "%s->%s_%d" (string_of_var a) t i
    | LField (RState,i) ->
      let t = state_t c.prog in
      let c, t = emit_type c ~noderef:true t in
      c, Printf.sprintf "state->%s_%d" t i
    | LCell (a,i) ->
      let c, i = emit_expr c ~decl ~tabs i in
      c, Printf.sprintf "%s[%s]" (string_of_var a) i

  and emit_expr c ~decl ~tabs e =
    (* Printf.printf "C.emit_expr: %s\n%!" (string_of_expr e); *)
    let emit_expr ?(decl=decl) ?(tabs=tabs) = emit_expr ~decl ~tabs in
    let emit_eqs ?(decl=decl) ?(tabs=tabs) = emit_eqs ~decl ~tabs in
    match e with
    | Int n -> c, Printf.sprintf "%d" n
    | Float f -> c, Printf.sprintf "%f" f
    | Bool b -> c, if b then "1" else "0"
    | Var n -> c, Printf.sprintf "%s" (string_of_var n)
    | Arg n -> c, Printf.sprintf "a%d" n
    | Op (op, args) ->
      let c, args =
        let c = ref c in
        let args = Array.map (fun e -> let c', e = emit_expr !c e in c := c'; e) args in
        !c, args
      in
      (
        (* Printf.printf "C.emit_expr op: %s\n%!" (string_of_op op); *)
        match op with
        | Add -> c, Printf.sprintf "(%s + %s)" args.(0) args.(1)
        | Sub -> c, Printf.sprintf "(%s - %s)" args.(0) args.(1)
        | Mul -> c, Printf.sprintf "(%s * %s)" args.(0) args.(1)
        | Div -> c, Printf.sprintf "(%s / %s)" args.(0) args.(1)
        | Eq -> c, Printf.sprintf "(%s == %s)" args.(0) args.(1)
        | Alloc t ->
          let n = if Array.length args = 0 then "1" else args.(0) in
          let c, tv = emit_type c ~noderef:true t in
          let c, t = emit_type c (T.Ptr t) in
          c, Printf.sprintf "(%s)malloc(%s * sizeof(%s))" t n tv
        | Realloc t ->
          assert (Array.length args = 2);
          let n = if Array.length args = 1 then "1" else args.(1) in
          let c, tv = emit_type c ~noderef:true t in
          let c, t = emit_type c (T.Ptr t) in
          c, Printf.sprintf "(%s)realloc(%s, %s * sizeof(%s))" args.(0) t n tv
        | External ext -> c, ext.ext_c args
      )
    | Return x ->
      c, if typ c.prog (LVar x) = T.Unit then "" else Printf.sprintf "return %s" (string_of_var x)
    | Field (x, i) ->
      let t = typ_rvar c.prog x in
      let x =
        match x with
        | RVar x -> string_of_var x
        | RState -> "state"
      in
      let c, t = emit_type c ~noderef:true (T.unptr t) in
      c, Printf.sprintf "%s->%s_%d" x t i
    | Cell (x, i) ->
      let c, e = emit_expr c (Var x) in
      let c, i = emit_expr c i in
      c, Printf.sprintf "%s[%s]" e i
    | If (b,t,e) ->
      let emit_eqs = emit_eqs ~tabs:(tabs+1) in
      let c, b = emit_expr c b in
      let c, t = emit_eqs c t in
      let c, e = emit_eqs c e in
      let tabs = tab tabs in
      c, Printf.sprintf "if (%s) {\n%s\n%s} else {\n%s\n%s}" b t tabs e tabs

  and emit_eq c ~decl ~tabs (x,expr) =
    let c, e = emit_expr ~decl ~tabs c expr in
    if typ c.prog x = T.Unit then
      (
        match expr with
        | Var _ | Field _ -> (c, decl), ""
        | _ -> (c, decl), Printf.sprintf "%s%s;" (tab tabs) e
      )
    else
      let c, decl, t =
        match x with
        | LVar x ->
          let t = typ c.prog (LVar x) in
          if List.mem x decl then
            c, decl, ""
          else
            let decl = x::decl in
            (* let deref = deref t in *)
            let c, t = emit_type c t in
            c, decl, (t^" ")
        | LCell _
        | LField _ ->
          c, decl, ""
      in
      let c, l = emit_loc c ~decl ~tabs x in
      (c, decl), Printf.sprintf "%s%s%s = %s;" (tab tabs) t l e

  (* TODO: decl should be replaced by FV.written because of if, etc. *)
  and emit_eqs c ?(decl=[]) ?(tabs=0) eqs =
    let (c,decl), eqs = List.fold_map (fun (c,decl) -> emit_eq c ~decl ~tabs) (c,decl) eqs in
    let eqs = List.filter (fun s -> s <> "") eqs in
    c, String.concat "\n" eqs

  let emit_proc c (name,p) =
    let args = p.proc_args in
    let c =
      match p.proc_state with
      | Some t ->
        (* We emit the state first so that we know its name. *)
        let c, _ = emit_type c ~state:true t in
        c
      | None -> c
    in
    let c, args =
      let i = ref (-1) in
      let c = ref c in
      let a =
        List.map
          (fun t ->
            Printf.sprintf "%s a%d"
              (let c', t = emit_type !c t in c := c'; t)
              (incr i; !i)
          ) args
      in
      !c, a
    in
    let c, args =
      match p.proc_state with
      | Some t ->
        (* We emit the state first so that we know its name. *)
        let c, t = emit_type c ~state:true (T.Ptr t) in
        c, (Printf.sprintf "%s state" t)::args
      | None -> c, args
    in
    let args = String.concat ", " args in
    let c, eqs = emit_eqs c ~tabs:1 p.proc_eqs in
    let c, ret = emit_type c p.proc_ret in
    c,
    Printf.sprintf "inline %s %s(%s) {\n%s\n}"
      ret
      name
      args
      eqs

  let emit prog =
    let c = create prog in
    (* TODO: alloc and run should always be handled as usual procs. *)
    let procs = ["run", proc_run prog; "alloc", proc_alloc prog]@prog.procs in
    let c, procs = List.fold_map emit_proc c procs in
    let procs = String.concat "\n\n" procs in
    let c, types =
      let c = ref c in
      let ans =
        String.concat_map "\n\n"
          (fun (t,l) ->
            let c', t = emit_type !c ~full:true t in
            c := c';
            Printf.sprintf "typedef struct { %s } %s;" t l
          ) (!c).types
      in
      !c, ans
    in
    types ^ "\n\n" ^ procs
end

(*
module Llvm = struct
  open Llvm

  type context =
      {
        context : llcontext;
        builder : llbuilder;
        modul : llmodule;
        mutable env : (string * llvalue) list;
      }

  let create () =
    let context = global_context () in
    {
      context = context;
      builder = builder context;
      modul = create_module context "SAML";
      env = [];
    }

  let typ c = function
    | TInt -> i64_type c.context
    | TFloat -> float_type c.context
    | TVoid -> void_type c.context

  let rec emit_expr ?(deref=true) c e =
    match e with
      | Int n -> const_int (typ c TInt) n
      | Float f -> const_float (typ c TFloat) f
      | Ident x ->
        let v = List.assoc x c.env in
        (* TODO: it would be better to emit Loads... *)
        if deref && classify_type (type_of v) = TypeKind.Pointer then
          build_load v "loadtmp" c.builder
        else
          v
      | Op (o, a) ->
        let a =
          if o = Store then
            [|emit_prog ~deref:false c a.(0); emit_prog c a.(1)|]
          else
            Array.map (emit_prog c) a
        in
        (
          match o with
            | FAdd -> build_fadd a.(0) a.(1) "addtmp" c.builder
            | FMul -> build_fmul a.(0) a.(1) "multmp" c.builder
            (* | Alloc (x, t) -> *)
            (* let v = build_alloca (typ c t) "alloctmp" c.builder in *)
            (* c.env <- (x,v)::c.env; *)
            (* v *)
            | Store -> build_store a.(1) a.(0) c.builder
            | Call f ->
              let f =
                match lookup_function f c.modul with
                  | Some f -> f
                  | None -> assert false
              (* raise (Error "unknown function referenced") *)
              in
              let params = params f in
              if Array.length params <> Array.length a then assert false;
              (* raise (Error "incorrect # arguments passed"); *)
              build_call f a "calltmp" c.builder
        )

  and emit_prog ?(deref=true) c p =
    (* Printf.printf "emit_prog: %s\n%!" (to_string p); *)
    match p with
      | [e] ->
        emit_expr ~deref c e
      | e::p ->
        ignore (emit_expr ~deref c e);
        emit_prog ~deref c p
      | [] -> assert false

  let emit_proto c (name,args,ret) =
      let targs = Array.map (fun (_,t) -> typ c t) args in
      let ret = typ c ret in
      let ft = function_type ret targs in
      let f = declare_function name ft c.modul in
      Array.iteri
        (fun i a ->
          let n = fst args.(i) in
          set_value_name n a;
          c.env <- (n,a) :: c.env
        ) (params f);
      f

  let emit_decl c = function
    | Decl (proto, body) ->
      (* Create a new basic block to start insertion into. *)
      let the_function = emit_proto c proto in
      let bb = append_block c.context "entry" the_function in
      position_at_end bb c.builder;
      (
        try
          let ret_val = emit_prog c body in
          (* Finish off the function. *)
          if thd3 proto = TVoid then
            ignore (build_ret_void c.builder)
          else
            ignore (build_ret ret_val c.builder);
          (* Validate the generated code, checking for consistency. *)
          Llvm_analysis.assert_valid_function the_function;
        with e ->
          delete_function the_function;
          raise e
      )
    | External proto ->
      ignore (emit_proto c proto)

  let emit m =
    let c = create () in
    List.iter (emit_decl c) m;
    c.modul

  let with_emit f m =
    let m = emit m in
    let ans = f m in
    dispose_module m;
    ans

  let dump m =
    with_emit dump_module m

  let write m fname =
    with_emit (fun m -> assert (Llvm_bitwriter.write_bitcode_file m fname)) m
end
*)
