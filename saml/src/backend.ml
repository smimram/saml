(** We support various backend: interpreter, C, OCaml. *)

open Stdlib

module Type = struct
  type t =
  | Int
  | Float
  | Bool
  | Unit
  | String
  | Ptr of t (** A pointer. *)
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
