open Stdlib

(** A backend. *)
type backend = LLVM | C | OCaml

module Type = struct
  type t = Int | Float | Bool | Unit | String | Record of t array | Array of t

  let rec to_string = function
    | Int -> "int"
    | Float -> "float"
    | Bool -> "bool"
    | Unit -> "unit"
    | String -> "string"
    | Record t ->
      let t = Array.to_list t in
      let t = String.concat_map ", " to_string t in
      Printf.sprintf "{ %s }" t
    | Array t -> Printf.sprintf "%s array" (to_string t)
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
    | _ -> assert false

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
  }

(** Operators. Non-prefixed operators operate on floats. *)
type op =
| Botop (** This value is used as a stub and should never occur. *)
| Add | Sub | Mul | Div
| Pi | Sin | Cos | Exp
| Le | Lt | Eq
| Print of T.t
| External of extern
(** Allocate a value. If an argument is given, it should be an integer and an
    array is then allocated. *)
| Alloc of T.t
| Free
(** Call an internal procedure. *)
| Call of string

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
| Field of expr * int
(** The global state (given as argument of functions). *)
| State
(** Return a value. *)
| Return of var
(** The n-th argument. In programs with state, the 0-th argument refers the
    first argument which is not the state (i.e. the second argument). *)
| Arg of int
and eq = loc * expr
and eqs = eq list
(** A memory location (where things can be written). *)
and loc =
| LVar of var
| LField of var * expr
(** A field of the state. *)
| LState of int

let unit = Unit

let extern ?saml ?ocaml name =
  let saml = maybe (fun _ -> failwith ("TODO: saml implementation for " ^ name)) saml in
  let ocaml =
    match ocaml with
    | Some ocaml -> (fun () -> ocaml)
    | None -> (fun () -> failwith ("TODO: ocaml implementation for " ^ name))
  in
  External {
    ext_name = name;
    ext_saml = saml;
    ext_ocaml = ocaml;
  }

let string_of_var n = Printf.sprintf "x%d" n
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
  | Field (e,i) -> Printf.sprintf "%s[%d]" (string_of_expr e) i
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
  | State -> "state"
  | Return v -> Printf.sprintf "return %s" (string_of_var v)

and string_of_eq ?(tab=0) (x,e) =
  Printf.sprintf "%s = %s" (string_of_loc x) (string_of_expr ~tab e)

and string_of_eqs ?(tab=0) eqs =
  let stab = String.spaces (2*tab) in
  let eqs = List.map (fun eq -> stab ^ string_of_eq ~tab eq) eqs in
  String.concat "\n" eqs

and string_of_loc = function
  | LVar v -> string_of_var v
  | LField (v,i) -> Printf.sprintf "%s[%s]" (string_of_var v) (string_of_expr i)
  | LState i -> Printf.sprintf "state[%d]" i

let loc v field =
  match field with
  | Some i -> LField (v,i)
  | None -> LVar v

(** A procedure. *)
type proc =
  {
    (** Type of the variables of the procedure. *)
    proc_vars : T.t array;
    (** Whether procedure takes the state as first argument (in which case we
        give the type of the state). *)
    proc_state : T.t option;
    (** Arguments. *)
    proc_args : T.t list;
    (** Code. *)
    proc_eqs : eqs;
    (** Return value. *)
    proc_ret : T.t;
  }

type prog =
  {
    (** Global procedures. *)
    procs : (string * proc) list;
    (** Type of variables. *)
    vars : T.t array;
    (** Allocated free variables. *)
    free_vars : (string * var) list;
    (** Type of the sate. *)
    state : T.t option;
    (** Type of the output. *)
    output : T.t;
    (** Initialization of variables. *)
    init : eqs;
    (** Main program loop. *)
    loop : eqs;
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

let typ prog x =
  match x with
  | LVar x -> prog.vars.(x)
  | LField (x,i) -> failwith "TODO"

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

(** Optimizations. *)

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

let simpl p =
  { p with
    init = simpl_eqs p.init;
    loop = simpl_eqs p.loop }

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
    | Field (e,i) -> expr fv e
    | Bool _ | Int _ | Float _ | String _ -> fv

  and eq ?(masking=true) fv (x,e) =
    let expr = expr ~masking in
    let fv =
      if masking then
        match x with
        | LVar x -> hide fv x
        | LField (x,i) -> expr fv i
      else
        match x with
        | LVar x -> incr fv x
        | LField (x,i) -> incr (expr fv i) x
    in
    expr fv e

  and eqs ?(masking=true) fv eqs =
    List.fold_right (fun xe fv -> eq ~masking fv xe) eqs fv

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
  | Field(e,i) -> Field (subst_expr s e, i)
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
      | LField (v,i) ->
        let i = subst_expr s i in
        let x = LField(v,i) in
        if v = x' then
          assert false
        else if FV.has fve' v then
          (x,e)::(LVar x',e')::eqs
        else
          (x,e)::(subst_eqs s eqs)
    )
  | [] -> []

let subst_eqs prog (x,e) = subst_eqs (x,e,FV.expr (FV.create prog) e)

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
      | LField (x,_) -> x
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
    | Field(e,i) -> Field (subst_expr e, i)
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
      | LField (x,i) -> LField (s.(x),i)
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

(** {3 Operations on state.} *)

(* TODO: we should maybe define eqs = eq list * expr and remove Return... *)
let split_ret eqs =
  let rec aux h = function
    | [eq] -> h, eq
    | eq::eqs -> aux (eq::h) eqs
    | [] -> assert false
  in
  let eqs, eq = aux [] eqs in
  List.rev eqs, eq

(** Type of the state of a program. *)
let state_t prog = get_some prog.state

let proc prog ?(state=false) args t eqs =
  let state = if state then Some (state_t prog) else None in
  {
    proc_vars = prog.vars;
    proc_state = state;
    proc_args = args;
    proc_eqs = eqs;
    proc_ret = t;
  }

let pack_state prog =
  let t = T.Record prog.vars in
  let n = Array.length prog.vars in
  let load = List.init n (fun i -> LVar i, Field(State, i)) in
  let store = List.init n (fun i -> LState(i), Var i) in
  let loop =
    let eqs, ret = split_ret prog.loop in
    load@eqs@store@[ret]
  in
  let prog, init =
    let prog, x = alloc prog t in
    let prog, ret = alloc prog T.Unit in
    let store = List.init n (fun i -> LField(x,Int i), Var i) in
    prog, [(LVar x), (Op(Alloc t,[||]))]@prog.init@store@[(LVar ret), Return x]
  in
  let procs =
    List.map
      (fun (l,p) ->
        l, { p with
          proc_eqs = load@p.proc_eqs@store;
          (* We add a lot of vars but it should be correct. *)
          proc_vars = prog.vars;
          proc_state = Some t }
      ) prog.procs
  in
  { prog with init; loop; state = Some t; procs }

(** Procedures. *)

let proc_alloc prog =
  let t = state_t prog in
  proc prog ~state:false [] t prog.init

let proc_run prog =
  proc prog ~state:true [] (T.Unit) prog.loop

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
    (* In theory, we could have masking but in practice we rename all the
       variables, so it's safer this way for now. *)
    (* Printf.printf "alloc: %s\n%!" x; *)
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
      (* TODO: this looks a bit hackish... *)
      let field = get_some field in
      let field =
        match field with
        | Int n -> n
        | _ -> assert false
      in
      LState field
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
        let prog = simpl prog in
        let prog = dead_code prog in
        let prog = inline prog in
        let prog = simpl prog in
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
    | Field (e,i) ->
      let v = eval_expr prog state e in
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
    | State -> State.to_record state
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
    | LField (x,i) ->
      (* Printf.printf "eval_eq field: %s\n%!" (string_of_var x); *)
      let r = V.get_record (State.get state x) in
      let i = V.get_int (eval_expr prog state i) in
      r.(i) <- e
    | LState i -> State.set state i e

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
  let emit_op = function
    | Sin -> "sin"
    | op -> failwith (Printf.sprintf "TODO: C.emit_op for %s." (string_of_op op))

  let rec emit_type = function
    | T.Int -> "int"
    | T.Float -> "double"
    | T.Unit -> "void"

  let rec emit_expr prog = function
    | Int n -> Printf.sprintf "(%d)" n
    | Float f -> Printf.sprintf "(%f)" f
    | Var n -> Printf.sprintf "%s" (string_of_var n)
    | Op (op, args) ->
      let args = Array.map (emit_expr prog) args in
      (
        match op with
        | Add -> Printf.sprintf "(%s + %s)" args.(0) args.(1)
      )
    | If (b,t,e) ->
      let b = emit_expr prog b in
      let emit_eqs prog eqs = "{" ^ String.concat " " (List.map (emit_eq prog) eqs) ^ "}" in
      let t = emit_eqs prog t in
      let e = emit_eqs prog e in
      Printf.sprintf "if (%s) then %s else %s" b t e

  and emit_eq prog (x,e) =
    (* if static then Printf.sprintf "let %s = %s in" (string_of_var x) (emit_expr prog e) else *)
    if typ prog x = T.Unit then
      Printf.sprintf "%s;" (emit_expr prog e)
    else
      Printf.sprintf "%s = %s;" (string_of_loc x) (emit_expr prog e)

  and emit_eqs prog eqs =
    String.concat "\n" (List.map (emit_eq prog) eqs)

  let emit prog =
    let vars = Array.to_list prog.vars in
    let vars =
      List.may_mapi
        (fun i t ->
          let default =
            match t with
            | T.Unit -> "()"
            | T.Int -> "0"
            | T.Bool -> "0"
            | T.Float -> "0."
          in
          if t = T.Unit then
            None
          else
            Some (Printf.sprintf "%s %s = ref %s in" (T.to_string (typ prog (LVar i))) (string_of_var i) default)
        ) vars
    in
    let vars = String.concat "\n" vars in
    let init = emit_eqs prog prog.init in
    let loop = emit_eqs prog prog.loop in
    Printf.sprintf "let program () =\n%s\n%s\nfun () ->\n%s" vars init loop
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
