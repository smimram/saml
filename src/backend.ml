(** We support various backend: interpreter, C, OCaml. *)

open Stdlib

module Type = struct
  type t =
  | Int
  | Float
  | Bool
  | Unit
  | String
  | Record of t array
  | Array of t
  | Ptr of t

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
    | Ptr t -> Printf.sprintf "*%s" (to_string t)
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
  let rec default ?(bot=true) t =
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

(** An external function along with its implementations in various backends. *)
type extern =
  {
    ext_name : string;
    ext_saml : V.t array -> V.t;
    ext_ocaml : unit -> string;
    ext_c : string array -> string;
  }

(** Operators. Non-prefixed operators operate on floats. *)
type op =
| Botop
(** This value is used as a stub and should never occur. *)
| Add | Sub | Mul | Div
| Pi | Sin | Cos | Exp
| Le | Lt | Eq
| Print of T.t
| External of extern
| Get | Set
(** [Get] and [Set] operate either on a [Ref] or a [Field] or a [Cell]. *)
| Alloc of T.t
(** Allocate a value. If an argument is given, it should be an integer and an
    array is then allocated otherwise a value is allocated. *)
| Realloc of T.t
(** Reallocate a value. *)
| Free
(** Free an allocated value. *)
| Call of string
(** Call an internal procedure. *)

type expr =
| Val of V.t
| Var of var (** A local variable. *)
| Arg of int (** The n-th argument of a function. *)
| Op of op * expr array
| If of expr * cmds * cmds
| For of var * expr * expr * cmds
| While of expr * cmds
| Field of expr * int (** Field of a record. *)
| Cell of expr * expr (** Cell of an array. *)
| Return of expr (** Return a value. *)
(** An equation of the form x = e. *)
and cmd = expr
(** A list of equations. *)
and cmds = cmd list

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
let string_of_arg n = Printf.sprintf "arg%d" n

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
  | Set -> "set"
  | Get -> "get"
  | Print _ -> "print"
  | External ext -> Printf.sprintf "'%s'" ext.ext_name
  | Alloc t  -> Printf.sprintf "alloc[%s]" (T.to_string t)
  | Realloc t  -> Printf.sprintf "realloc[%s]" (T.to_string t)
  | Free -> "free"
  | Call s -> Printf.sprintf "+%s" s
  | Botop -> "⊥"

let rec string_of_expr ?(tab=0) e =
  let string_of_expr ?(tab=tab) = string_of_expr ~tab in
  let string_of_cmds ?(tab=tab) = string_of_cmds ~tab in
  let expr_cmds cmds =
    match cmds with
    | [] -> "{}"
    | [e] -> string_of_expr e
    | l ->
      let s = string_of_cmds ~tab:(tab+1) cmds in
      let stab = String.spaces (2*tab) in
      Printf.sprintf "{\n%s\n%s}" s stab
  in
  match e with
  | Val v -> V.to_string v
  | Var v -> string_of_var v
  | Arg n -> string_of_arg n
  | Field (x,i) -> Printf.sprintf "%s.%d" (string_of_expr x) i
  | Cell (x,i) -> Printf.sprintf "%s[%s]" (string_of_expr x) (string_of_expr i)
  | Op (Set, [|x;e|]) ->
    Printf.sprintf "%s := %s" (string_of_expr x) (string_of_expr e)
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
    let t = expr_cmds t in
    if e = [] then
      Printf.sprintf "if %s then %s" b t
    else
      let e = expr_cmds e in
      Printf.sprintf "if %s then %s else %s" b t e
  | For(i,a,b,ee) ->
    let ee = expr_cmds ee in
    Printf.sprintf "for %s = %s to %s do %s" (string_of_var i) (string_of_expr a) (string_of_expr b) ee
  | While(b,ee) ->
    let ee = expr_cmds ee in
    Printf.sprintf "while %s do %s" (string_of_expr b) ee
  | Return e -> Printf.sprintf "return %s" (string_of_expr e)

and string_of_cmds ?(tab=0) cmds =
  let stab = String.spaces (2*tab) in
  let cmds = List.map (fun e -> stab ^ string_of_expr ~tab e) cmds in
  String.concat "\n" cmds

module Expr = struct
  let to_string = string_of_expr

  let unit = Val V.U

  let ident x = Var x

  let get x =
    Op(Get, [|x|])

  let set x e =
    Op(Set, [|x;e|])

  let return e =
    Return e

  let record r =
    Val (V.R r)

  let alloc ?n t =
    let a =
      match n with
      | None -> [||]
      | Some n -> [|n|]
    in
    Op(Alloc t, a)

  let field e l =
    Field(e,l)
end
module E = Expr

(** A procedure. *)
type proc =
  {
    proc_args : T.t list;
    (** Arguments. *)
    proc_ret : T.t;
    (** Return type. *)
    proc_vars : T.t array;
    (** Local variables. *)
    proc_cmds : cmds;
    (** Code. *)
  }

(** A program. *)
type prog =
  {
    procs : (string * proc) list;
    (** Global procedures. *)
    vars : T.t array;
    (** Local variables. *)
    cmds : cmds;
    (** Equations of the program. *)
  }

(** Create an empty program. *)
let create () =
  {
    procs = [];
    vars = [||];
    cmds = [];
  }

(** Allocate a variable of given type. *)
let alloc prog t =
  try
    (* Trye to reuse unit variables. *)
    if t = T.Unit then
      prog, Array.index t prog.vars
    else
      raise Not_found
  with
  | Not_found ->
    let v = Array.length prog.vars in
    let prog = { prog with vars = Array.append prog.vars [|t|] } in
    prog, v

(** Add a command. *)
let cmd prog e =
  { prog with cmds = prog.cmds@[e] }

let eq prog x e =
  cmd prog (E.set x e)

(** String representation of a program. *)
let to_string p =
  let ans = ref "" in
  let print s = ans := !ans ^ s in
  let vars = Array.mapi (fun i t -> Printf.sprintf "%s:%s" (string_of_var i) (T.to_string t)) p.vars in
  let vars = String.concat ", " (Array.to_list vars) in
  print (Printf.sprintf "variables:\n  %s\n\n" vars);
  (
    if p.procs <> [] then
      let procs =
        String.concat_map "\n\n"
          (fun (name,p) ->
            let tret = p.proc_ret in
            let tret = T.to_string tret in
            let args = List.map T.to_string p.proc_args in
            let args = String.concat ", " args in
            let eqs = if p.proc_cmds = [] then "" else string_of_cmds ~tab:2 p.proc_cmds ^ "\n" in
            Printf.sprintf "  %s %s(%s) {\n%s  }" tret name args eqs
          ) p.procs
      in
      print (Printf.sprintf "procedures:\n%s\n\n" procs)
  );
  let eqs = string_of_cmds ~tab:1 p.cmds in
  print (Printf.sprintf "cmds:\n%s\n\n" eqs);
  !ans

(** Rename procedures of the program. *)
let map_proc_names prog f =
  let procs = List.map (fun (l,p) -> f l, p) prog.procs in
  { prog with procs }

(*
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
    | Field (x,_) -> incr fv x
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
      | LField (x,_) -> incr fv x
      | LCell (x,_) -> incr fv x
    in
    List.fold_left (fun fv (x,e) -> aux fv x) fv eqs

  let bound prog =
    let bound = create prog in
    bound

  let iter fv f =
    Array.iteri f fv
end
*)

(*
exception Substitution

let rec subst_expr ((x',e',fve') as s) e =
  (* Printf.printf "B.subst_expr: %s\n%!" (string_of_expr e); *)
  match e with
  | Var x -> if x = x' then e' else e
  | Field(x,i) -> assert (x <> x'); Field (x, i)
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
*)

(** Optimizations on the code. *)
module Opt = struct
  (** Simple algebraic simplification of expressions. *)
  let simpl p =
    let rec simpl_expr = function
      | Op(op,a) ->
        let a = Array.map simpl_expr a in
        (
          match op,a with
          | Pi,[||] -> Val (V.F pi)
          | Add,[|Val (V.F x); Val (V.F y)|] -> Val (V.F (x +. y))
          | Sub,[|Val (V.F x); Val (V.F y)|] -> Val (V.F (x -. y))
          | Mul,[|Val (V.F x); Val (V.F y)|] -> Val (V.F (x *. y))
          | Div,[|Val (V.F x); Val (V.F y)|] -> Val (V.F (x /. y))
          | Add,[|x; Val (V.F 0.)|] -> x
          | Mul,[|x; Val (V.F 1.)|] -> x
          | Mul,[|x; Val (V.F 0.)|] -> Val (V.F 0.)
          | Mul,[|Val (V.F 1.); x|] -> x
          | Eq,[|Val (V.F x); Val (V.F y)|] -> Val (V.B (x=y))
          | _ -> Op(op,a)
        )
      | If (b,t,e) ->
        let b = simpl_expr b in
        let t = simpl_cmds t in
        let e = simpl_cmds e in
        (
          match b with
          | Val (V.B true) when List.length t = 1 -> List.hd t
          | Val (V.B false) when List.length e = 1 -> List.hd e
          | _ -> If (b,t,e)
        )
      | e -> e

    and simpl_cmds cmds =
      List.map simpl_expr cmds
    in
    { p with cmds = simpl_cmds p.cmds; }

(*
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
*)

(* TODO *)
(* Inline events. *)
(* Compute constant variables (so that we can let instead of := when emitting OCaml). *)
(* Move constant assignments from loop to init. *)
(* Explode records. *)
(* Merge common subexpressions. *)
end

(** Split the last return of a list of equations. *)
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

(** {3 Procedures} *)

(** Helper functions to create programs. *)
module Builder = struct
  type t =
    {
      ident : (string * var) list;
      (** Declared variables. *)
      prog : prog;
      (** Stacks are used to temporarily emit instructions into a buffer instead of
          loop, for emitting if for instance. *)
      stack : cmds list;
    }

  (** Create a program with output of given type and initial value. *)
  let create () =
    {
      ident = [];
      prog = create ();
      stack = [];
    }

  let push b =
    { b with stack = []::b.stack }

  let pop b =
    { b with stack = List.tl b.stack }, List.hd b.stack

  let alloc_anon b t =
    let prog, v = alloc b.prog t in
    { b with prog }, v

  let alloc b x t =
    (* In theory, we could have masking but in practice we rename all the
       variables, so it's safer this way for now. *)
    if List.exists (fun (y,_) -> x = y) b.ident then
      failwith (Printf.sprintf "Backend: trying to reallocate %s." x);
    let prog, v = alloc b.prog t in
    { b with
      prog;
      ident = (x,v)::b.ident }

  let procs b procs =
    let prog = b.prog in
    let prog = { prog with procs = prog.procs@procs } in
    { b with prog }

  let var b x =
    try
      Var (List.assoc x b.ident)
    with
    | Not_found ->
      failwith (Printf.sprintf "Internal error: variable %s not found in backend builder." x)

  (** Perform a command. *)
  let cmd b e =
    match b.stack with
    | cmds::stack ->
      let cmds = cmds@[e] in
      let stack = cmds::stack in
      { b with stack }
    | [] ->
      let prog = cmd b.prog e in
      { b with prog }

  let eq b x e =
    cmd b (E.set x e)

  let return b e =
    cmd b (Return e)

  (** Produce the resulting program. *)
  let prog b =
    let prog = b.prog in
    (* Optimize the program. *)
    let prog =
      if !Config.Compiler.optimize then
        let prog = Opt.simpl prog in
        (* let prog = Opt.dead_code prog in *)
        (* let prog = Opt.inline prog in *)
        (* let prog = Opt.simpl prog in *)
        (* let prog = compact prog in *)
        prog
      else
        prog
    in
    prog
end
