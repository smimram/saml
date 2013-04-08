(** Interpreter. *)

open Stdlib
open Backend

let default_value t = V.default ~bot:true t

(** Operations on state for interpreter. *)
module State = struct
  type state =
    {
      state_vars : V.t array;
      (** Variables. *)
      state_refs : V.t array;
      (** References. *)
      state_proc_vars : (string * V.t array) list;
      (** Local variables for procedures. *)
      state_args : V.t array;
      (** Arguments (for functions). *)
      mutable state_return : V.t;
      (** Returned value for functions calls. *)
    }

  let to_string state =
    (* let mem = String.concat_map ", " V.to_string (Array.to_list state.state_mem) in *)
    (* Printf.sprintf "%s [%s]" (V.to_string state.state_out) mem *)
    "TODO: State.to_string"

  let create prog =
    let alloc vars = Array.map (fun t -> default_value t) vars in
    {
      state_vars = alloc prog.vars;
      state_refs = [||]; (* TODO *)
      state_proc_vars = List.map (fun (l,p) -> l, alloc p.proc_vars) prog.procs;
      state_args = [||];
      state_return = V.Z;
    }

  let set state x v =
    state.state_refs.(x) <- v

  let get state x =
    state.state_refs.(x)

  let get_arg state n =
    state.state_args.(n)

  let get_return state =
    state.state_return
end

let rec eval_expr prog state e =
  (* Printf.printf "SAML.eval_expr: %s\n" (string_of_expr e); *)
  match e with
  | Val v -> v
  | Var v -> State.get state v
  | Arg n -> State.get_arg state n
  | Field (e,i) ->
    let e = eval_expr prog state e in
    let e = V.get_record e in
    e.(i)
  | Cell (e,i) ->
    let e = eval_expr prog state e in
    let i = eval_expr prog state i in
    let i = V.get_int i in
    (V.get_record e).(i)
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
        let p_vars = List.assoc s state.State.state_proc_vars in
        let p_state = { state with State.state_vars = p_vars; state_args = a } in
        eval prog p_state p.proc_cmds;
        State.get_return state
    )
  | If(b,t,e) ->
    let b = eval_expr prog state b in
    if V.get_bool b then eval prog state t else eval prog state e;
    V.unit
  | Return x ->
    let e = eval_expr prog state e in
    state.State.state_return <- e;
    V.unit

and eval prog state cmds =
  List.iter (fun e -> let v = eval_expr prog state e in assert (v = V.U)) cmds

let emit prog =
  let state = State.create prog in
  eval prog state prog.cmds
