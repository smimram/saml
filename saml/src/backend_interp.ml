open Stdlib
open Backend

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
