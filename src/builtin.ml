open Stdlib
open Common
open Lang

module B = Backend
module BB = B.Builder


(** Registered externals. *)
let externals = ref []


(** {2 General functions} *)

(** Helpers for constructing types. *)
module T = struct
  include T

  let f_f _ = arrnl [float] float

  let ff_f _ = arrnl [float;float] float

  let bb_b _ = arrnl [bool;bool] bool

  let b_b _ = arrnl [bool] bool

  let aa_b _ = let a = T.fresh_var () in T.arrnl [a;a] bool
end

let may_implem i =
  maybe (fun _ -> raise E.Cannot_reduce) i

let may_backend b =
  maybe (fun _ -> assert false) b

(** Declare an external backend operator. *)
let mop name ?i ?b t =
  assert (i <> None || b <> None);
  let e =
    {
      E.
      ext_name = name;
      ext_t = t;
      ext_backend = may_backend b;
      ext_implem = may_implem i;
    }
  in
  externals := e :: !externals

(** Declare an external backend operator whose implementation is an operator. *)
let op name t ?i b =
  let b _ prog a = prog, B.Op(b,a) in
  mop name ?i ~b t

let get_string e =
  match e.E.desc with
  | E.Cst (E.String s) -> s
  | _ -> raise E.Cannot_reduce


(** {2 Simple operators} *)

(** {3 Arithmetic} *)

let () = op "mul" T.ff_f B.Mul

let () = op "div" T.ff_f B.Div

let () = op "pi" (fun _ -> T.float) B.Pi

let () = op "sin" T.f_f B.Sin

let () = op "cos" T.f_f B.Cos

let () = op "exp" T.f_f B.Exp

let () = op "random" T.f_f (B.extern ~saml:(fun a -> B.V.float (Random.float (B.V.get_float a.(0)))) ~ocaml:"Random.float" "random")

(** {3 Booleans} *)

let () = op "eq" T.aa_b B.Eq

let () = op "and" T.bb_b (B.extern ~saml:(fun a -> B.V.bool ((B.V.get_bool a.(0)) && (B.V.get_bool a.(1)))) ~ocaml:"( && )" "and")

let () = op "or" T.bb_b (B.extern ~saml:(fun a -> B.V.bool ((B.V.get_bool a.(0)) || (B.V.get_bool a.(1)))) ~ocaml:"( || )" "or")

let () = op "not" T.b_b (B.extern ~saml:(fun a -> B.V.bool (not (B.V.get_bool a.(0)))) ~ocaml:"( not )" "not")


(** {2 Meta operators} *)

let () =
  let name = "bot" in
  let t _ = T.arrnl [] (T.fresh_var ()) in
  let i _ = E.bot () in
  mop name ~i t

let () =
  let name = "init" in
  let t _ = T.arrnl [] T.bool in
  let i _ = E.ident E.Ident.init in
  mop name ~i t

(** {2 Records} *)
(*
let () =
  let name = "fst" in
  let t _ =
    let a = T.fresh_var () in
    let b = T.fresh_var () in
    T.arrnl [T.record ~row:false ["",(a,false);"",(b,false)]] a
  in
  let i a =
    let e = List.assoc "" a in
    match e.E.desc with
    | E.Record r -> List.assoc "" r
    | _ -> raise E.Cannot_reduce
  in
  mop name ~i t

let () =
  let name = "snd" in
  let t _ =
    let a = T.fresh_var () in
    let b = T.fresh_var () in
    T.arrnl [T.record ~row:false ["",(a,false);"",(b,false)]] b
  in
  let i a =
    let e = List.assoc "" a in
    match e.E.desc with
    | E.Record r -> List.assoc_nth 1 "" r
    | _ -> raise E.Cannot_reduce
  in
  mop name ~i t
*)

(** {2 Specific implementations} *)

let () =
  let name = "exit" in
  let t _ = T.arrnl [T.int] (T.fresh_var ()) in
  let i args =
    let n = List.assoc "" args in
    let n =
      match n.E.desc with
      | E.Cst (E.Int n) -> n
      | _ -> assert false
    in
    exit n
  in
  mop name t ~i

(** Declare a binary operator on either int or floats. *)
let nn_n name fop iop fml iml c =
  let c arg = Printf.sprintf "(%s %s %s)" arg.(0) c arg.(1) in
  let is_int args =
    let args = List.map snd args in
    let int = List.exists T.is_int args in
    let int = int && List.for_all (fun t -> T.is_int t || T.is_var t) args in
    int
  in
  let t args =
    (* Printf.printf "nn_n: %s\n%!" (String.concat_map ", " T.to_string args); *)
    if is_int args then
      T.arrnl [T.int; T.int] T.int
    else
      T.arrnl [T.float; T.float] T.float
  in
  let i args =
    let x = List.assoc "" args in
    let y = List.assoc_nth 1 "" args in
    match x.E.desc, y.E.desc with
    | E.Cst (E.Int x), E.Cst (E.Int y) -> E.int (iop x y)
    | E.Cst (E.Float x), E.Cst (E.Float y) -> E.float (fop x y)
    | _ -> raise E.Cannot_reduce
  in
  let b t prog args =
    let a, _ = T.split_arr t in
    let a = List.map (fun (l,(t,o)) -> l,t) a in
    let op =
      if is_int a then
        B.extern ~saml:(fun a -> B.V.int (iop (B.V.get_int a.(0)) (B.V.get_int a.(1)))) ~ocaml:iml ~c name
      else
        B.extern ~saml:(fun a -> B.V.float (fop (B.V.get_float a.(0)) (B.V.get_float a.(1)))) ~ocaml:fml ~c name
    in
    prog, B.Op(op, args)
  in
  mop name t ~i ~b

let () = nn_n "add" (+.) (+) "(+.)" "(+)" "+"
let () = nn_n "sub" (-.) (-) "(-.)" "(-)" "-"

(* TODO: share code with nn_n *)
let nn_b name fop iop ocaml c =
  let c arg = Printf.sprintf "(%s %s %s)" arg.(0) c arg.(1) in
  let is_int args =
    let args = List.map snd args in
    let int = List.exists T.is_int args in
    let int = int && List.for_all (fun t -> T.is_int t || T.is_var t) args in
    int
  in
  let t args =
    (* Printf.printf "nn_n: %s\n%!" (String.concat_map ", " T.to_string args); *)
    if is_int args then
      T.arrnl [T.int; T.int] T.bool
    else
      T.arrnl [T.float; T.float] T.bool
  in
  let i args =
    let x = List.assoc "" args in
    let y = List.assoc_nth 1 "" args in
    match x.E.desc, y.E.desc with
    | E.Cst (E.Int x), E.Cst (E.Int y) -> E.bool (iop x y)
    | E.Cst (E.Float x), E.Cst (E.Float y) -> E.bool (fop x y)
    | _ -> raise E.Cannot_reduce
  in
  let b t prog args =
    let a, _ = T.split_arr t in
    let a = List.map (fun (l,(t,o)) -> l,t) a in
    let op =
      if is_int a then
        B.extern ~saml:(fun a -> B.V.bool (iop (B.V.get_int a.(0)) (B.V.get_int a.(1)))) ~ocaml ~c name
      else
        B.extern ~saml:(fun a -> B.V.bool (fop (B.V.get_float a.(0)) (B.V.get_float a.(1)))) ~ocaml ~c name
    in
    prog, B.Op(op, args)
  in
  mop name t ~i ~b

let le = nn_b "le" (<=) (<=) "(<=)" "<="
let lt = nn_b "lt" (<) (<) "(<)" "<"

let () =
  let name = "print" in
  let t _ = (T.arrnl [T.fresh_var ()] T.unit) in
  let i args =
    let s = List.assoc "" args in
    match s.E.desc with
    | E.Cst (E.String s) ->
      let s = Scanf.sscanf (Printf.sprintf "\"%s\"" s) "%S" id in
      Printf.printf "%s%!" s;
      raise E.Cannot_reduce
    | E.Cst (E.Float x) ->
      Printf.printf "%f\n%!" x;
      raise E.Cannot_reduce
    | e ->
      Printf.printf "%s%!" (E.to_string s);
      raise E.Cannot_reduce
  in
  let b t prog args =
    let t, _ = T.split_arr t in
    let t = T.unvar (fst (List.assoc "" t)) in
    prog, B.Op (B.Print (T.emit t),args)
  in
  mop name t ~i ~b

let () =
  let name = "array_play" in
  let channels = 1 in
  let sr = 44100 in
  let writer = ref None in
  let saml a =
    (* Printf.printf "array_play: %s\n%!" (B.V.to_string a.(0)); *)
    let buf = a.(0) in
    let buf = B.V.get_array buf in
    let buf = Array.map B.V.get_float buf in
    let writer =
      match !writer with
      | Some w -> w
      | None ->
        let w = new Samlrun.pulseaudio_writer "SAML" "sound" channels sr in
        (* let w = new Audio.IO.Writer.to_wav_file channels sr "output.wav" in *)
        writer := Some w;
        w
    in
    writer#write [|buf|] 0 (Array.length buf);
    B.V.unit
  in
  let ocaml = "Array.play" in
  let extern = B.extern ~saml ~ocaml name in
  op name (fun _ -> T.arrnl [T.array T.float] T.unit) extern

let () =
  let name = "array_play_stereo" in
  let channels = 2 in
  let sr = 44100 in
  let writer = ref None in
  let saml a =
    (* Printf.printf "array_play: %s\n%!" (B.V.to_string a.(0)); *)
    let bufl = B.V.get_array a.(0) in
    let bufr = B.V.get_array a.(1) in
    let bufl = Array.map B.V.get_float bufl in
    let bufr = Array.map B.V.get_float bufr in
    let writer =
      match !writer with
      | Some w -> w
      | None ->
        let w = new Samlrun.pulseaudio_writer "SAML" "sound" channels sr in
        (* let w = new Audio.IO.Writer.to_wav_file channels sr "output.wav" in *)
        writer := Some w;
        w
    in
    let buf = [|bufl; bufr|] in
    writer#write buf 0 (Array.length buf.(0));
    B.V.unit
  in
  let c a = Printf.sprintf "samlrun_array_play_stereo(%s,%s)" a.(0) a.(1) in
  let ocaml = "Array.play_stereo" in
  let extern = B.extern ~saml ~ocaml ~c name in
  op name (fun _ -> T.arrnl [T.array T.float; T.array T.float] T.unit) extern

(* TODO: reimplement using array_play *)
let play =
  let name = "play" in
  let channels = 1 in
  let sr = 44100 in
  let writer = ref None in
  let saml a =
    let buf = a.(0) in
    let buf = B.V.get_array buf in
    let buf = Array.map B.V.get_float buf in
    let writer =
      match !writer with
      | Some w -> w
      | None ->
        let w = new Samlrun.pulseaudio_writer "SAML" "sound" channels sr in
        (* let w = new Audio.IO.Writer.to_wav_file channels sr "output.wav" in *)
        writer := Some w;
        w
    in
    writer#write [|buf|] 0 (Array.length buf);
    B.V.unit
  in
  let extern = B.extern ~saml name in
  op name (fun _ -> T.arrnl [T.monad (T.fresh_var ()) T.float] T.unit) extern

(* TODO: remove this debug *)
(*
let play_song =
  (* Takes as argument somthing that generates a stream from a freq. *)
  let t _ = T.arrnl [T.arrnl [T.float] T.float] T.unit in
  let b _ = assert false in
  let i ~subst ~state a =
    (* Compile the sound generator. *)
    let osc = List.assoc "" a in
    let _, osc = E.reduce_quote ~subst ~state:(E.reduce_state_empty) osc ["", E.ident "freq"] in
    let state, osc = E.emit ~subst ~state ~free_vars:true osc in
    let dt = 1. /. 44100. in
    let osc = BB.init osc "dt" (B.Float dt) in
    let osc = BB.prog ~state:true osc in
    let state_t = B.state_t osc in
    let prog = BB.create B.T.Unit in
    let prog = BB.proc prog "osc_alloc" (B.proc_alloc osc) in
    (* let prog = BB.proc prog "osc_init" (B.proc_init osc) in *)
    let prog = BB.proc prog "osc_run" (B.proc_run osc) in
    let buflen = 1024 in
    let prog = BB.init_alloc prog "state" state_t (B.Op(B.Call "osc_alloc",[||])) in
    let prog = BB.init_alloc prog "buffer" (B.T.Array B.T.Float) (B.Op(B.Alloc B.T.Float, [|B.Int buflen|])) in
    let prog = BB.alloc prog "i" B.T.Int in
    let state = B.Var (BB.var prog "state") in
    let buffer = B.Var (BB.var prog "buffer") in
    (* let prog = BB.cmd ~init:true prog (B.Op(B.Call "osc_init", [|state|])) in *)
    let i = B.Var (BB.var prog "i") in
    let prog = BB.push prog in
    (* TODO: we shouldn't drop the first sample... *)
    let prog = BB.eq prog "buffer" ~field:i (B.Op(B.Call "osc_run", [|state|])) in
    let prog, f = BB.pop prog in
    let prog = BB.cmd prog (B.For (BB.var prog "i", B.Int 0, B.Int (buflen-1),f)) in
    (* let prog = BB.cmd prog (B.Op(play_buffer_mono,[|buffer|])) in *)
    let prog = BB.output prog B.unit in
    let prog = BB.prog prog in
    file_out "out/output.saml" (B.to_string prog);
    Printf.printf "%s\n%!" (B.to_string prog);
    let prog = B.SAML.emit prog in
    while true do
      ignore (prog ())
    done;
    exit 0
  in
  mop "play_song" t ~i b
*)

(* TODO *)
(* let dssi = *)
  (* let t = T.record [] in *)
  (* let t _ = T.arrnl [t] (T.unit()) in *)
  (* let b _ = B.Unit in *)
  (* mop "dssi" t b *)

(** {2 Arrays} *)

let () =
  let name = "array_create" in
  let t _ =
    let a = T.fresh_var () in
    T.arrnl [T.int; a] (T.array a)
  in
  let b t prog a =
    let _, t = T.split_arr t in
    let t =
      match (T.unvar t).T.desc with
      | T.Array t -> t
      | _ -> assert false
    in
    let t = T.emit t in
    prog, B.Op(B.Alloc t,[|a.(0)|])
  in
  mop name t ~b

let () =
  let name = "array_realloc" in
  let t _ =
    let a = T.fresh_var () in
    T.arrnl [T.array a; T.int] (T.array a)
  in
  let b t prog args =
    let t =
      match (T.unvar t).T.desc with
      | T.Array t -> t
      | _ -> assert false
    in
    let t = T.emit t in
    prog, B.Op(B.Realloc t, args)
  in
  mop name t ~b

let () =
  let name = "array_set" in
  let t _ =
    let a = T.fresh_var () in
    T.arrnl [T.array a; T.int; a] T.unit
  in
  let b t prog a =
    let cmd = B.E.set (B.Cell (a.(0), a.(1))) a.(2) in
    prog, cmd
  in
  mop name t ~b

let () =
  let name = "array_get" in
  let t _ =
    let a = T.fresh_var () in
    T.arrnl [T.array a; T.int] a
  in
  let i arg =
    (* Printf.printf "array_get impl\n%!"; *)
    let array = List.assoc "" arg in
    let n = List.assoc_nth 1 "" arg in
    match array.E.desc, n.E.desc with
    | E.Array a, E.Cst (E.Int n) -> List.nth n a
    | _ -> raise E.Cannot_reduce
  in
  let b t prog a =
    prog, B.Cell(a.(0), a.(1))
  in
  mop name t ~i ~b

let () =
  let name = "array_tail" in
  let t _ =
    let v = T.fresh_var () in
    let a = T.array v in
    T.arrnl [a] a
  in
  let i a =
    let array = List.assoc "" a in
    match array.E.desc with
    | E.Array a ->
      let a = List.tl a in
      E.array ~t:(E.typ array) a
    | _ -> raise E.Cannot_reduce
  in
  mop name t ~i

let () =
  let name = "array_length" in
  let t _ =
    let v = T.fresh_var () in
    let a = T.array v in
    T.arrnl [a] T.int
  in
  let i a =
    let array = List.assoc "" a in
    match array.E.desc with
    | E.Array a -> E.int (List.length a)
    | _ -> raise E.Cannot_reduce
  in
  mop name t ~i

(*
let compile =
  let t args =
    let state = T.state () in
    let t_out, (t_ret, t_aux) =
      try
        let t = List.assoc "" args in
        Printf.printf "compile t: %s\n%!" (T.to_string t);
        if not (T.is_arr t) then raise Not_found;
        let _, t = T.split_arr t in
        let t_out = t in
        t_out,
        match (T.unvar t).T.desc with
        (* In case of a record, we might get unboxed! *)
        (* TODO: be label-ordering-independent *)
        | T.Record (("",(t,false))::l,_) when List.for_all (fun (l,_) -> l <> "") l ->
          t,
          List.may_map
            (fun (l,(t,o)) ->
              if T.is_arr t then
                let ta, t = T.split_arr t in
                let ta = ("",(state,false))::ta in
                let t = T.arr ta t in
                Some (l,(t,o))
              else
                None
            ) l
        | _ -> t, []
      with
      | Not_found ->
        let a = T.fresh_var () in
        a, (a, [])
    in
    let t_alloc = T.arrnl [] state in
    let t_run = T.arrnl [state] t_ret in
    let r =
      [
        "alloc",(t_alloc,false);
        "run",(t_run,false);
      ]@t_aux
    in
    T.arrnl [T.arrnl [] t_out] (T.record r)
  in
  let i ~subst ~state a =
    let prog = List.assoc "" a in
    let t_ret = E.typ prog in
    let ret_t = E.emit_type (E.unquote prog) in
    let state, prog = E.reduce_quote ~subst ~state prog [] in
    let state, prog = E.emit ~subst ~state ~free_vars:true prog in
    let prog = BB.prog ~state:true prog in
    Printf.printf "---\nEmit prog:\n%s---\n\n%!" (B.to_string prog);
    let state_t = B.state_t prog in
    (* TODO: generate a new name each time *)
    let name = "osc" in
    let procs =
      [
        name^"_alloc", B.proc_alloc prog;
        name^"_run", B.proc_run prog;
      ]@(B.procs prog)
    in
    let state = { state with E. rs_procs = procs@state.E.rs_procs } in
    let t_state = T.state () in
    let t_alloc = T.arrnl [] t_state in
    let alloc = E.proc ~t:t_alloc (name^"_alloc",([],state_t)) in
    (* We need to load the state before calling and store it afterwards. *)
    let set_state =
      let b t prog arg =
        let state = arg.(0) in
        let n = arg.(1) in
        let n =
          match n with
          | B.Int n -> n
          | _ -> assert false
        in
        let v = arg.(2) in
        let prog, s = BB.alloc_anon prog state_t in
        let prog = BB.eq_anon prog (B.LVar s) state in
        let prog = BB.eq_anon prog (B.LField(B.RVar s,n)) v in
        prog, B.unit
        (* let prog = BB.eq_alloc prog "_state" state_t state in *)
        (* BB.eq prog "_state" ~field:n v, B.unit *)
      in
      quick_backend "set_state" (T.arrnl [T.state (); T.int] T.unit) b
    in
    let set_state s v e = E.app ~t:T.unit set_state ["",s;"",E.int v;"",e] in
    (* let get_state = *)
    (* let b t prog arg = *)
    (* let state = arg.(0) in *)
    (* let n = arg.(1) in *)
    (* let x = *)
    (* match arg.(2) with *)
    (* | Ident x *)
    (* in *)
    (* let prog = BB.eq_alloc prog "_state" state_t state in *)
    (* BB.eq prog "_state" ~field:n v, B.unit *)
    (* in *)
    (* quick_backend "set_state" (T.arrnl [T.state (); T.int] T.unit) b *)
    (* in *)
    (* let get_state s v e = E.app ~t:T.unit get_state ["",s;"",E.int v;"",e] in *)
    let implem proc_name proc =
      let reduce ~subst ~state arg =
        let st = List.assoc "" arg in
        (* TODO: the argument list should be stored in the order indicated by
           the type, until it's cleared up we forbid unlabeled arguments *)
        assert (List.for_all (fun (l,_) -> l = "") arg);
        let arg = List.remove_assoc "" arg in
        (* TODO: store afterwards *)
        let load = B.map_fv prog (fun x v -> set_state st v (E.ident x)) in
        (* let store = B.map_fv prog (fun x v -> get_state st v (E.ident x)) in *)
        let state_t =
          match proc.B.proc_state with
          | Some state -> [state]
          | None -> []
        in
        let arg_t = List.map (fun (l,e) -> T.emit (E.typ e)) arg in
        let ret_t = proc.B.proc_ret in
        (* TODO: args *)
        (* TODO: return type *)
        let reduce = E.app (E.proc ~t:t_alloc (proc_name,(state_t@arg_t,ret_t))) (("",st)::arg) in
        let reduce = E.seqs (load@[reduce]) in
        state, reduce
      in
      (* TODO: return type *)
      quick_external t_ret reduce
    in
    let run = implem (name^"_run") (B.proc_run prog) in
    let proc_implem = List.map (fun (l,p) -> l, implem l p) (B.procs prog) in
    let r =
      [
        "alloc", alloc;
        "run", run;
      ]@proc_implem
    in
    state, E.record r
  in
  mop "compile" t ~i
*)

(*
let emit_dssi =
  let t _ =
    let a = T.fresh_var () in
    T.arrnl [T.arrnl [] a] T.string
  in
  let i ~subst ~state args =
    let prog = List.assoc "" args in
    let state, prog = E.reduce_quote ~subst ~state prog [] in
    let state, prog = E.emit ~subst ~state ~free_vars:true prog in
    let prog = BB.prog ~state:true prog in
    let prog = B.map_proc_names prog (fun l -> "SAML_DSSI_"^l) in
    Printf.printf "---\nEmit C prog:\n%s---\n\n%!" (B.to_string prog);
    let c = B.C.emit prog in
    let c = String.concat "\n"
      [
        "#include <stdlib.h>";
        "#include <math.h>";
        "#include <stdio.h>";
        "";
        c;
        "";
      ]
    in
    let c = c ^ String.concat "\n"
      [
        "";
        "#define STATE state";
        "#define SAML_name \"saml_synth\"";
        "#define SAML_DSSI_run run";
        "#define SAML_DSSI_alloc alloc";
        "#define SAML_DSSI_free SAML_DSSI_unalloc";
        "";
      ]
    in
    let c = c^Saml_dssi.c in
    state, E.string c
  in
  mop "emit_dssi" t ~i
*)

let () =
  let name = "file_write" in
  let t _ = T.arrnl[T.string; T.string] T.unit in
  let i args =
    let fname = List.assoc "" args in
    let fname = get_string fname in
    let s = List.assoc_nth 1 "" args in
    let s = get_string s in
    file_out fname s;
    E.unit ()
  in
  mop name t ~i

(*
let run =
  let t _ = T.arr ["loop",(T.bool,true); "",(T.arrnl [] T.unit,false)] T.unit in
  let i ~subst ~state args =
    let loop =
      try
        let loop = List.assoc "loop" args in
        match loop.E.desc with
        | E.Cst (E.Bool b) -> b
        | _ -> assert false
      with
      | Not_found -> true
    in
    let prog = List.assoc "" args in
    let state, prog = E.reduce_quote ~subst ~state prog [] in
    file_out "out/output.prog" (E.to_string prog ^ "\n");
    let state, prog = E.emit ~subst ~state prog in
    (* let sr = 44100 in *)
    (* let dt = 1. /. (float_of_int sr) in *)
    (* let prog = BB.init prog "dt" (B.Float dt) in *)
    let prog = BB.output prog B.T.Unit B.unit in
    let prog = BB.procs prog state.E.rs_procs in
    let prog = BB.prog prog in
    file_out "out/output.saml" (B.to_string prog);
    Printf.printf "%s\n%!" (B.to_string prog);
    let prog = B.SAML.emit prog in
    if loop then
      while true do
        ignore (prog ())
      done
    else
      (
        ignore (prog ());
        (* TODO: don't exit *)
        Pervasives.exit 0
      );
    state, E.unit ()
  in
  mop "run" t ~i
*)

(* TODO: we could implement for as an external *)
(*
let for_loop =
  let t _ = T.arrnl[T.int; T.int; T.arrnl [T.int] T.unit] T.unit in
  let b t prog arg =
    let prog, a = BB.eq_alloc_anon prog (T.emit T.int) arg.(0) in
    let prog, b = BB.eq_alloc_anon prog (T.emit T.int) arg.(1) in
    assert false
  in
  mop "for" t b
*)

(** Convert int to float. *)
let () =
  let name = "float" in
  let t _ = T.arrnl [T.int] T.float in
  (* TODO: implem? *)
  let b t prog args =
    let saml a = B.V.float (float (B.V.get_int a.(0))) in
    let c a = a.(0) in
    prog, B.Op (B.extern name ~saml ~c, args)
  in
  mop name t ~b

let () =
  let name = "pow" in
  let t _ = T.arrnl [T.float;T.float] T.float in
  let b t prog args =
    let saml a =
      let x = B.V.get_float a.(0) in
      let y = B.V.get_float a.(1) in
      B.V.float (x ** y)
    in
    let c a = Printf.sprintf "pow(%s,%s)" a.(0) a.(1) in
    prog, B.Op (B.extern name ~saml ~c, args)
  in
  mop name t ~b

(* let assertion = *)
  (* let name = "assert" in *)
  (* let t _ = *)
    (* let a = T.fresh_var () in *)
    (* T.arrnl [T.bool] a *)
  (* in *)
  (* let b t prog args = *)
  (* in *)
  (* mop name t ~b *)

let externals =
  List.map (fun e -> e.E.ext_name, E.make (E.External e)) !externals

let get ?pos x =
  try
    let e = List.assoc x externals in
    match pos with
    | Some pos -> { e with E.pos = pos }
    | None -> e
  with
  | Not_found -> failwith (Printf.sprintf "Internal command %s was not found. Please report." x)
