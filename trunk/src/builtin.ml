open Stdlib
open Common
open Lang

module B = Backend
module BB = B.Builder

let may_implem i =
  maybe (fun ~subst ~state _ -> raise E.Cannot_reduce) i

let may_backend b =
  maybe (fun _ -> assert false) b

(** Used for operators reducing to a closure. *)
let quick_external t i =
  let ext =
    {
      E.
      ext_name = "quick_external";
      ext_t = (fun _ -> t);
      ext_backend = (fun _ -> assert false);
      ext_implem = i;
    }
  in
  E.make ~t (E.External ext)

let quick_backend name t b =
  let ext =
    {
      E.
      ext_name = "quick_"^name;
      ext_t = (fun _ -> t);
      ext_backend = b;
      ext_implem = may_implem None;
    }
  in
  E.make ~t (E.External ext)

let op name t ?i b =
  {
    E.
    ext_name = name;
    ext_t = (fun _ -> t);
    ext_backend = (fun _ prog a -> prog, B.Op(b,a));
    ext_implem = may_implem i;
  }

let mop name ?i ?b t =
  assert (i <> None || b <> None);
  {
    E.
    ext_name = name;
    ext_t = t;
    ext_backend = may_backend b;
    ext_implem = may_implem i;
  }

let get_string e =
  match e.E.desc with
  | E.Cst (E.String s) -> s
  | _ -> raise E.Cannot_reduce

let exit =
  let t _ = T.arrnl [T.int] (T.fresh_var ()) in
  let i ~subst ~state args =
    let n = List.assoc "" args in
    let n =
      match n.E.desc with
      | E.Cst (E.Int n) -> n
      | _ -> assert false
    in
    exit n
  in
  mop "exit" t ~i

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
  let i ~subst ~state args =
    let x = List.assoc "" args in
    let y = List.assoc_nth 1 "" args in
    match x.E.desc, y.E.desc with
    | E.Cst (E.Int x), E.Cst (E.Int y) -> state, E.int (iop x y)
    | E.Cst (E.Float x), E.Cst (E.Float y) -> state, E.float (fop x y)
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

let add = nn_n "add" (+.) (+) "(+.)" "(+)" "+"
let sub = nn_n "sub" (-.) (-) "(-.)" "(-)" "-"
let pow = nn_n "pow" ( ** ) pow "( ** )" "( pow )" "pow"

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
  let i ~subst ~state args =
    let x = List.assoc "" args in
    let y = List.assoc_nth 1 "" args in
    match x.E.desc, y.E.desc with
    | E.Cst (E.Int x), E.Cst (E.Int y) -> state, E.bool (iop x y)
    | E.Cst (E.Float x), E.Cst (E.Float y) -> state, E.bool (fop x y)
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

let print =
  let t _ = (T.arrnl [T.fresh_var ()] T.unit) in
  let i ~subst ~state args =
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
    prog, B.Op(B.Print (T.emit t),args)
  in
  mop "print" t ~i ~b

let array_play =
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
        let w = new Samlib.pulseaudio_writer "SAML" "sound" channels sr in
        (* let w = new Audio.IO.Writer.to_wav_file channels sr "output.wav" in *)
        writer := Some w;
        w
    in
    writer#write [|buf|] 0 (Array.length buf);
    B.V.unit
  in
  let extern = B.extern ~saml "array_play" in
  op "array_play" (T.arrnl [T.fresh_var()] T.unit) extern
  (* extern *)

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

let array_create =
  let t _ =
    let a = T.fresh_var () in
    T.arrnl [T.int; a] (T.array ~alloc:true a)
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
  mop "array_create" t ~b

let array_set =
  let t _ =
    let a = T.fresh_var () in
    T.arrnl [T.array a; T.int; a] T.unit
  in
  let b t prog a =
    let t, _ = T.split_arr t in
    let t, _ = List.assoc_nth 2 "" t in
    let prog, x = BB.eq_alloc_anon prog (T.emit t) a.(0) in
    let prog = BB.eq_anon prog (B.LCell(x,a.(1))) a.(2) in
    prog, B.Unit
  in
  mop "array_set" t ~b

let array_get =
  let t _ =
    let a = T.fresh_var () in
    T.arrnl [T.array a; T.int] a
  in
  let i ~subst ~state arg =
    (* Printf.printf "array_get impl\n%!"; *)
    let array = List.assoc "" arg in
    let n = List.assoc_nth 1 "" arg in
    match array.E.desc, n.E.desc with
    | E.Array a, E.Cst (E.Int n) -> state, List.nth n a
    | _ -> raise E.Cannot_reduce
  in
  let b t prog a =
    let x =
      match a.(0) with
      | B.Var x -> x
      | _ -> assert false
    in
    prog, B.Cell(x, a.(1))
  in
  mop "array_get" t ~i ~b

let array_tail =
  let t _ =
    let v = T.fresh_var () in
    let a = T.array ~static:true v in
    T.arrnl [a] a
  in
  let i ~subst ~state a =
    let array = List.assoc "" a in
    match array.E.desc with
    | E.Array a ->
      let a = List.tl a in
      state, E.array ~t:(E.typ array) a
    | _ -> raise E.Cannot_reduce
  in
  mop "array_tail" t ~i

let array_length =
  let t _ =
    let v = T.fresh_var () in
    let a = T.array ~static:true v in
    T.arrnl [a] T.int
  in
  let i ~subst ~state a =
    let array = List.assoc "" a in
    match array.E.desc with
    | E.Array a -> state, E.int (List.length a)
    | _ -> raise E.Cannot_reduce
  in
  mop "array_length" t ~i

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
    let t_alloc = T.arrnl [] { state with T.alloc = true } in
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
    (* let dt = 1. /. 44100. in *)
    (* let prog = BB.init prog "dt" (B.Float dt) in *)
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
    (* let run = *)
    (* let run ~subst ~state arg = *)
    (* let st = List.assoc "" arg in *)
    (* (\* TODO: store afterwards *\) *)
    (* let load = B.map_fv prog (fun x v -> set_state st v (E.ident x)) in *)
    (* let run = E.app (E.proc ~t:t_alloc (name^"_run",([state_t],ret_t))) arg in *)
    (* let run = E.seqs (load@[run]) in *)
    (* state, run *)
    (* in *)
    (* quick_external t_ret run *)
    (* in *)
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
        "#define SAML_name \"saml_syth\"";
        "#define SAML_synth run";
        "#define SAML_synth_alloc alloc";
        "#define SAML_synth_period period";
        "#define SAML_synth_reset reset";
        "#define SAML_synth_free unalloc";
        "#define SAML_synth_set_velocity velocity";
        "#define SAML_synth_set_freq freq";
        "#define SAML_synth_note_off release";
        "#define SAML_synth_is_active is_active";
        "#define SAML_synth_activate activate";
        "";
      ]
    in
    let c = c^Saml_dssi.c in
    state, E.string c
  in
  mop "emit_dssi" t ~i

let write_file =
  let t _ = T.arrnl[T.string; T.string] T.unit in
  let i ~subst ~state args =
    let fname = List.assoc "" args in
    let fname = get_string fname in
    let s = List.assoc_nth 1 "" args in
    let s = get_string s in
    file_out fname s;
    state, E.unit ()
  in
  mop "write_file" t ~i

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

let float_of_int =
  let name = "float" in
  let t _ = T.arrnl [T.int] T.float in
  (* TODO: implem? *)
  let b t prog args =
    let saml a = B.V.float (float (B.V.get_int a.(0))) in
    prog, B.Op (B.extern name ~saml, args)
  in
  mop name t ~b

(* TODO: use GADT for cleanly handling type especially with backend
   externals. *)
let impl =
  let tf = T.float in
  let tb = T.bool in
  let f_f = T.arrnl [tf] tf in
  let ff_f = T.arrnl [tf;tf] tf in
  let bb_b = T.arrnl [tb;tb] tb in
  let b_b = T.arrnl [tb] tb in
  let aa_b () = let a = T.fresh_var () in T.arrnl [a;a] tb in
  [
    (* Arithmetic. *)
    (* op "add" ff_f B.Add; *)
    (* op "sub" ff_f B.Sub; *)
    add;
    sub;
    op "mul" ff_f B.Mul;
    op "div" ff_f B.Div;
    pow;
    op "pi" tf B.Pi;
    op "sin" f_f B.Sin;
    op "cos" f_f B.Cos;
    op "exp" f_f B.Exp;
    op "random" f_f (B.extern ~saml:(fun a -> B.V.float (Random.float (B.V.get_float a.(0)))) ~ocaml:"Random.float" "random");

    (* Booleans. *)
    (* op "le" ff_b B.Le; *)
    le;
    (* op "lt" ff_b B.Lt; *)
    lt;
    op "eq" (aa_b()) B.Eq;
    op "and" bb_b (B.extern ~saml:(fun a -> B.V.bool ((B.V.get_bool a.(0)) && (B.V.get_bool a.(1)))) ~ocaml:"( && )" "and");
    op "or" bb_b (B.extern ~saml:(fun a -> B.V.bool ((B.V.get_bool a.(0)) || (B.V.get_bool a.(1)))) ~ocaml:"( || )" "or");
    op "not" b_b (B.extern ~saml:(fun a -> B.V.bool (not (B.V.get_bool a.(0)))) ~ocaml:"( not )" "not");

    (* Conversions. *)
    float_of_int;

    (* Arrays. *)
    array_create;
    array_get;
    array_set;
    array_length;
    array_tail;
    array_play;

    (* Actions. *)
    exit;
    compile;
    emit_dssi;
    run;
    print;
    write_file;

    (* Sound. *)
    (* play_buffer_mono; *)

    (* Debug. *)
    op "play" (T.arrnl [T.arr [] T.float] T.unit) B.Botop;
    op "save" (T.arrnl [T.arr [] T.float] T.unit) B.Botop;
    (* dssi; *)
  ]

let externals =
  List.map (fun e -> e.E.ext_name, E.make (E.External e)) impl

(* let decls = *)
(* List.map (fun (x,e) -> M.Decl (x,e)) externals *)

let get ?pos x =
  try
    let e = List.assoc x externals in
    match pos with
    | Some pos -> { e with E.pos = pos }
    | None -> e
  with
  | Not_found -> failwith (Printf.sprintf "Internal command %s was not found. Please report." x)

let () =
  Lang.E.backend_get := get
