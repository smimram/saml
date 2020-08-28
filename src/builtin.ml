(** Builtin operations. *)

open Extlib

module T = Type
module E = Lang
module V = Lang.Value

let builtins = ref []

(** When set to true, the evaluation will be formal, i.e. return constants. *)
let formal = ref false

(** Register a builtin function. *)
let register name t f =
  let f a =
    if !formal then
      V.Neutral (V.App (V.Code ("saml_"^name), a))
    else
      f a
  in
  let t = T.generalize min_int t in
  builtins := (name,(t,f)) :: !builtins

(** Same as [register] but for functions with no labels. *)
let registernl name t f =
  let f a =
    let a = a |> List.map (fun (l,v) -> assert (l = ""); v) |> Array.of_list in
    f a
  in
  register name t f

(* Floats *)
let () =
  let _f name f =
    let t = T.arr [] (T.float ()) in
    let f _ = V.float (f ()) in
    register name t f
  in
  let f_f name f =
    let t = T.arrnl [T.float ()] (T.float ()) in
    let f a =
      let x = a.(0) |> V.get_float in
      V.float (f x)
    in
    registernl name t f
  in
  let ff_f name f =
    let t = T.arrnl [T.float (); T.float ()] (T.float ()) in
    let f a =
      let x = V.get_float a.(0) in
      let y = V.get_float a.(1) in
      V.float (f x y)
    in
    registernl name t f
  in
  let ff_b name f =
    let t = T.arrnl [T.float (); T.float ()] (T.bool ()) in
    let f a =
      let x = V.get_float a.(0) in
      let y = V.get_float a.(1) in
      V.bool (f x y)
    in
    registernl name t f
  in
  ff_f "fadd" ( +. );
  ff_f "fsub" ( -. );
  ff_f "fmul" ( *. );
  ff_f "fdiv" ( /. );
  ff_b "fle"  ( <= );
  ff_b "fge"  ( >= );
  ff_b "flt"  ( < );
  ff_b "fgt"  ( > );
  _f   "pi"   (fun _ -> Float.pi);
  f_f  "sin"  sin

(* Bool *)
let () =
  let bb_b name f =
    let t = T.arrnl [T.bool (); T.bool ()] (T.bool ()) in
    let f a =
      let x = V.get_bool a.(0) in
      let y = V.get_bool a.(1) in
      V.bool (f x y)
    in
    registernl name t f
  in
  let b_b name f =
    let t = T.arrnl [T.bool ()] (T.bool ()) in
    let f a =
      let x = V.get_bool a.(0) in
      V.bool (f x)
    in
    registernl name t f
  in
  bb_b "and" ( && );
  b_b  "not" ( not )

(* Ref *)
let () =
  let refs = ref [] in
  let ref_new a =
    let x = List.assoc "" a in
    if !formal then
      let n = List.length !refs in
      refs := x :: !refs;
      V.code (Printf.sprintf "ref%d" n)
    else V.Ref (ref x)
  in
    let ref_get a =
      let r = List.assoc "" a in
      if !formal then r
      else !(V.get_ref r)
  in
  let ref_set a =
    let r = List.assoc_nth 0 "" a in
    let x = List.assoc_nth 1 "" a in
    if !formal then
      let r = V.get_code r in
      let x = V.compile x in
      V.code (Printf.sprintf "%s = %s" r x)
    else
      (
        (V.get_ref r) := x;
        V.unit
      )
  in
  let a = T.var 0 in
  let t = T.arrnl [a] (T.ref a) in
  register "ref_new" t ref_new;
  let t = T.arrnl [T.ref a] a in
  register "ref_get" t ref_get;
  let t = T.arrnl [T.ref a; a] (T.unit ()) in
  register "ref_set" t ref_set

(* Nullable *)
let () =
  let a = T.var 0 in
  let b = T.var 0 in
  let t = T.arrnl [T.nullable a; T.arrnl [] b; T.arrnl [a] b] b in
  let f _ = failwith "TODO" in
  register "null_elim" t f

(* String *)
(* let () = *)
  (* let t = T.arr [T.var 0] (T.string ()) in *)
  (* register "repr" ~eval:(fun l -> E.string (E.get_string (snd (List.hd l)))) t *)

(* Control *)
let () =
  let a = T.var 0 in
  let t = T.arrno ["if", T.bool (); "then", T.arrnl [] a; "else", T.arrnl [] a] a in
  let ite args =
    let b = List.assoc "if" args |> V.get_bool in
    let t = List.assoc "then" args |> V.get_fun in
    let e = List.assoc "else" args |> V.get_fun in
    if b then t [] else e []
  in
  register "ite" t ite

(* IO *)
let () =
  let t = T.arrnl [T.string ()] (T.unit ()) in
  let print a =
    let s = List.assoc "" a |> V.get_string in
    print_string s;
    V.unit
  in
  register "print" t print

(* Compilation *)
let () =
  let t = T.arrnl [T.arr [] (T.stream (T.pair (T.float ()) (T.float ())))] (T.string ()) in
  let compile a =
    let s = List.assoc "" a |> V.get_fun in
    Printf.printf "begin compilation\n%!";
    formal := true;
    let s = s [] |> V.get_fun in
    let s = s [T.dtv, V.code "DT"] in
    let s = V.compile s in
    formal := false;
    Printf.printf "end compilation\n%!";
    V.string s
  in
  register "compile" t compile

(* Multimedia. *)
let () =
  let t = T.arrnl [T.arrno [T.dtv, T.float ()] (T.pair (T.float ()) (T.float ()))] (T.unit ()) in
  let play a =
    let s = List.assoc "" a |> V.get_fun in
    let s dt = s [T.dtv, V.float dt] |> V.get_pair |> Pair.map V.get_float V.get_float in
    let sample_rate = 44100 in
    let dt = 1. /. float sample_rate in
    let handle =
      let open Pulseaudio in
      let sample =
        {
          sample_format = Sample_format_float32le;
          sample_rate;
          sample_chans = 2
        }
      in
      Simple.create ~client_name:"SAML" ~dir:Dir_playback ~stream_name:"run" ~sample ()
    in
    let len = 1024 in
    let a = Array.init 2 (fun _ -> Array.make len 0.) in
    while true do
      for i = 0 to len-1 do
        let x, y = s dt in
        a.(0).(i) <- x;
        a.(1).(i) <- y;
        (* Printf.printf "%f / %f\n%!" x y *)
      done;
      Pulseaudio.Simple.write handle a 0 len
    done;
    V.unit
  in
  register "play" t play

(** Typing environment. *)
let tenv () = List.map (fun (x,(t,f)) -> x, t) !builtins

(** Environment. *)
let env () = List.map (fun (x,(t,f)) -> x, V.Fun f) !builtins

(** Use a given builtin. *)
let get ?pos name =
  assert (List.mem_assoc name !builtins);
  E.var ?pos name
