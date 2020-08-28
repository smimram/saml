(** Builtin operations. *)

open Extlib

module T = Type
module E = Lang
module V = Lang.Value

let builtins = ref []

let register name t f =
  let t = T.generalize min_int t in
  builtins := (name,(t,f)) :: !builtins

(* Floats *)
let () =
  let _f name f =
    let t = T.arr [] (T.float ()) in
    let f a = V.float (f ()) in
    register name t f
  in
  let f_f name f =
    let t = T.arrnl [T.float ()] (T.float ()) in
    let f a =
      let x = List.assoc "" a in
      V.float (f (V.to_float x))
    in
    register name t f
  in
  let ff_f name f =
    let t = T.arrnl [T.float (); T.float ()] (T.float ()) in
    let f a =
      let x = List.assoc_nth 0 "" a |> V.to_float in
      let y = List.assoc_nth 1 "" a |> V.to_float in
      V.float (f x y)
    in
    register name t f
  in
  let ff_b name f =
    let t = T.arrnl [T.float (); T.float ()] (T.bool ()) in
    let f a =
      let x = List.assoc_nth 0 "" a |> V.to_float in
      let y = List.assoc_nth 1 "" a |> V.to_float in
      V.bool (f x y)
    in
    register name t f
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
      let x = List.assoc_nth 0 "" a |> V.to_bool in
      let y = List.assoc_nth 1 "" a |> V.to_bool in
      V.bool (f x y)
    in
    register name t f
  in
  let b_b name f =
    let t = T.arrnl [T.bool ()] (T.bool ()) in
    let f a =
      let x = List.assoc "" a |> V.to_bool in
      V.bool (f x)
    in
    register name t f
  in
  bb_b "and" ( && );
  b_b  "not" ( not )

(* Ref *)
let () =
  let a = T.var 0 in
  let t = T.arrnl [a] (T.ref a) in
  let ref_new a =
    let x = List.assoc "" a in
    V.Ref (ref x)
  in
  register "ref_new" t ref_new;
  let t = T.arrnl [T.ref a] a in
  let ref_get a =
    let r = List.assoc "" a |> V.to_ref in
    !r
  in
  register "ref_get" t ref_get;
  let t = T.arrnl [T.ref a; a] (T.unit ()) in
  let ref_set a =
    let r = List.assoc_nth 0 "" a |> V.to_ref in
    let x = List.assoc_nth 1 "" a in
    r := x;
    V.unit
  in
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
  (* register "repr" ~eval:(fun l -> E.string (E.to_string (snd (List.hd l)))) t *)

(* Control *)
let () =
  let a = T.var 0 in
  let t = T.arrno ["if", T.bool (); "then", T.arrnl [] a; "else", T.arrnl [] a] a in
  let ite args =
    let b = List.assoc "if" args |> V.to_bool in
    let t = List.assoc "then" args |> V.to_fun in
    let e = List.assoc "else" args |> V.to_fun in
    if b then t [] else e []
  in
  register "ite" t ite

(* IO *)
(* let () = *)
(* register "print" ~eval:(fun t -> print_string (E.get_string t); E.unit ()) (T.string ()) (T.unit ()) *)

(* Multimedia. *)
let () =
  let t = T.arrnl [T.arrno [T.dtv, T.float ()] (T.pair (T.float ()) (T.float ()))] (T.unit ()) in
  let play a =
    let s = List.assoc "" a |> V.to_fun in
    let s dt = s [T.dtv, V.float dt] |> V.to_pair |> Pair.map V.to_float V.to_float in
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

(** Compiling. *)
let compile_env () = List.map (fun (x,_) -> x, "saml_"^x) !builtins

(** Use a given builtin. *)
let get ?pos name =
  assert (List.mem_assoc name !builtins);
  E.var ?pos name
