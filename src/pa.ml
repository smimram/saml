(** Operations involving pulseaudio. *)

(*
module T = Builtin.T
module Run = Lang.Run
module P = Pulseaudio

let sample_rate = 44100

let handle = ref None
let handle () =
  match !handle with
  | Some handle -> handle
  | None ->
     let sample =
       {
         P.
         sample_format = P.Sample_format_float32le;
         sample_rate;
         sample_chans = 1
       }
     in
     let h = P.Simple.create ~client_name:"SAML" ~dir:P.Dir_playback ~stream_name:"run" ~sample () in
     handle := Some h;
     h

let () =
  let array_play_run a =
    let a = Run.to_array a.(0) in
    let a = Array.map Run.to_float a in
    (* P.Simple.drain (handle ()); *)
    P.Simple.write (handle ()) [|a|] 0 (Array.length a);
    Lang.unit ()
  in
  Builtin.op "array_play" (T.arrnl [T.array (T.float ())] (T.unit ())) ~run:array_play_run
 *)
