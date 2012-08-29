(** {2 Global variables } *)

let buffer_length = ref 1024
let channels = ref 2

(** {2 Types} *)

type 'a stream = unit -> 'a

(** {2 Standard functions} *)

let if_then_else b t e = if b then t else e

let n = ref (-1)
let print_float x =
  incr n;
  if !n mod (44100 / 4) = 0 then
    Printf.printf "%f\n%!" x;
  x

(* let print_float x = Printf.printf "%f\n%!" x; x *)

let output writer (f : float stream) =
  let b = ref 0 in
  let buflen = !buffer_length in
  let buf = Array.make buflen 0. in
  let cbuf = Array.make !channels buf in
  while true do
    for i = 0 to buflen - 1 do
      let x = f () in
      buf.(i) <- x;
      (* if x > 1. || x < -1. then Printf.printf "W: overflow %f\n%!" x *)
    done;
    incr b;
    writer#write cbuf 0 buflen
  done

let play sr f = output (new MMPulseaudio.writer "SAML" "sound" !channels sr) f

let save fname sr f = output (new Audio.IO.Writer.to_wav_file !channels sr fname) f

let equals x y = compare x y = 0

let feedback : 'a -> ('a -> 'a stream) -> 'a stream = fun x0 ->
  let x = ref x0 in
  fun f t ->
    x := f !x t;
    !x
