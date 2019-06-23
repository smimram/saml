(** Builtin operations. *)

module T = Type
module E = Lang

type t = E.ffi

let builtins = ref []

let register name ?eval a b =
  let f = E.ffi name ?eval a b in
  builtins := (name, f) :: !builtins

let ff_f f t =
  E.float (f (E.get_float (E.Run.fst t)) (E.get_float (E.Run.snd t)))

(* Floats *)
let () =
  register "fmul" ~eval:(ff_f ( *. )) (T.pair (T.float ()) (T.float ())) (T.unit ())

(* String *)
let () =
  register "string" ~eval:(fun t -> E.string (E.to_string t)) (T.uvar ()) (T.unit ())

(* IO *)
let () =
  register "print" ~eval:(fun t -> print_string (E.get_string t); E.unit ()) (T.string ()) (T.unit ())

let get ?pos name =
  let t = List.assoc name !builtins in
  E.make ?pos t.desc
