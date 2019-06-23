(** Builtin operations. *)

module T = Type
module E = Lang

type t = E.ffi

let register name ?eval a b =
  let f = E.ffi name ?eval a b in
  E.tenv := (name, T.arr a b) :: !E.tenv;
  E.env := (name, f) :: !E.env

let () =
  Printf.printf "Registering builtins.\n%!";
  register "print" ~eval:(fun t -> print_string (E.get_string t); E.unit ()) (T.string ()) (T.unit ())
