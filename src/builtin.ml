(** Builtin operations. *)

module T = Type
module E = Lang

type t = E.ffi

let register name ?eval a b =
  let f = E.ffi name a b in
  E.tenv := (name, T.arr a b) :: !E.tenv;
  E.env := (name, f) :: !E.env

let () =
  let a = T.uvar () in
  register "print" ~eval:(fun t -> print_string (E.to_string t); t) a a
