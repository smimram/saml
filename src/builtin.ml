(** Builtin operations. *)

module T = Type
module E = Lang

type t = E.ffi

let builtins = ref []

let register name ?eval a b =
  let f = E.ffi name ?eval a b in
  builtins := (name, f) :: !builtins

let f_f name f =
  register name ~eval:(fun t -> E.float (f (E.get_float t))) (T.float ()) (T.float ())

let ff_f name f =
  register name ~eval:(fun t -> E.float (f (E.get_float (E.Run.fst t)) (E.get_float (E.Run.snd t)))) (T.pair (T.float ()) (T.float ())) (T.float ())

(* Floats *)
let () =
  ff_f "fadd" ( +. );
  ff_f "fsub" ( -. );
  ff_f "fmul" ( *. );
  ff_f "fdiv" ( /. );
  f_f "sin" sin

(* String *)
let () =
  register "repr" ~eval:(fun t -> E.string (E.to_string t)) (T.uvar ()) (T.string ())

(* Control *)
let () =
  let a = T.uvar () in
  register "ite" (T.record ["if", T.bool (); "then", T.arr (T.unit ()) a; "else", T.arr (T.unit ()) a]) a

(* IO *)
let () =
  register "print" ~eval:(fun t -> print_string (E.get_string t); E.unit ()) (T.string ()) (T.unit ())

let get ?pos name =
  let t = try List.assoc name !builtins with Not_found -> failwith ("Builtin not implemented: "^name^".") in
  E.make ?pos t.desc
