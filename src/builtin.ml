(** Builtin operations. *)

module T = Type
module E = Lang

type t = E.ffi

let externals = ref []

let op name t a b =
  let f = E.ffi name a b in
  externals := (name, f) :: !externals

let get ?pos x =
  try
    let e = List.assoc x !externals in
    match pos with
    | Some pos -> { e with E.pos = pos }
    | None -> e
  with
  | Not_found -> failwith (Printf.sprintf "Internal command %s was not found. Please report." x)
