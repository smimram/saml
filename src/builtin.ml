(** Builtin operations. *)

open Stdlib
open Lang

type t = E.extern

module T = struct
  include Type

  let ff_f = arrnl [float (); float ()] (float ())
end

let externals = ref ([] : t list)

let op name ?r t =
  let ext =
    {
      E.
      ext_name = name;
      ext_type = t;
      ext_reduce = (fun _ -> assert false);
      ext_exec = (fun _ -> failwith ("No implementation for " ^ name))
    }
  in
  ext.E.ext_reduce <-
    begin
      match r with
      | Some f -> f
      | None -> fun a -> E.app (E.make (E.External ext)) a
    end;
  externals := ext :: !externals

let () =
  op "fadd" T.ff_f;
  op "fmul" T.ff_f

let externals =
  List.map (fun e -> e.E.ext_name, E.make (E.External e)) !externals

let get ?pos x =
  try
    let e = List.assoc x externals in
    match pos with
    | Some pos -> { e with E.pos = pos }
    | None -> e
  with
  | Not_found -> failwith (Printf.sprintf "Internal command %s was not found. Please report." x)
