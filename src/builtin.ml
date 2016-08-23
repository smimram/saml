(** Builtin operations. *)

open Stdlib
module E = Lang
module Run = E.Run

type t = E.extern

module T = struct
  include Type

  let var () = var max_int

  let ii_i = arrnl [int (); int ()] (int ())

  let f_f = arrnl [float ()] (float ())

  let ff_f = arrnl [float (); float ()] (float ())
end

let externals = ref ([] : t list)

let op name ?reduce ?run t =
  let run =
    Option.default
      (fun _ -> failwith ("No implementation for " ^ name))
      run
  in
  let ext =
    {
      E.
      ext_name = name;
      ext_type = t;
      ext_reduce = (fun _ -> assert false);
      ext_run = run
    }
  in
  ext.E.ext_reduce <-
    begin
      match reduce with
      | Some f -> f
      | None ->
         fun a ->
         let a = Array.to_list a in
         let a = List.map (fun e -> "",e) a in
         E.app (E.make (E.External ext)) a
    end;
  externals := ext :: !externals

(** Integer operations. *)
let () =
  let ii_i_run f a = E.value (E.Int (f (Run.to_int a.(0)) (Run.to_int a.(1)))) in
  op "iadd" T.ii_i ~run:(ii_i_run (+));
  op "isub" T.ii_i ~run:(ii_i_run (-));
  let float_of_int_run a = E.value (E.Float (float_of_int (Run.to_int a.(0)))) in
  op "float_of_int" (T.arrnl [T.int ()] (T.float ())) ~run:float_of_int_run

(** Floating point operations. *)
let () =
  let f_f_run f a = E.float (f (Run.to_float a.(0))) in
  let ff_f_run f a = E.float (f (Run.to_float a.(0)) (Run.to_float a.(1))) in
  op "fadd" T.ff_f ~run:(ff_f_run (+.));
  op "fsub" T.ff_f ~run:(ff_f_run (-.));
  (* let fmul_red a = *)
    (* let x = a.(0) in *)
    (* let y = a.(1) in *)
    (* if Run.is_float x && Run.is_float y *)
    (* then E.float (Run.get_float x +. Run.get_float y) *)
    (* else  *)
  (* in *)
  op "fmul" T.ff_f ~run:(ff_f_run ( *.));
  op "fdiv" T.ff_f ~run:(ff_f_run (/.));
  let pi_red _ = E.value (E.Float pi) in
  op "pi" (T.arr [] (T.float ())) ~reduce:pi_red;
  op "sin" T.f_f ~run:(f_f_run sin)

(** Commands. *)
let () =
  let print_run a =
    let s =
      match a.(0).E.desc with
      | E.Value (E.String s) -> s
      | _ -> E.to_string a.(0)
    in
    print_string s; flush stdout; E.unit ()
  in
  op "print" (T.arrnl [T.var ()] (T.unit ())) ~run:print_run

(** Arrays. *)
let () =
  let a = T.var () in
  let array_create_run a = E.make (E.Array (Array.make (Run.to_int a.(0)) a.(1)))in
  op "array_create" (T.arrnl [T.int (); a] (T.array a)) ~run:array_create_run;
  let array_get_run a =
    let n = Run.to_int a.(1) in
    let a = Run.to_array a.(0) in
    a.(n)
  in
  op "array_get" (T.arrnl [T.array a; T.int ()] a) ~run:array_get_run;
  let array_set_run a =
    let n = Run.to_int a.(1) in
    let e = a.(2) in
    let a = Run.to_array a.(0) in
    a.(n) <- e;
    E.unit ()
  in
  op "array_set" (T.arrnl [T.array a; T.int (); a] (T.unit ())) ~run:array_set_run

let get ?pos x =
  let externals =
    List.map (fun e -> e.E.ext_name, E.make (E.External e)) !externals
  in
  try
    let e = List.assoc x externals in
    match pos with
    | Some pos -> { e with E.pos = pos }
    | None -> e
  with
  | Not_found -> failwith (Printf.sprintf "Internal command %s was not found. Please report." x)
