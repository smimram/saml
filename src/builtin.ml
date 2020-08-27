(** Builtin operations. *)

module T = Type
module E = Lang

type t = E.ffi

let builtins = ref []

let register name ?eval t =
  let t = T.generalize min_int t in
  let f = E.ffi name ?eval t in
  builtins := (name, f) :: !builtins

let f_f name f =
  let t = T.arrnl [T.float ()] (T.float ()) in
  let eval = function
    | [_,x] -> E.float (f (E.get_float x))
    | _ -> assert false
  in
  register name ~eval t

let ff_f name f =
  let t = T.arrnl [T.float (); T.float ()] (T.float ()) in
  let eval = function
    | [_,x;_,y] -> E.float (f (E.get_float x) (E.get_float y))
    | _ -> assert false
  in
  register name ~eval t

let ff_b name f =
  let t = T.arrnl [T.float (); T.float ()] (T.bool ()) in
  register name t

(* Floats *)
let () =
  ff_f "fadd" ( +. );
  ff_f "fsub" ( -. );
  ff_f "fmul" ( *. );
  ff_f "fdiv" ( /. );
  ff_b "fle" ( <= );
  ff_b "fge" ( >= );
  ff_b "flt" ( < );
  ff_b "fgt" ( > );
  f_f "sin" sin

(* Bool *)
let () =
  let bb_b name f =
    let t = T.arrnl [T.bool (); T.bool ()] (T.bool ()) in
    register name t
  in
  bb_b "and" ( && )

(* Ref *)
let () =
  let a = T.var 0 in
  let t = T.arrnl [a] (T.ref a) in
  register "ref_new" t;
  let t = T.arrnl [T.ref a] a in
  register "ref_get" t;
  let t = T.arrnl [T.ref a; a] (T.unit ()) in
  register "ref_set" t

(* Nullable *)
let () =
  let a = T.var 0 in
  let b = T.var 0 in
  let t = T.arrnl [T.nullable a; T.arrnl [] b; T.arrnl [a] b] b in
  register "null_elim" t

(* String *)
(* let () = *)
  (* let t = T.arr [T.var 0] (T.string ()) in *)
  (* register "repr" ~eval:(fun l -> E.string (E.to_string (snd (List.hd l)))) t *)

(* Control *)
let () =
  let a = T.var 0 in
  let t = T.arrno ["if", T.bool (); "then", T.arrnl [] a; "else", T.arrnl [] a] a in
  register "ite" t

(* IO *)
(* let () = *)
(* register "print" ~eval:(fun t -> print_string (E.get_string t); E.unit ()) (T.string ()) (T.unit ()) *)

let tenv () =
  let typ e =
    match e.E.descr with
    | E.FFI f -> f.E.ffi_type
    | _ -> assert false
  in
  List.map (fun (f,e) -> f, typ e) !builtins

let get ?pos name =
  let t = try List.assoc name !builtins with Not_found -> failwith ("Builtin not implemented: "^name^".") in
  E.make ?pos t.descr
