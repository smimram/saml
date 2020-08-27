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

(* Floats *)
let () =
  ff_f "fadd" ( +. );
  ff_f "fsub" ( -. );
  ff_f "fmul" ( *. );
  ff_f "fdiv" ( /. );
  f_f "sin" sin

(* Ref *)
let () =
  let a = T.var 0 in
  let t = T.arrnl [a] (T.ref a) in
  register "ref_new" t;
  let t = T.arrnl [T.ref a] a in
  register "ref_get" t;
  let t = T.arrnl [T.ref a; a] (T.unit ()) in
  register "ref_set" t

(* String *)
(* let () = *)
  (* let t = T.arr [T.var 0] (T.string ()) in *)
  (* register "repr" ~eval:(fun l -> E.string (E.to_string (snd (List.hd l)))) t *)

(* Control *)
(* let () = *)
  (* let a = T.uvar () in *)
  (* register "ite" (T.record ["if", T.bool (); "then", T.arr (T.unit ()) a; "else", T.arr (T.unit ()) a]) a *)

(* IO *)
(* let () = *)
  (* register "print" ~eval:(fun t -> print_string (E.get_string t); E.unit ()) (T.string ()) (T.unit ()) *)

let get ?pos name =
  let t = try List.assoc name !builtins with Not_found -> failwith ("Builtin not implemented: "^name^".") in
  E.make ?pos t.descr
