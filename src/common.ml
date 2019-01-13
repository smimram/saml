(** Common procedures. *)

open Core

(** Print a debugging message. *)
let debug = Printf.printf

(** Print an error. *)
let error s =
  Printf.eprintf "%s\n%!" s;
  exit 1

(** Print a warning. *)
let warning s =
  Printf.eprintf "Warning: %s\n%!" s

(** A position in source file. *)
type pos = Lexing.position * Lexing.position

(** Dummy position. *)
let dummy_pos = Lexing.dummy_pos, Lexing.dummy_pos

(** String representation of a position. *)
let string_of_pos (p1,p2) =
  let l1 = p1.Lexing.pos_lnum in
  let l2 = p2.Lexing.pos_lnum in
  let b1 = p1.Lexing.pos_bol in
  let b2 = p2.Lexing.pos_bol in
  let c1 = p1.Lexing.pos_cnum in
  let c2 = p2.Lexing.pos_cnum in
  let c1 = c1 - b1 in
  let c2 = c2 - b2 in
  (
    if p1.Lexing.pos_fname <> "" then
      Printf.sprintf "in file %s " p1.Lexing.pos_fname
    else
      ""
  ) ^
  if l1 = l2 then
    if c1 = c2 then
      Printf.sprintf "line %d character %d" l1 c1
    else
      Printf.sprintf "line %d characters %d-%d" l1 c1 c2
  else
    Printf.sprintf "from line %d character %d to line %d character %d" l1 c1 l2 c2

(** Create a function which will return a new integer on each call with a given
    name. *)
let instance_counter () =
  let cnt = ref [] in
  fun name ->
    try
      let n = List.assoc name !cnt in
      cnt := List.map (fun (n,k) -> if n = name then n,k+1 else n,k) !cnt;
      n
    with
      | Not_found ->
        cnt := (name,1) :: !cnt;
        0

(** Given a strictly positive integer, generate a name in [a-z]+: a, b, ... z,
    aa, ab, ... az, ba, ... *)
let string_of_univ =
  let base = 26 in
  let c i = char_of_int (int_of_char 'a' + i - 1) in
  let add i suffix = Printf.sprintf "%c%s" (c i) suffix in
  let rec n suffix i =
    if i <= base then
      add i suffix
    else
      let head = i mod base in
      let head = if head = 0 then base else head in
      n (add head suffix) ((i-head)/base)
  in
  n ""

(** Namer for universal variables. *)
let univ_namer () =
  let vars = ref [] in
  fun v ->
    if not (List.memq v !vars) then vars := !vars @ [v];
    "'" ^ string_of_univ (List.indexq v !vars + 1)

let mapperq f =
  let l = ref [] in
  fun x ->
    if not (List.mem_assq x !l) then l := (x, f x) :: !l;
    List.assq x !l

(** Write a string on a file. *)
let file_out fname s =
  let oc = open_out fname in
  output_string oc s;
  close_out oc
