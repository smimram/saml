(** Main part of the program. *)

open Stdlib
open Common

(** Parse a saml file. *)
let parse_file parse f =
  let sin =
    let fi = open_in f in
    let flen = in_channel_length fi in
    let buf = Bytes.create flen in
    really_input fi buf 0 flen;
    close_in fi;
    Bytes.to_string buf
  in
  let lexbuf = Lexing.from_string sin in
  lexbuf.Lexing.lex_start_p <- { lexbuf.Lexing.lex_start_p with Lexing.pos_fname = f };
  lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = f };
  try
    parse Preproc.token lexbuf
  with
    (* TODO: use string_of_pos *)
    | Failure s when s = "lexing: empty token" ->
      let pos = Lexing.lexeme_end_p lexbuf in
      error
        "Lexing error in file %s at line %d, character %d."
        pos.Lexing.pos_fname
        pos.Lexing.pos_lnum
        (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
    | Parser.Error | Parsing.Parse_error ->
      let pos = (Lexing.lexeme_end_p lexbuf) in
      error
        "Parsing error in file %s at word \"%s\", line %d, character %d."
        pos.Lexing.pos_fname
        (Lexing.lexeme lexbuf)
        pos.Lexing.pos_lnum
        (pos.Lexing.pos_cnum - pos.Lexing.pos_bol - 1)

let parse_file = parse_file Parser.prog

let output_file = ref "out.ml"

let usage = "saml -- SAML Ain't a Monadic Language\nusage: saml [options] file"

let () =
  Printexc.record_backtrace true;
  let file_in = ref [] in
  Arg.parse
    (Arg.align
       [
         "-O", Arg.Int (fun n -> Config.Compiler.optimize := (n <> 0)), " Optimization level";
         "-o", Arg.Set_string output_file, " Output file name.";
       ]
    )
    (fun s -> file_in := s::!file_in)
    usage;
  let fname =
    match !file_in with
    | [f] -> f
    | _ -> error "Exactly one .saml file should be present on command-line."
  in
  let prog = parse_file fname in
  let prog = ref prog in
  let pass name f =
    try
      Printf.printf "****** %s *****\n\n%!" name;
      let s = f !prog in
      Printf.printf "%s\n\n%!" s
    with
    | Lang.Typing (pos, msg) ->
      error "Typing error at %s: %s" (Common.string_of_pos pos) msg
  in
  pass "Parsing program" Lang.to_string;
  pass "Checking type" (fun e -> Lang.check (Builtin.tenv ()) e; Type.to_string (Lang.typ e));
  pass "Evaluating program" (fun e -> Lang.V.to_string (Lang.eval [] e));
  (* pass "Infering type" (fun e -> Type.to_string (Lang.infer_type e)); *)
  (* pass "Running program" (fun e -> Lang.run e; ""); *)
  ()
