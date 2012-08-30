open Stdlib
open Common

(* let parse_expr e = *)
  (* let lexbuf = Lexing.from_string e in *)
  (* Parser.expr Lexer.token lexbuf *)

let parse_file f =
  let sin =
    let fi = open_in f in
    let flen = in_channel_length fi in
    let buf = String.create flen in
    really_input fi buf 0 flen;
    close_in fi;
    buf
  in
  let lexbuf = Lexing.from_string sin in
  try
    Parser.prog Lexer.token lexbuf
  with
    | Failure "lexing: empty token" ->
      let pos = (Lexing.lexeme_end_p lexbuf) in
      let err =
        Printf.sprintf "Lexing error at line %d, character %d."
          pos.Lexing.pos_lnum
          (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
      in
      error err
    | Parsing.Parse_error ->
      let pos = (Lexing.lexeme_end_p lexbuf) in
      let err =
        Printf.sprintf "Parse error at word \"%s\", line %d, character %d."
          (Lexing.lexeme lexbuf)
          pos.Lexing.pos_lnum
          (pos.Lexing.pos_cnum - pos.Lexing.pos_bol - 1)
      in
      error err

let output_file = ref "out.ml"

let usage = "saml -- Stream Advanced Monadic Language\nusage: saml [options] file"

let infer_type ?annot p =
  try
    (* (Builtin.decls@p) *)
    Lang.M.infer_type ?annot p
  with
    | Lang.E.Typing (pos, msg) ->
      let msg =
        Printf.sprintf "\nError %s: %s"
          (string_of_pos pos)
          msg
      in
      error msg

let () =
  let file_in = ref [] in
  Arg.parse
    (Arg.align
       [
         "-O", Arg.Int (fun n -> if n = 0 then Config.Compiler.optimize := false), " Optimization level";
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
  let pass name f prog =
    Printf.printf "****** %s *****\n\n%!" name;
    let prog = f prog in
    Printf.printf "%s\n\n%!" (Lang.M.to_string prog);
    prog
  in
  let prog = pass "Parsing program" id prog in
  let prog = pass "Infering type" (infer_type ~annot:fname) prog in
  let prog = pass "Reducing program" Lang.M.reduce prog in
  ()
  (* Printf.printf "* Emitting program:\n%!"; *)
  (* Lang.M.emit prog *)
