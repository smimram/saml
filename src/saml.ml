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
    buf
  in
  let lexbuf = Lexing.from_string sin in
  lexbuf.Lexing.lex_start_p <- { lexbuf.Lexing.lex_start_p with Lexing.pos_fname = f };
  lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = f };
  try
    parse Lexer.token lexbuf
  with
    (* TODO: use string_of_pos *)
    | Failure s when s = "lexing: empty token" ->
      let pos = Lexing.lexeme_end_p lexbuf in
      let err =
        Printf.sprintf "Lexing error in file %s at line %d, character %d."
          pos.Lexing.pos_fname
          pos.Lexing.pos_lnum
          (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
      in
      error err
    | Parsing.Parse_error ->
      let pos = (Lexing.lexeme_end_p lexbuf) in
      let err =
        Printf.sprintf "Parsing error in file %s at word \"%s\", line %d, character %d."
          pos.Lexing.pos_fname
          (Lexing.lexeme lexbuf)
          pos.Lexing.pos_lnum
          (pos.Lexing.pos_cnum - pos.Lexing.pos_bol - 1)
      in
      error err

let parse_file_ctx = parse_file Parser.prog_ctx
let parse_file = parse_file Parser.prog

let () = Lang.parse_file_ctx_fun := parse_file_ctx

let output_file = ref "out.ml"

let usage = "saml -- SAML Ain't a Monadic Language\nusage: saml [options] file"

let () =
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
  let pass name f prog =
    try
      Printf.printf "****** %s *****\n\n%!" name;
      let prog = f prog in
      Printf.printf "%s\n\n%!" (Lang.to_string prog);
      prog
    with
    | Lang.Typing (pos, msg) ->
      let err = Printf.sprintf "Typing error at %s: %s" (Common.string_of_pos pos) msg in
      error err
  in
  let prog = pass "Parsing program" id prog in
  let prog = pass "Infering type" (fun prog -> let t = Lang.infer_type prog in prog) prog in
  let prog = pass "Reducing program" (fun e -> Lang.reduce e) prog in
  (* let prog = pass "Infering type" (Lang.E.infer_type ~annot:false) prog in *)
  (* Printf.printf "****** Emit program *****\n\n%!"; *)
  (* let prog = Lang.E.emit prog in *)
  (* let prog = Lang.E.BB.prog prog in *)
  (* Printf.printf "%s\n%!" (Backend.to_string prog); *)
  (* Printf.printf "****** ML program *****\n\n%!"; *)
  (* let ml = Backend_ocaml.emit prog in *)
  (* Printf.printf "%s\n%!" ml; *)
  (* File.write "out/output.ml" ml; *)
  (* (\* Printf.printf "****** C program *****\n\n%!"; *\) *)
  (* (\* let c = Backend_c.emit prog in *\) *)
  (* (\* Printf.printf "%s\n%!" c; *\) *)
  (* (\* File.write "out/output.c" c; *\) *)
  (* Backend_interp.emit prog; *)
  ()
