(** Preprocessing on files. *)

(* Expand includes. *)
let rec includer tokenizer =
  let queue = ref [] in
  let state = ref false in
  let rec token lexbuf =
    match !queue with
    | (lbuf,ic)::q ->
       begin
         match (includer Lexer.token) lbuf with
         | Parser.EOF -> close_in ic; queue := q; token lexbuf
         | x -> x
       end
    | [] ->
       begin
         match tokenizer lexbuf with
         | Parser.INCLUDE -> state := true; token lexbuf
         | Parser.STRING s when !state ->
            state := false;
            let ic = open_in s in
            let lbuf = Lexing.from_channel ~with_positions:true ic in
            lbuf.lex_curr_p <- { lbuf.lex_curr_p with pos_fname = s };
            queue := (lbuf, ic) :: !queue;
            token lexbuf
         | x -> state := false; x
       end
  in
  token

(* Merge consecutive newlines *)
let merge_newlines tokenizer =
  let state = ref false in
  let rec token lexbuf =
    match tokenizer lexbuf with
    | Parser.NEWLINE ->
       if !state then token lexbuf
       else (state := true; Parser.NEWLINE)
    | x ->
       state := false;
       x
  in
  token

(* Allow a tokenizer to return a list of tokens. *)
let flatten tokenl =
  let queue = ref [] in
  let rec token lexbuf =
    match !queue with
    | t::q -> queue := q; t
    | [] -> queue := tokenl lexbuf; token lexbuf
  in
  token

(* Remove newlines at the end of blocks. *)
let remove_newlines tokenizer =
  let state = ref false in
  let rec token lexbuf =
    match tokenizer lexbuf with
    | Parser.NEWLINE -> state := true; []
    | Parser.END | Parser.EOF as t -> [t]
    | t ->
      let ans = if !state then [Parser.NEWLINE; t] else [t] in
      state := false;
      ans
  in
  flatten token

(* The usual trick for uminus in yacc does not work with our syntax. *)
let uminus tokenizer =
  let state = ref false in
  let rec token lexbuf =
    match tokenizer lexbuf with
    | Parser.LPAR as x -> state := true; x
    | Parser.MINUS when !state -> state := false; Parser.UMINUS
    | x -> state := false; x
  in
  token

(* Add a unit value at then end of files so that we have a valid expression. *)
let end_with_unit tokenizer =
  let token lexbuf =
    match tokenizer lexbuf with
    | Parser.EOF -> [Parser.NEWLINE; Parser.LPAR; Parser.RPAR; Parser.EOF]
    | x -> [x]
  in
  flatten token

let token =
  let (+) f g = g f in
  Lexer.token
  + includer
  + merge_newlines
  + remove_newlines
  + uminus
  + end_with_unit
