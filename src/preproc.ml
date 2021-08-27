(** Preprocessing on files. *)

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

(*
(* Remove the new lines and merge IDENT LPAR into IDENT_LPAR if they are not
   separated by a newline. This is necessary to distinguish f(3), a function
   application, and f\n(3), a sequence consisting of f and then 3. *)
let strip_newlines tokenizer =
  let state = ref None in
  let rec token lexbuf =
    match !state with
    | None ->
       begin
         match tokenizer lexbuf with
         | Parser.PP_NEWLINE -> token lexbuf
         | Parser.IDENT _ as v -> state := Some v; token lexbuf
         | x -> x
       end
    | Some (Parser.IDENT var as v) ->
       begin
         match tokenizer lexbuf with
         | Parser.LPAR -> state := None; Parser.IDENT_LPAR var
         | Parser.PP_NEWLINE -> state := None; v
         | x -> state := Some x; v
       end
    | Some x -> state := None ; x
  in
  token
 *)

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

(* The usual trick for uminus in yacc does not work with our syntax. *)
let uminus tokenizer =
  let state = ref false in
  let token lexbuf =
    let x = tokenizer lexbuf in
    match x with
    | Parser.LPAR -> state := true; x
    | Parser.MINUS when !state -> state := false; Parser.UMINUS
    | _ -> state := false; x
  in
  token

let token =
  let (+) f g = g f in
  Lexer.token
  + includer
  + merge_newlines
  + uminus
