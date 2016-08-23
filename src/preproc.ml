(** Preprocessing on files. *)

(* Remove the new lines and merge IDENT LPAR into IDENT_LPAR if they are not
separated by a newline. This is necessary to distinguish f(3), a function
application, and f\n(3), a sequence consisting of f and then 3. *)
let strip_newlines tokenizer =
  let state = ref None in
  let rec token lexbuf =
    match !state with
    | None ->
       begin match tokenizer lexbuf with
       | Parser.PP_NEWLINE -> token lexbuf
       | Parser.IDENT _ as v -> state := Some v; token lexbuf
       | x -> x
       end
    | Some (Parser.IDENT var as v) ->
       begin match tokenizer lexbuf with
       | Parser.LPAR -> state := None; Parser.IDENT_LPAR var
       | Parser.PP_NEWLINE -> state := None; v
       | x -> state := Some x; v
       end
    | Some x -> state := None ; x
  in
  token

let token =
  let (+) f g = g f in
  Lexer.token
  + strip_newlines
