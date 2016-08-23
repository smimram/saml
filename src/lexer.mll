{
  open Stdlib
  open Lexing
  open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse
  (***** Symbols *****)
  | "?" { MAYBE }
  | "=" { EQ }
  | "<=" { LE }
  | ">=" { GE }
  | "<" { LT }
  | ">" { GT }
  | "==" { CMP }
  | "&&" { BAND }
  | "||" { BOR }
  | ":=" { SET }
  | "!" { GET }
  | "," { COMMA }
  | ";" { SEMICOLON }
  | ":" { COLON }
  | "(" { LPAR }
  | ")" { RPAR }
  | "[" { LARR }
  | "]" { RARR }
  | "{" { LACC }
  | "}" { RACC }
  | "->" { ARR }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | "/" { DIV }
  | "." { DOT }
  (* | "`"([^' ']+ as s) { VARIANT s } *)

  (***** Keywords *****)
  | "def" { DEF }
  | "begin" { BEGIN }
  | "end" { END }
  | "true" { BOOL true }
  | "false" { BOOL false }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "elseif" { ELIF }
  | "ref" { REF }
  | "for" { FOR }
  | "to" { TO }
  | "while" { WHILE }
  | "do" { DO }
  | "done" { DONE }
  | "module" { MODULE }
  | "builtin" { BUILTIN }
  | "not" { BNOT }
  | "include" { INCLUDE }
  | "expand" { EXPAND }
  | "dt" { DT }
  | "unref" { UNREF }
  | "undt" { UNDT }
  | "fun" { FUN }
  | "nop" { NOP }

  (***** Identifiers *****)
  | (['_''a'-'z''A'-'Z']['a'-'z''A'-'Z''0'-'9''_']*['\'']* as str) { IDENT str }
  | ('"'[^'"']*'"' as str) { STRING (Scanf.sscanf str "%S%!" (fun u -> u)) }
  | ['0'-'9']+ as str { INT (int_of_string str) }
  | ['0'-'9']+"."['0'-'9']* as str { FLOAT (float_of_string str) }

  (***** Non-meaningful characters *****)
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | "\n" { Lexing.new_line lexbuf; PP_NEWLINE }
  | eof { EOF }
