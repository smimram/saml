{
  open Stdlib
  open Lexing
  open Parser

  let keywords =
    [
      (***** Keywords *****)
      "def", DEF;
      "begin", BEGIN;
      "end", END;
      "true", BOOL true;
      "false", BOOL false;
      "if", IF;
      "then", THEN;
      "else", ELSE;
      "ref", REF;
      "for", FOR;
      "to", TO;
      "while", WHILE;
      "do", DO;
      "done", DONE;
      "module", MODULE;
      "builtin", BUILTIN;
      "not", BNOT;
      "include", INCLUDE;
      "expand", EXPAND;
      "dt", DT;
      "unref", UNREF;
      "undt", UNDT;
    ]
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

  (***** Identifiers *****)
  | (['_''a'-'z''A'-'Z']['a'-'z''A'-'Z''0'-'9''_']*['\'']* as str)
      {
        try
          List.assoc str keywords
        with
          | Not_found -> IDENT str
      }
  | '"'([^'"']* as str)'"' { STRING str }
  | ['0'-'9']+ as str { INT (int_of_string str) }
  | ['0'-'9']+"."['0'-'9']* as str { FLOAT (float_of_string str) }

  (***** Non-meaningful characters *****)
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | "\n" { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
