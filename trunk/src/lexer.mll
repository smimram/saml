{
  open Stdlib
  open Lexing
  open Parser

  let keywords =
    [
      (***** Keywords *****)
      "fun", FUN;
      "let", LET;
      "in", IN;
      "true", BOOL true;
      "false", BOOL false;
      "if", IF;
      "then", THEN;
      "else", ELSE;
      "ref", REF;
      "rec", REC;
      "for", FOR;
      "to", TO;
      "do", DO;
      "done", DONE;
      "module", MODULE;
      "struct", MODULE;
      "end", END;
      "builtin", BUILTIN;
      "static", STATIC;
      "not", BNOT;
      "compile", COMPILE;
      "with", WITH;
      "type", TYPE;
      "include", INCLUDE;
    ]
}

let space = ' ' | '\t' | '\r'

rule token = parse
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
  | "->" { ARR }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | "/" { DIV }
  | "." { DOT }
  | "`"([^' ']+ as s) { VARIANT s }

  (***** Non-meaningful characters *****)
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | "(*"([^'*']|'*'[^')'])*"*)" as comment { for i = 1 to String.count '\n' comment do Lexing.new_line lexbuf done; token lexbuf }
  | "\n" { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
