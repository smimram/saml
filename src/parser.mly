%{
    open Stdlib
    open Lang

    let letin ~pos (pat,def) body =
      letin ~pos pat def body
%}

%token DEF LET BEGIN END FUN ARR DOT
%token MODULE BUILTIN INCLUDE
%token REF GET SET UNREF DT UNDT
%token FOR WHILE TO DO DONE
%token CMP LE GE LT GT
%token BAND BOR BNOT
%token IF THEN ELSE ELIF
%token LPAR RPAR LARR RARR LACC RACC
%token SEMICOLON COLON COMMA MAYBE
%token EQ PLUS MINUS UMINUS TIMES DIV POW
%token EXPAND
%token EOF
%token PP_NEWLINE
%token NOP
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <string> IDENT IDENT_LPAR
%token <string> STRING
%token <string> VARIANT

%nonassoc ARR
%right SEMICOLON
%nonassoc THEN
%nonassoc ELSE
%right BOR
%right BAND
%nonassoc BNOT
%nonassoc CMP
%nonassoc LE GE LT GT
%nonassoc LARR
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS
%nonassoc GET
%nonassoc SET
%left DOT

%start prog
%type <Lang.t> prog
/* %start prog_ctx */
/* %type <Lang.t -> Lang.t> prog_ctx */
%%

prog:
  | exprs EOF { $1 }

/* prog_ctx: */
  /* | exprs_ctx EOF { $1 } */

expr:
  | IDENT { var ~pos:$loc $1 }
  | BOOL { make ~pos:$loc (Bool $1) }
  | INT { make ~pos:$loc (Int $1) }
  | FLOAT { make ~pos:$loc (Float $1) }
  | STRING { make ~pos:$loc (String $1) }
  /* | expr expr { app ~pos:$loc $1 $2 } */
  | FUN pattern ARR expr { fct ~pos:$loc $2 $4 }
  | LPAR expr RPAR { $2 }
  | BEGIN exprs END { $2 }
  | MODULE simple_decl_list END { record ~pos:$loc true $2 }
/*
  | BUILTIN LPAR STRING RPAR { Builtin.get ~pos:(defpos None) $3 }
  | expr DOT IDENT { mk_field $1 $3 }
  | expr LARR expr RARR { mk_bapp "array_get" [$1; $3] }
  | expr PLUS expr { mk_bapp "fadd" [$1; $3] }
  | expr MINUS expr { mk_bapp "fsub" [$1; $3] }
  | UMINUS expr { mk_bapp "fsub" [mk_val (Float 0.); $2] }
  | expr TIMES expr { mk_bapp "fmul" [$1; $3] }
  | expr DIV expr { mk_bapp "fdiv" [$1; $3] }
  | expr LE expr { mk_bapp "fle" [$1; $3] }
  | expr GE expr { mk_bapp "fle" [$3; $1] }
  | expr LT expr { mk_bapp "flt" [$1; $3] }
  | expr GT expr { mk_bapp "flt" [$3; $1] }
  | expr CMP expr { mk_bapp "feq" [$1; $3] }
  | expr BAND expr { mk_bapp "and" [$1; $3] }
  | expr BOR expr { mk_bapp "or" [$1; $3] }
  | BNOT expr { mk_bapp "not" [$2] }
  | REF LPAR expr RPAR { mk (Monadic (Ref $3)) }
  | IDENT_LPAR apps RPAR { mk_app (ident $1) $2 }
  | expr DOT IDENT_LPAR apps RPAR { mk_app (mk_field $1 $3) $4 }
  | UNREF LPAR expr RPAR { mk (Monadic (RefFun $3)) }
  | UNDT LPAR expr RPAR { mk (Monadic (DtFun $3)) }
  | LACC decls RACC { mk (Record (false, $2)) }
  | expr LARR expr RARR SET expr { mk_bapp "array_set" [$1; $3; $6] }
  | FOR IDENT EQ expr TO expr DO expr DONE { mk (For ($2, $4, $6, $8)) }
  | WHILE expr DO exprs DONE { mk (While ($2, $4)) }
  | IF expr THEN exprs elif END { mk (If ($2, $4, $5)) }

elif:
  | { unit () }
  | ELSE exprs { $2 }
  | ELIF exprs THEN exprs elif { mk (If ($2, $4, $5)) }
*/

exprs:
  | expr { $1 }
  | expr exprs { seq ~pos:$loc $1 $2 }
  | decl { letin ~pos:$loc $1 (unit ~pos:$loc ()) }
  | decl exprs { letin ~pos:$loc $1 $2 }
//| INCLUDE LPAR STRING RPAR exprs { (parse_file_ctx $3) $5 }

// An expression context, this is used for includes
/*                                                 
exprs_ctx:
  | { fun e -> e }
  | expr exprs_ctx { fun e -> mk_seq $1 ($2 e) }
  | decl exprs_ctx { fun e -> mk_let $1 ($2 e) }
  | INCLUDE LPAR STRING RPAR exprs_ctx { fun e -> (parse_file_ctx $3) ($5 e) }
*/

simple_decl:
  | IDENT EQ expr { $1, $3 }

simple_decl_list:
  | { [] }
  | simple_decls { $1 }

simple_decls:
  | simple_decl { [$1] }
  | simple_decl COMMA simple_decls { $1::$3 }

decl:
  | simple_decl { let x, v = $1 in PVar x, v }
  | LET pattern EQ expr { $2, $4 }
  | DEF pattern EQ exprs END { $2, $4 }
  | DEF IDENT pattern EQ exprs END { PVar $2, fct ~pos:$loc $3 $5 }

decls:
  | decl decls { $1::$2 }
  | { [] }

pattern:
  | IDENT { PVar $1 }
  | LPAR in_pattern_list RPAR { $2 }

in_pattern_list:
  | { PRecord [] }
  | in_patterns { PRecord $1 }

in_patterns:
  | in_pattern { [$1] }
  | in_pattern COMMA in_patterns { $1::$3 }

in_pattern:
  | IDENT { $1,$1,None }

