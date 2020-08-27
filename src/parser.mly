%{
    open Stdlib
    open Lang

    let letin ~pos (pat,def) body =
      letin ~pos pat def body
%}

%token DEF LET BEGIN END FUN ARR DOT PIPE BANG
%token STREAM DT
%token MODULE BUILTIN INCLUDE
%token FOR WHILE TO DO DONE
%token CMP LE GE LT GT
%token BAND BOR BNOT
%token IF THEN ELSE ELIF
%token LPAR RPAR LARR RARR LACC RACC
%token SEMICOLON COLON COMMA
%token EQ PLUS MINUS UMINUS TIMES DIV POW
%token EOF
%token NEWLINE
%token NULL
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <string> IDENT IDENT_LPAR
%token <string> STRING

%nonassoc ARR
%right NEWLINE SEMICOLON
%right BOR
%right BAND
%nonassoc BNOT
%nonassoc EQ LT LE GT GE
%left PLUS MINUS
%left TIMES DIV
%left PIPE
%nonassoc BANG
%nonassoc LPAR

%start prog
%type <Lang.t> prog
%%

prog:
  | nexpr EOF { $1 }

expr:
  | IDENT { var ~pos:$loc $1 }
  | FLOAT { make ~pos:$loc (Float $1) }
  | BOOL { make ~pos:$loc (Bool $1) }
  | BUILTIN LPAR STRING RPAR { Builtin.get ~pos:$loc $3 }
  | FUN LPAR def_args RPAR ARR n expr { fct ~pos:$loc $3 $7 }
  | expr LPAR args RPAR { app ~pos:$loc $1 $3 }
  | expr PLUS expr { appnl ~pos:$loc (Builtin.get ~pos:$loc($2) "fadd") [$1; $3] }
  | expr MINUS expr { appnl ~pos:$loc (Builtin.get ~pos:$loc($2) "fsub") [$1; $3] }
  | expr TIMES expr { appnl ~pos:$loc (Builtin.get ~pos:$loc($2) "fmul") [$1; $3] }
  | expr BAND expr { appnl ~pos:$loc (Builtin.get ~pos:$loc "and") [$1; $3] }
  | expr BOR expr { appnl ~pos:$loc (Builtin.get ~pos:$loc "or") [$1; $3] }
  | BNOT expr { appnl ~pos:$loc (Builtin.get ~pos:$loc "not") [$2] }
  | expr LE expr { appnl ~pos:$loc (Builtin.get ~pos:$loc "fle") [$1; $3] }
  | expr GE expr { appnl ~pos:$loc (Builtin.get ~pos:$loc "fge") [$1; $3] }
  | expr LT expr { appnl ~pos:$loc (Builtin.get ~pos:$loc "flt") [$1; $3] }
  | expr GT expr { appnl ~pos:$loc (Builtin.get ~pos:$loc "fgt") [$1; $3] }
  /* | expr CMP expr { appnl ~pos:$loc (Builtin.get ~pos:$loc "feq") [$1; $3] } */
  | expr NEWLINE expr { seq ~pos:$loc $1 $3 }
  | expr SEMICOLON expr { seq ~pos:$loc $1 $3 }
  | decl NEWLINE expr { letin ~pos:$loc($1) $1 $3 }
  | IF expr THEN expr elif END { app ~pos:$loc (Builtin.get ~pos:$loc "ite") ["if",$2; "then", fct ~pos:$loc [] $4; "else", fct ~pos:$loc [] $5] }
  | BEGIN nexpr END { $2 }
  | NULL { null ~pos:$loc () }
  | STREAM LPAR def_args RPAR ARR n expr { fct ~pos:$loc ($3) (fct ~pos:$loc [dtv,(dtv,None)] $7) }
  | STREAM ARR n expr { fct ~pos:$loc [dtv,(dtv,None)] $4 }
  | DT { var ~pos:$loc dtv }
  | LPAR l = tuple RPAR { if List.length l = 1 then List.hd l else tuple ~pos:$loc l }
  | expr PIPE expr { make ~pos:$loc (Stream_bind ($1, $3)) }
  | BANG expr { make ~pos:$loc (Stream_get $2) }

elif:
  | { unit () }
  | ELSE expr { $2 }
  | ELIF expr THEN expr elif { app ~pos:$loc (Builtin.get ~pos:$loc "ite") ["if",$2; "then", fct ~pos:$loc [] $4; "else", fct ~pos:$loc [] $5] }

n:
  | NEWLINE { () }
  | { () }

eqn:
  | EQ { () }
  | NEWLINE { () }

eq:
  | EQ { () }
  | { () }

nexpr:
  | n expr { $2 }

decl:
  | IDENT EQ expr { $1, $3 }
  | DEF IDENT eqn nexpr END { $2, $4 }
  | DEF IDENT LPAR def_args RPAR eq nexpr END { $2, fct ~pos:$loc $4 $7 }

arg:
  | expr { "", $1 }
  | IDENT EQ expr { $1, $3 }

args:
  | arg COMMA args { $1::$3 }
  | arg { [$1] }
  | { [] }

def_arg:
  | IDENT { "",($1,None) }
  | IDENT EQ { $1,($1,None) }
  | IDENT EQ expr { $1,($1,Some $3) }

def_args:
  | def_arg COMMA def_args { $1::$3 }
  | def_arg { [$1] }
  | { [] }

tuple:
  | expr COMMA tuple { $1::$3 }
  | expr { [$1] }
  | { [] }






/* prog_ctx: */
/* | exprs_ctx EOF { $1 } */

/* expr: */
  /* | simple_expr { $1 } */
  /* | simple_expr expr { app ~pos:$loc $1 $2 } */
  /* | FUN args ARR expr { fct ~pos:$loc $2 $4 } */

/* simple_expr: */
  /* | IDENT { var ~pos:$loc $1 } */
  /* | BOOL { make ~pos:$loc (Bool $1) } */
  /* | INT { make ~pos:$loc (Int $1) } */
  /* | FLOAT { make ~pos:$loc (Float $1) } */
  /* | STRING { make ~pos:$loc (String $1) } */
  /* | LPAR expr RPAR { $2 } */
  /* | BEGIN exprs END { $2 } */
  /* | LPAR simple_decl_list RPAR { record ~pos:$loc $2 } */
  /* | MODULE n simple_decl_list END { record ~pos:$loc ~recursive:true $3 } */
  /* | simple_expr PIPE IDENT { field ~pos:$loc $3 $1 } */
  /* | BUILTIN STRING { Builtin.get ~pos:$loc $2 } */
  /* | simple_expr PLUS simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fadd") (pair ~pos:$loc $1 $3) } */
  /* | simple_expr MINUS simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fsub") (pair ~pos:$loc $1 $3) } */
  /* | simple_expr TIMES simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fmul") (pair ~pos:$loc $1 $3) } */
  /* | simple_expr DIV simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fdiv") (pair ~pos:$loc $1 $3) } */
  /* | UMINUS simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fsub") (pair ~pos:$loc (float 0.) $2) } */
  /* | IF expr THEN exprs elif END { app ~pos:$loc (Builtin.get ~pos:$loc "ite") (record ~pos:$loc ["if",$2; "then", ufun ~pos:$loc $4; "else", ufun ~pos:$loc $5]) } */
  /* | WHILE expr DO exprs DONE { app ~pos:$loc (Builtin.get ~pos:$loc "while") (record ~pos:$loc ["cond",$2; "body", ufun ~pos:$loc $4]) } */

/*
elif:
  | { unit () }
  | ELSE exprs { $2 }
  | ELIF exprs THEN exprs elif { app ~pos:$loc (Builtin.get ~pos:$loc "ite") (record ~pos:$loc ["if",$2; "then", ufun ~pos:$loc $4; "else", ufun ~pos:$loc $5]) }
*/

/* exprs: */
  /* | expr n { $1 } */
  /* | expr NEWLINE exprs { seq ~pos:$loc $1 $3 } */
  /* | decl n { letin ~pos:$loc $1 (unit ~pos:$loc ()) } */
  /* | decl NEWLINE exprs { letin ~pos:$loc $1 $3 } */
  /* | INCLUDE STRING NEWLINE exprs { (parse_file_ctx $3) $5 } */

// An expression context, this is used for includes
/* exprs_ctx: */
  /* | { fun e -> e } */
  /* | expr exprs_ctx { fun e -> mk_seq $1 ($2 e) } */
  /* | decl exprs_ctx { fun e -> mk_let $1 ($2 e) } */
  /* | INCLUDE LPAR STRING RPAR exprs_ctx { fun e -> (parse_file_ctx $3) ($5 e) } */

/* simple_decl: */
  /* | IDENT EQ expr { $1, $3 } */
  /* | DEF IDENT LPAR args RPAR EQ n exprs END { $2, fct ~pos:$loc $3 $6 } */

/* simple_decl_list: */
  /* | { [] } */
  /* | simple_decls { $1 } */

/* simple_decls: */
  /* | simple_decl n { [$1] } */
  /* | simple_decl COMMA simple_decls { $1::$3 } */
  /* | simple_decl NEWLINE simple_decls { $1::$3 } */

/* decl: */
  /* | simple_decl { let x, v = $1 in PVar x, v } */
  /* | LET IDENT EQ expr { $2, $4 } */
  /* | DEF IDENT EQ n exprs END { $2, $5 } */

/* decl_list: */
  /* | decl n decl_list { $1::$3 } */
  /* | { [] } */

/* args: */
  /* | args_list { $1 } */
  /* | { [] } */

/* args_list: */
  /* | IDENT COMMA args_list { $1::$3 } */
  /* | IDENT { [$1] } */
