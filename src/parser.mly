%{
    open Stdlib
    open Lang

    let letin ~pos (pat,def) body =
      letin ~pos pat def body
%}

%token DEF LET BEGIN END FUN ARR DOT PIPE
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
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <string> IDENT
%token <string> STRING

%right BOR
%right BAND
%nonassoc BNOT
%nonassoc CMP
%nonassoc LE GE LT GT
%nonassoc LARR
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS
%left PIPE

%start prog
%type <Lang.t> prog
/* %start prog_ctx */
/* %type <Lang.t -> Lang.t> prog_ctx */
%%

n:
  | NEWLINE { () }
  | { () }

prog:
  | n exprs EOF { $2 }

/* prog_ctx: */
/* | exprs_ctx EOF { $1 } */

expr:
  | simple_expr { $1 }
  | simple_expr expr { app ~pos:$loc $1 $2 }
  | FUN pattern ARR expr { fct ~pos:$loc $2 $4 }

simple_expr:
  | IDENT { var ~pos:$loc $1 }
  | BOOL { make ~pos:$loc (Bool $1) }
  | INT { make ~pos:$loc (Int $1) }
  | FLOAT { make ~pos:$loc (Float $1) }
  | STRING { make ~pos:$loc (String $1) }
  | BEGIN exprs END { $2 }
  | LPAR simple_expr_list RPAR { tuple ~pos:$loc $2 }
  | LPAR labeled_expr_list RPAR { record ~pos:$loc $2 }
  (* | LPAR expr COMMA labeled_expr_list RPAR { record ~pos:$loc $4 } *)
  (* | MODULE n simple_decl_list END { record ~pos:$loc ~recursive:true $3 } *)
  (* | simple_expr PIPE IDENT { field ~pos:$loc $3 $1 } *)
  | BUILTIN STRING { Builtin.get ~pos:$loc $2 }
  | simple_expr PLUS simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fadd") (pair ~pos:$loc $1 $3) }
  | simple_expr MINUS simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fsub") (pair ~pos:$loc $1 $3) }
  | simple_expr TIMES simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fmul") (pair ~pos:$loc $1 $3) }
  | simple_expr DIV simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fdiv") (pair ~pos:$loc $1 $3) }
  | UMINUS simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fsub") (pair ~pos:$loc (float 0.) $2) }
  | simple_expr LE simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fle") (pair ~pos:$loc $1 $3) }
  | simple_expr GE simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fge") (pair ~pos:$loc $1 $3) }
  | simple_expr LT simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "flt") (pair ~pos:$loc $1 $3) }
  | simple_expr GT simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "fgt") (pair ~pos:$loc $1 $3) }
  | simple_expr CMP simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "feq") (pair ~pos:$loc $1 $3) }
  | simple_expr BAND simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "and") (pair ~pos:$loc $1 $3) }
  | simple_expr BOR simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "or") (pair ~pos:$loc $1 $3) }
  | BNOT simple_expr { app ~pos:$loc (Builtin.get ~pos:$loc "not") $2 }
  | IF expr THEN exprs elif END { app ~pos:$loc (Builtin.get ~pos:$loc "ite") (tuple ~pos:$loc [$2; ufun ~pos:$loc $4; ufun ~pos:$loc $5]) }
  (* | WHILE expr DO exprs DONE { app ~pos:$loc (Builtin.get ~pos:$loc "while") (record ~pos:$loc ["cond",$2; "body", ufun ~pos:$loc $4]) } *)

elif:
  | { unit () }
  | ELSE exprs { $2 }
  | ELIF exprs THEN exprs elif { app ~pos:$loc (Builtin.get ~pos:$loc "ite") (tuple ~pos:$loc [$2; ufun ~pos:$loc $4; ufun ~pos:$loc $5]) }

exprs:
  | expr n { $1 }
  | expr NEWLINE exprs { seq ~pos:$loc $1 $3 }
  | decl n { letin ~pos:$loc $1 (unit ~pos:$loc ()) }
  | decl NEWLINE exprs { letin ~pos:$loc $1 $3 }
  /* | INCLUDE STRING NEWLINE exprs { (parse_file_ctx $3) $5 } */

simple_expr_list:
  | simple_expr { [$1] }
  | simple_expr COMMA simple_expr_list { $1::$3 }


labeled_expr_list:
  | IDENT EQ simple_expr { [$1,$3] }
  | IDENT EQ simple_expr COMMA labeled_expr_list { ($1,$3)::$5 }

// an expression context, this is used for includes
exprs_ctx:
  | { fun e -> e }
  | expr exprs_ctx { fun e -> mk_seq $1 ($2 e) }
  | decl exprs_ctx { fun e -> mk_let $1 ($2 e) }
  /* | INCLUDE LPAR STRING RPAR exprs_ctx { fun e -> (parse_file_ctx $3) ($5 e) } */

simple_decl:
  | IDENT EQ expr { $1, $3 }
  | DEF IDENT pattern EQ n exprs END { $2, fct ~pos:$loc $3 $6 }

decl:
  | simple_decl { let x, v = $1 in PVar x, v }
  | LET pattern EQ expr { $2, $4 }
  | DEF pattern EQ n exprs END { $2, $5 }

decl_list:
  | decl n decl_list { $1::$3 }
  | { [] }

pattern:
  | IDENT { PVar $1 }
  | LPAR pattern_list RPAR { PTuple $2 }
  | LPAR RPAR { PTuple [] }

pattern_list:
  | pattern { [$1] }
  | pattern COMMA pattern_list { $1::$3 }
