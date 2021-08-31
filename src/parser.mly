%{
open Stdlib
open Lang

let letin ?pos (pat,def) body =
  letin ?pos pat def body  
%}

%token DEF LET BEGIN END FUN ARR DOT MONAD WITH
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

%nonassoc WITH
%right ARR
%right BOR
%right BAND
%nonassoc BNOT
%nonassoc CMP
%nonassoc LE GE LT GT
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS
%left DOT

%start prog
%type <Lang.t> prog
(* %start prog_ctx *)
(* %type <Lang.t -> Lang.t> prog_ctx *)
%%

n:
  | NEWLINE { () }
  | { () }

prog:
  | n exprs EOF { $2 }

(* prog_ctx: *)
(* | exprs_ctx EOF { $1 } *)

expr:
  | simple_expr { $1 }
  | simple_expr simple_expr { app ~pos:$loc $1 $2 }
  | FUN pattern ARR n expr { fct ~pos:$loc $2 $5 }

simple_expr:
  | IDENT { var ~pos:$loc $1 }
  | BOOL { make ~pos:$loc (Bool $1) }
  | INT { make ~pos:$loc (Int $1) }
  | FLOAT { make ~pos:$loc (Float $1) }
  | STRING { make ~pos:$loc (String $1) }
  | BEGIN n e = exprs END { e }
  | LPAR expr_list RPAR { tuple ~pos:$loc $2 }
  | LPAR labeled_expr_list RPAR { record ~pos:$loc (List.rev $2) }
  | MODULE n decls = decl_list END { modul ~pos:$loc (List.rev decls) }
  | LPAR expr COMMA labeled_expr_list RPAR { meths $2 (List.rev $4) }
  | LPAR expr COLON typ RPAR { cast ~pos:$loc $2 (T.Bind.eval [] $4) }
  | simple_expr DOT IDENT { field $1 $3 }
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
  | MONAD name = IDENT a = IDENT EQ t = typ WITH fields = simple_expr { make ~pos:$loc (Monad (name, (fun x -> T.Bind.eval [a,x] t), fields)) }

elif:
  | { unit () }
  | ELSE exprs { $2 }
  | ELIF exprs THEN exprs elif { app ~pos:$loc (Builtin.get ~pos:$loc "ite") (tuple ~pos:$loc [$2; ufun ~pos:$loc $4; ufun ~pos:$loc $5]) }

exprs:
  | expr n { $1 }
  | expr NEWLINE exprs { seq ~pos:$loc $1 $3 }
  | decl n { letin ~pos:$loc $1 (unit ~pos:$loc ()) }
  | decl NEWLINE exprs { letin ~pos:$loc $1 $3 }
  (* | INCLUDE STRING NEWLINE exprs { (parse_file_ctx $3) $5 } *)

expr_list:
  | expr { [$1] }
  | expr COMMA expr_list { $1::$3 }

labeled_expr_list:
  | IDENT EQ expr { [$1,$3] }
  | IDENT EQ expr COMMA labeled_expr_list { ($1,$3)::$5 }

(* An expression context, this is used for includes *)
exprs_ctx:
  | { fun e -> e }
  | expr exprs_ctx { fun e -> mk_seq $1 ($2 e) }
  | decl exprs_ctx { fun e -> mk_let $1 ($2 e) }
  (* | INCLUDE LPAR STRING RPAR exprs_ctx { fun e -> (parse_file_ctx $3) ($5 e) } *)

simple_decl:
  | IDENT EQ expr { $1, $3 }
  | DEF record = IDENT DOT field = IDENT EQ e = exprs END { record, meth ~pos:$loc (var ~pos:$loc(record) record) (field,e) }
  | DEF IDENT pattern EQ n exprs END { $2, fct ~pos:$loc $3 $6 }

decl:
  | simple_decl { let x, v = $1 in PVar x, v }
  | LET pattern EQ expr { $2, $4 }
  | DEF pattern EQ n exprs END { $2, $5 }

decl_list:
  | decl NEWLINE decl_list { $1::$3 }
  | { [] }

pattern:
  | IDENT { PVar $1 }
  | LPAR pattern_list RPAR { PTuple $2 }
  | LPAR RPAR { PTuple [] }

pattern_list:
  | pattern { [$1] }
  | pattern COMMA pattern_list { $1::$3 }

typ:
  | IDENT { Type.Bind.of_string $1 }
  | LPAR in_tuple RPAR { Type.Bind.tuple $2 }
  | LPAR in_record RPAR { Type.Bind.record (List.rev $2) }
  | LPAR RPAR { Type.Bind.unit () }
  | typ ARR typ { Type.Bind.arr $1 $3 }

in_tuple:
  | typ { [$1] }
  | typ TIMES in_tuple { $1::$3 }

in_record:
  | l = IDENT COLON t = typ { [l,t] }
  | l = IDENT COLON t = typ COMMA r = in_record { (l,t)::r }
