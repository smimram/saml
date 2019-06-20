%{
  open Stdlib
  open Lang

  let defpos = function
    | Some pos -> pos
    | None -> Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()

  let mk ?pos e =
    let pos = defpos pos in
    make ~pos e

  let mk_val ?pos =
    let pos = defpos pos in
    value ~pos

  let mk_seq ?pos =
    let pos = defpos pos in
    seq ~pos

  let mk_fun ?pos =
    let pos = defpos pos in
    fct ~pos

  let mk_app ?pos =
    let pos = defpos pos in
    app ~pos

  (** A builtin applied to arguments. *)
  let mk_bapp ?pos b args =
    let pos = defpos pos in
    mk_app ~pos (Builtin.get ~pos b) (List.map (fun e -> "", e) args)

  let mk_ident ?pos x =
    mk ?pos (Ident x)

  let mk_let ?pos (x, e) e' =
    let pos = defpos pos in
    letin ~pos x e e'

  let mk_module ?pos decls =
    mk ?pos (Module decls)

  let mk_field ?pos r x =
    mk ?pos (Field (r, x))
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
%start prog_ctx
%type <Lang.t -> Lang.t> prog_ctx
%%

prog:
    | exprs EOF { $1 }

prog_ctx:
    | exprs_ctx EOF { $1 }

expr:
    | IDENT { mk_ident $1 }
    | NOP { mk_val Unit }
    | INT { mk_val (Int $1) }
    | FLOAT { mk_val (Float $1) }
    | BOOL { mk_val (Bool $1) }
    | STRING { mk_val (String $1) }
    | DT { mk (Monadic Dt) }
    | LPAR expr RPAR { $2 }
    | BEGIN exprs END { $2 }
    | MODULE decls END { mk_module $2 }
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
    | GET expr { mk (Monadic (RefGet $2)) }
    | ident SET expr { mk (Monadic (RefSet ($1, $3))) }
    | UNREF LPAR expr RPAR { mk (Monadic (RefFun $3)) }
    | UNDT LPAR expr RPAR { mk (Monadic (DtFun $3)) }
    | LACC decls RACC { mk (Record (false, $2)) }
    | expr LARR expr RARR SET expr { mk_bapp "array_set" [$1; $3; $6] }
    | FOR IDENT EQ expr TO expr DO expr DONE { mk (For ($2, $4, $6, $8)) }
    | WHILE expr DO exprs DONE { mk (While ($2, $4)) }
    | IF expr THEN exprs elif END { mk (If ($2, $4, $5)) }
    | FUN LPAR args RPAR ARR expr { mk_fun $3 $6 }

elif:
    | { unit () }
    | ELSE exprs { $2 }
    | ELIF exprs THEN exprs elif { mk (If ($2, $4, $5)) }

exprs:
    | expr { $1 }
    | expr exprs { mk_seq $1 $2 }
    | decl { mk_let $1 (unit()) }
    | decl exprs { mk_let $1 $2 }
    | INCLUDE LPAR STRING RPAR exprs { (parse_file_ctx $3) $5 }

// An expression context, this is used for includes
exprs_ctx:
    | { fun e -> e }
    | expr exprs_ctx { fun e -> mk_seq $1 ($2 e) }
    | decl exprs_ctx { fun e -> mk_let $1 ($2 e) }
    | INCLUDE LPAR STRING RPAR exprs_ctx { fun e -> (parse_file_ctx $3) ($5 e) }

ident:
    | IDENT { mk_ident $1 }

decl:
    | IDENT EQ expr { $1, $3 }
    | DEF IDENT EQ exprs END { $2, $4 }
    | DEF IDENT_LPAR args RPAR EQ exprs END { $2, mk_fun $3 $6 }
    | MODULE IDENT EQ decls END { $2, mk_module $4 }

decls:
    | decl decls { $1::$2 }
    | { [] }

args:
    | { [] }
    | arg { [$1] }
    | arg COMMA args { $1::$3 }

arg:
    | IDENT { "",($1,None) }
    | IDENT EQ { $1,($1,None) }
    | IDENT EQ expr { $1,($1,Some $3) }

apps:
    | app { [$1] }
    | app COMMA apps { $1::$3 }
    | { [] }

app:
    | expr { "",$1 }
    | IDENT EQ expr { $1, $3 }
    | IDENT EQ { $1, mk_ident $1 }
