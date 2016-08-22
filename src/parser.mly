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
    let pos = defpos pos in
    mk ~pos (Module decls)
%}

%token DEF BEGIN END FUN ARR DOT
%token MODULE BUILTIN INCLUDE
%token REF GET SET UNREF DT UNDT
%token FOR WHILE TO DO DONE
%token CMP LE GE LT GT
%token BAND BOR BNOT
%token IF THEN ELSE
%token LPAR RPAR LARR RARR LACC RACC
%token SEMICOLON COLON COMMA MAYBE
%token EQ PLUS MINUS TIMES DIV POW
%token EXPAND
%token EOF
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <string> IDENT
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
%nonassoc GET
%nonassoc SET
%right DOT
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS

%start prog
%type <Lang.t> prog
%start prog_ctx
%type <Lang.t -> Lang.t> prog_ctx
%%

prog:
    | expr EOF { $1 }

prog_ctx:
    | expr_ctx EOF { $1 }

// A very simple expression
vsexpr:
    | IDENT { mk_ident $1 }
    | INT { mk_val (Int $1) }
    | FLOAT { mk_val (Float $1) }
    | BOOL { mk_val (Bool $1) }
    | STRING { mk_val (String $1) }
    | DT { mk (Monadic Dt) }
    | BEGIN expr END { $2 }
    | MODULE decls END { mk_module $2 }
    | BUILTIN LPAR STRING RPAR { Builtin.get ~pos:(defpos None) $3 }
    | sexpr DOT IDENT { mk (Field ($1, $3)) }

ident:
    | IDENT { mk_ident $1 }

// A simple expression
sexpr:
    | vsexpr { $1 }
    | sexpr PLUS sexpr { mk_bapp "fadd" [$1; $3] }
    | sexpr MINUS sexpr { mk_bapp "fsub" [$1; $3] }
  //| MINUS sexpr %prec UMINUS { mk_bapp "fsub" [mk_val (Float 0.); $2] }
    | sexpr TIMES sexpr { mk_bapp "fmul" [$1; $3] }
    | sexpr DIV sexpr { mk_bapp "fdiv" [$1; $3] }
    | sexpr LE sexpr { mk_bapp "le" [$1; $3] }
    | sexpr GE sexpr { mk_bapp "le" [$3; $1] }
    | sexpr LT sexpr { mk_bapp "lt" [$1; $3] }
    | sexpr GT sexpr { mk_bapp "lt" [$3; $1] }
    | sexpr CMP sexpr { mk_bapp "eq" [$1; $3] }
    | sexpr BAND sexpr { mk_bapp "and" [$1; $3] }
    | sexpr BOR sexpr { mk_bapp "or" [$1; $3] }
    | BNOT sexpr { mk_bapp "not" [$2] }
    | vsexpr app_args { mk_app $1 $2 }
    | REF LPAR sexpr RPAR { mk (Monadic (Ref $3)) }
    | GET ident { mk (Monadic (RefGet $2)) }
    | ident SET sexpr { mk (Monadic (RefSet ($1, $3))) }
    | UNREF LPAR sexpr RPAR { mk (Monadic (RefFun $3)) }
    | UNDT LPAR sexpr RPAR { mk (Monadic (DtFun $3)) }
    | LACC decls RACC { mk (Record (false, $2)) }

// A simple expression with parenthesis
psexpr:
    | sexpr { $1 }
    | LPAR psexpr RPAR { $2 }

expr:
    | sexpr { $1 }
    | sexpr expr { mk_seq $1 $2 }
    | decl { mk_let $1 (unit ()) }
    | decl expr { mk_let $1 $2 }
    | INCLUDE LPAR STRING RPAR expr { (parse_file_ctx $3) $5 }

// An expression context, this is used for includes
expr_ctx:
    | { fun e -> e }
    | sexpr expr_ctx { fun e -> mk_seq $1 ($2 e) }
    | decl expr_ctx { fun e -> mk_let $1 ($2 e) }
    | INCLUDE LPAR STRING RPAR expr_ctx { fun e -> (parse_file_ctx $3) ($5 e) }

decl:
    | IDENT EQ sexpr { $1, $3 }
    | DEF IDENT args EQ expr END { $2, mk_fun $3 $5 }
    | MODULE IDENT EQ decls END { $2, mk_module $4 }

decls:
    | decl decls { $1::$2 }
    | { [] }

args:
    | LPAR arg_list RPAR { $2 }

arg_list:
    | { [] }
    | arg { [$1] }
    | arg COMMA arg_list { $1::$3 }

arg:
    | IDENT { "",($1,None) }
    | IDENT EQ { $1,($1,None) }
    | IDENT EQ sexpr { $1,($1,Some $3) }

app_args:
    | LPAR in_app_args RPAR { $2 }

app_arg:
    | sexpr { "",$1 }
    | IDENT EQ sexpr { $1, $3 }
    | IDENT EQ { $1, mk_ident $1 }

in_app_args:
    | app_arg { [$1] }
    | app_arg COMMA in_app_args { $1::$3 }
