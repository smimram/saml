%{
  open Lang
  open Expr
  open Stdlib

  let type_of_string t =
    (* Printf.printf "type_of_string: %s\n%!" t; *)
    match t with
    | "int" -> T.int
    | "float" -> T.float
    | "string" -> T.string
    | "unit" -> T.unit
    | "bool" -> T.bool
    | s -> T.ident s

  let defpos = function
    | Some pos -> pos
    | None -> Parsing.symbol_start_pos (), Parsing.symbol_end_pos ()

  let mk ?pos e =
    let pos = defpos pos in
    E.make ~pos e

  let mk_fun ?pos =
    let pos = defpos pos in
    E.fct ~pos

  let mk_app ?pos =
    let pos = defpos pos in
    E.app ~pos

  let mk_cst ?pos c =
    mk ?pos (Cst c)

  let mk_ident ?pos x =
    mk ?pos (Ident x)

  let mk_let ?pos ?recursive  =
    let pos = defpos pos in
    E.letin ~pos ?recursive

  let mk_seq ?pos =
    let pos = defpos pos in
    E.seq ~pos

  let mk_ref ?pos e =
   mk ?pos (Ref e)

  let mkt ?pos t =
    let pos = defpos pos in
    T.make ~pos t

  let mkt_ident ?pos x =
    let t =
      match x with
        | "int" -> T.Int
        | "float" -> T.Float
        | _ -> assert false
    in
    mkt ?pos t

  let mk_module ?pos decls =
    let r =
      List.may_map
        (function
        | M.Decl (x,e) -> Some (x,e)
        | _ -> None
        ) decls
    in
    mk ?pos (E.Module r)

  let mk_array ?pos a =
    mk ?pos (Array a)
%}

%token LET REC IN FUN ARR DOT
%token MODULE END BUILTIN INCLUDE
%token REF GET SET FOR TO DO DONE
%token CMP LE GE LT GT
%token BAND BOR BNOT
%token IF THEN ELSE
%token STATIC COMPILE WITH TYPE
%token LPAR RPAR LARR RARR
%token SEMICOLON COLON COMMA MAYBE
%token EQ PLUS MINUS TIMES DIV POW
%token EOF
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <string> IDENT
%token <string> STRING
%token <string> VARIANT

%nonassoc IN
%nonassoc ARR
%right SEMICOLON
%nonassoc THEN
%nonassoc ELSE
%right BOR
%right BAND
%nonassoc BNOT
%nonassoc CMP
%nonassoc LE GE LT GT
//%nonassoc LARR
%nonassoc GET
%nonassoc SET
//%nonassoc EQ
//%nonassoc REF
%right DOT
//%left COMMA
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS

%start prog
//%start expr
%type <Lang.Module.t> prog
//%type <Lang.Expr.t> expr
%%

prog:
    | decls EOF { $1 }

decls:
    | decl decls { $1::$2 }
    | INCLUDE STRING decls { (M.parse_file $2)@$3 }
    | { [] }

decl:
    | LET IDENT args EQ expr { M.Decl ($2, mk_fun $3 $5) }
    | LET IDENT EQ expr { M.Decl($2,$4) }
    | LET LPAR RPAR EQ expr { M.Expr (mk (Coerce ($5, T.unit))) }
    | TYPE IDENT EQ typ { M.Type ($2,$4) }
    | TYPE VARIANT { M.Variant ($2,T.unit) }
    | TYPE VARIANT COLON typ { M.Variant ($2,$4) }

ident:
    | IDENT { mk_ident $1 }

arg:
    | IDENT { "",($1,None) }
    | IDENT EQ { $1,($1,None) }
    | IDENT EQ expr { $1,($1,Some $3) }

arg_list:
    | { [] }
    | arg { [$1] }
    | arg COMMA arg_list { $1::$3 }

args:
    | LPAR arg_list RPAR { $2 }

record_elem:
    | expr { "",$1 }
    | IDENT EQ expr { $1,$3 }
    | IDENT EQ { $1,mk_ident $1 }

in_record:
    | { [] }
    | record_elem { [$1] }
    | record_elem COMMA in_record { $1::$3 }

/* We have to hack because (x) cannot be parsed as a unary record: it's a simple_expr */
record:
    | LPAR RPAR { mk (Record []) }
    | LPAR IDENT EQ expr RPAR { mk (Record [$2,$4]) }
    | LPAR IDENT EQ RPAR { mk (Record [$2,mk_ident $2]) }
    | LPAR record_elem COMMA in_record RPAR { mk (Record ($2::$4)) }

app_args:
    | LPAR in_record RPAR { $2 }

array_field:
    | ident LARR expr RARR { $1,$3 }

expr:
    | LET IDENT EQ expr IN expr { mk_let $2 $4 $6 }
    | LET REC IDENT EQ expr IN expr { mk_let ~recursive:true $3 $5 $7 }
    | LET IDENT args EQ expr IN expr { mk_let $2 (mk_fun $3 $5) $7 }
    | FUN args ARR expr { mk_fun $2 $4 }
    | expr SEMICOLON expr { mk_seq (mk (Coerce($1,T.unit))) $3 }
    | IF expr THEN expr ELSE expr { mk_app (mk_cst If) ["",$2; "then",E.quote $4; "else",E.quote $6] }
    | IF expr THEN expr { mk_app (mk_cst If) ["",$2; "then",mk_fun [] $4; "else",mk_fun [] (unit ())] }
    | ident SET expr { mk_app (mk_cst Set) ["",$1; "",$3] }
    | array_field SET expr { let a,i = $1 in mk_app (Builtin.get "array_set") ["",a;"",i;"",$3] }
    | expr PLUS expr { mk_app (Builtin.get "add") ["",$1; "",$3] }
    | expr MINUS expr { mk_app (Builtin.get "sub") ["",$1; "",$3] }
    | MINUS expr %prec UMINUS { mk_app (Builtin.get "sub") ["",mk_cst (Float 0.); "",$2] }
    | expr TIMES expr { mk_app (Builtin.get "mul") ["",$1; "",$3] }
    | expr DIV expr { mk_app (Builtin.get "div") ["",$1; "",$3] }
    | expr LE expr { mk_app (Builtin.get "le") ["",$1; "",$3] }
    | expr GE expr { mk_app (Builtin.get "le") ["",$3; "",$1] }
    | expr LT expr { mk_app (Builtin.get "lt") ["",$1; "",$3] }
    | expr GT expr { mk_app (Builtin.get "lt") ["",$3; "",$1] }
    | expr CMP expr { mk_app (Builtin.get "eq") ["",$1; "",$3] }
    | expr BAND expr { mk_app (Builtin.get "and") ["",$1; "",$3] }
    | expr BOR expr { mk_app (Builtin.get "or") ["",$1; "",$3] }
    | BNOT expr { mk_app (Builtin.get "not") ["",$2] }
    | POW LPAR expr COMMA expr RPAR { mk_app (Builtin.get "pow") ["",$3;"",$5] }
    | FOR IDENT EQ expr TO expr DO expr DONE { mk (For($2,$4,$6,E.quote $8)) }
    | simple_expr app_args { mk_app $1 $2 }
    | REF simple_expr { mk_ref $2 }
    | simple_expr { $1 }

expr_list:
    | { [] }
    | expr { [$1] }
    | expr COMMA expr_list { $1::$3 }

simple_expr:
    | ident { $1 }
    | INT { mk_cst (Int $1) }
    | FLOAT { mk_cst (Float $1) }
    | BOOL { mk_cst (Bool $1) }
    | STRING { mk_cst (String $1) }
    | LPAR expr RPAR { $2 }
    | LPAR expr COLON typ RPAR { mk (Coerce ($2, $4)) }
    | GET simple_expr { mk_app (mk_cst Get) ["",$2] }
    | record { $1 }
    | LPAR ident WITH in_record RPAR { let r = List.map (fun (l,e) -> l,(e,false)) $4 in mk (Replace_fields($2,r)) }
      /* TODO: I'm not so fan of this syntax */
    | LPAR ident WITH MAYBE in_record RPAR { let r = List.map (fun (l,e) -> l,(e,true)) $5 in mk (Replace_fields($2,r)) }
    | LARR expr_list RARR { mk_array $2 }
    | array_field { let a, i = $1 in mk_app (Builtin.get "array_get") ["",a;"",i] }
    | simple_expr DOT IDENT { mk (Field ($1, $3)) }
    | simple_expr DOT { mk (Field ($1, "")) }
    | VARIANT LPAR expr RPAR { mk (Variant($1,$3)) }
    | VARIANT LPAR RPAR { mk (Variant ($1, unit ~pos:(defpos None) ())) }
    | MODULE decls END { mk_module $2 }
    | BUILTIN STRING { Builtin.get ~pos:(defpos None) $2 }
    | COMPILE { Builtin.get "compile" }

/***** Types *****/

typ:
    | IDENT { type_of_string $1 }
    | typ_record ARR typ { T.arr $1 $3 }
    | STATIC typ { T.static $2 }
    | typ_record { T.record $1 }

typ_record:
    | LPAR typ_args RPAR { $2 }

typ_arg:
    | typ { "",($1,false) }
    | IDENT COLON typ { $1,($3,false) }
    | IDENT COLON MAYBE typ { $1,($4,true) }

typ_args:
    | { [] }
    | typ_arg { [$1] }
    | typ_arg COMMA typ_args { $1::$3 }
