(*
open Stdlib
open Backend

type t =
  {
    (** Currently processed program. *)
    prog : prog;
    (** Already defined types. *)
    types : (T.t * string) list;
  }

let create prog =
  {
    prog;
    types = [];
  }

let rec emit_type c ?(noderef=false) ?(state=false) ?(full=false) t =
  (* Printf.printf "C.emit_type %B: %s\n%!" state (T.to_string t); *)
  match t with
  | T.Int -> c, "int"
  | T.Float -> c, "double"
  | T.Unit -> c, "void"
  | T.Bool -> c, "int"
  | T.Ptr t ->
    let c, t = emit_type c ~noderef ~state ~full t in
    c, t^"*"
  | T.Record r ->
    if full then
      let c, l = emit_type c ~noderef:true t in
      let c = ref c in
      let ans =
        Array.mapi
          (fun i t ->
            if t = T.Unit then "" else
              let c', t = emit_type !c (T.unptr t) in
              c := c';
              Printf.sprintf "%s %s_%d;" t l i
          ) r
      in
      let ans = Array.to_list ans in
      !c, String.concat " " ans
    else
      let c, typ =
        try
          c, List.assoc t c.types
        with
        | Not_found ->
          (* Printf.printf "didn't find type\n%!"; *)
          let l = if state then "state" else Printf.sprintf "type%d" (List.length c.types) in
          let c = { c with types = (t,l)::c.types } in
          c, l
      in
      c, typ

let tab n = String.spaces (2*n)

let rec emit_loc c ~decl ~tabs x =
  match x with
  | LVar x -> c, string_of_var x
  | LField (RVar a,i) ->
    let t = typ c.prog (LVar a) in
    let c, t = emit_type c ~noderef:true (T.unptr t) in
    c, Printf.sprintf "%s->%s_%d" (string_of_var a) t i
  | LField (RState,i) ->
    let t = state_t c.prog in
    let c, t = emit_type c ~noderef:true t in
    c, Printf.sprintf "state->%s_%d" t i
  | LCell (a,i) ->
    let c, i = emit_expr c ~decl ~tabs i in
    c, Printf.sprintf "%s[%s]" (string_of_var a) i

and emit_expr c ~decl ~tabs e =
  (* Printf.printf "C.emit_expr: %s\n%!" (string_of_expr e); *)
  let emit_expr ?(decl=decl) ?(tabs=tabs) = emit_expr ~decl ~tabs in
  let emit_eqs ?(decl=decl) ?(tabs=tabs) = emit_eqs ~decl ~tabs in
  match e with
  | Int n -> c, Printf.sprintf "%d" n
  | Float f -> c, Printf.sprintf "%f" f
  | Bool b -> c, if b then "1" else "0"
  | Var n -> c, Printf.sprintf "%s" (string_of_var n)
  | Arg n -> c, Printf.sprintf "a%d" n
  | Op (op, args) ->
    let c, args =
      let c = ref c in
      let args = Array.map (fun e -> let c', e = emit_expr !c e in c := c'; e) args in
      !c, args
    in
    (
      (* Printf.printf "C.emit_expr op: %s\n%!" (string_of_op op); *)
      match op with
      | Add -> c, Printf.sprintf "(%s + %s)" args.(0) args.(1)
      | Sub -> c, Printf.sprintf "(%s - %s)" args.(0) args.(1)
      | Mul -> c, Printf.sprintf "(%s * %s)" args.(0) args.(1)
      | Div -> c, Printf.sprintf "(%s / %s)" args.(0) args.(1)
      | Eq -> c, Printf.sprintf "(%s == %s)" args.(0) args.(1)
      | Alloc t ->
        let n = if Array.length args = 0 then "1" else args.(0) in
        let c, tv = emit_type c ~noderef:true t in
        let c, t = emit_type c (T.Ptr t) in
        c, Printf.sprintf "(%s)malloc(%s * sizeof(%s))" t n tv
      | Realloc t ->
        assert (Array.length args = 2);
        let n = if Array.length args = 1 then "1" else args.(1) in
        let c, tv = emit_type c ~noderef:true t in
        let c, t = emit_type c (T.Ptr t) in
        c, Printf.sprintf "(%s)realloc(%s, %s * sizeof(%s))" args.(0) t n tv
      | External ext -> c, ext.ext_c args
    )
  | Return x ->
    c, if typ c.prog (LVar x) = T.Unit then "" else Printf.sprintf "return %s" (string_of_var x)
  | Field (x, i) ->
    let t = typ_rvar c.prog x in
    let x =
      match x with
      | RVar x -> string_of_var x
      | RState -> "state"
    in
    let c, t = emit_type c ~noderef:true (T.unptr t) in
    c, Printf.sprintf "%s->%s_%d" x t i
  | Cell (x, i) ->
    let c, e = emit_expr c (Var x) in
    let c, i = emit_expr c i in
    c, Printf.sprintf "%s[%s]" e i
  | If (b,t,e) ->
    let emit_eqs = emit_eqs ~tabs:(tabs+1) in
    let c, b = emit_expr c b in
    let c, t = emit_eqs c t in
    let c, e = emit_eqs c e in
    let tabs = tab tabs in
    c, Printf.sprintf "if (%s) {\n%s\n%s} else {\n%s\n%s}" b t tabs e tabs

and emit_eq c ~decl ~tabs (x,expr) =
  let c, e = emit_expr ~decl ~tabs c expr in
  if typ c.prog x = T.Unit then
    (
      match expr with
      | Var _ | Field _ -> (c, decl), ""
      | _ -> (c, decl), Printf.sprintf "%s%s;" (tab tabs) e
    )
  else
    let c, decl, t =
      match x with
      | LVar x ->
        let t = typ c.prog (LVar x) in
        if List.mem x decl then
          c, decl, ""
        else
          let decl = x::decl in
          (* let deref = deref t in *)
          let c, t = emit_type c t in
          c, decl, (t^" ")
      | LCell _
      | LField _ ->
        c, decl, ""
    in
    let c, l = emit_loc c ~decl ~tabs x in
    (c, decl), Printf.sprintf "%s%s%s = %s;" (tab tabs) t l e

(* TODO: decl should be replaced by FV.written because of if, etc. *)
and emit_eqs c ?(decl=[]) ?(tabs=0) eqs =
  let (c,decl), eqs = List.fold_map (fun (c,decl) -> emit_eq c ~decl ~tabs) (c,decl) eqs in
  let eqs = List.filter (fun s -> s <> "") eqs in
  c, String.concat "\n" eqs

let emit_proc c (name,p) =
  let args = p.proc_args in
  let c =
    match p.proc_state with
    | Some t ->
      (* We emit the state first so that we know its name. *)
      let c, _ = emit_type c ~state:true t in
      c
    | None -> c
  in
  let c, args =
    let i = ref (-1) in
    let c = ref c in
    let a =
      List.map
        (fun t ->
          Printf.sprintf "%s a%d"
            (let c', t = emit_type !c t in c := c'; t)
            (incr i; !i)
        ) args
    in
    !c, a
  in
  let c, args =
    match p.proc_state with
    | Some t ->
      (* We emit the state first so that we know its name. *)
      let c, t = emit_type c ~state:true (T.Ptr t) in
      c, (Printf.sprintf "%s state" t)::args
    | None -> c, args
  in
  let args = String.concat ", " args in
  let c, eqs = emit_eqs c ~tabs:1 p.proc_eqs in
  let c, ret = emit_type c p.proc_ret in
  c,
  Printf.sprintf "inline %s %s(%s) {\n%s\n}"
    ret
    name
    args
    eqs

let emit prog =
  let c = create prog in
  (* TODO: alloc and run should always be handled as usual procs. *)
  let procs = ["run", proc_run prog; "alloc", proc_alloc prog]@prog.procs in
  let c, procs = List.fold_map emit_proc c procs in
  let procs = String.concat "\n\n" procs in
  let c, types =
    let c = ref c in
    let ans =
      String.concat_map "\n\n"
        (fun (t,l) ->
          let c', t = emit_type !c ~full:true t in
          c := c';
          Printf.sprintf "typedef struct { %s } %s;" t l
        ) (!c).types
    in
    !c, ans
  in
  types ^ "\n\n" ^ procs
*)


open Stdlib
open Backend

type t =
  {
    prog : prog; (** The program. *)
    mutable records : (T.t array * string) list; (** Types for records. *)
  }

let rec record_type_name prog t =
  try
    List.assoc t prog.records
  with
  | Not_found ->
    let name = Printf.sprintf "rec%d" (List.length prog.records) in
    prog.records <- (t,name)::prog.records;
    record_type_name prog t

let record_field prog t =
  let name = record_type_name prog t in
  Printf.sprintf "%s_%d" name

let rec default_value prog t =
  (* Printf.printf "default_value: %s\n%!" (T.to_string t); *)
  match t with
  | T.Int -> "0"
  | T.Bool -> "0"
  | T.Float -> "0."
  | T.Record r ->
    let f = record_field prog r in
    let r =
      List.init (Array.length r) (fun i ->
        let v = default_value prog r.(i) in
        Printf.sprintf "%s = %s;" (f i) v)
    in
    Printf.sprintf "{ %s }" (String.concat " " r)
  | T.Array _ -> "[||]"

let rec emit_type prog = function
  | T.Int -> "int"
  | T.Float -> "double"
  | T.Unit -> "unit"
  | T.Record r -> record_type_name prog r

let emit_value v =
  match v with
  | V.I n -> Printf.sprintf "(%d)" n
  | V.F f -> Printf.sprintf "(%F)" f
  | V.B b -> Printf.sprintf "%b" b
  | V.S s -> Printf.sprintf "\"%s\"" s

let rec emit_expr prog e =
  Printf.printf "B.OCaml.emit_expr: %s\n%!" (string_of_expr e);
  let emit_type = emit_type prog in
  let emit_expr = emit_expr prog in
  let emit_cmds cmds = Printf.sprintf "{ %s }" (emit_cmds prog cmds) in
  match e with
  | Val v -> emit_value v
  | Var n -> Printf.sprintf "%s" (string_of_var n)
  | Field (t,e,n) -> Printf.sprintf "%s->%s" (emit_expr e) (record_field prog t n)
  | Cell (e,n) -> Printf.sprintf "%s[%s]" (emit_expr e) (emit_expr n)
  | Op (o, a) ->
    (
      match o with
      | Alloc t ->
        if Array.length a > 0 then
          Printf.sprintf "malloc(%s*sizeof(%s))" (emit_expr a.(0)) (emit_type t)
        else
          default_value prog t
      | Get ->
        (
          match a.(0) with
          | Var n -> Printf.sprintf "%s" (string_of_var n)
          | Field _ | Cell _ -> (emit_expr a.(0))
        )
      | Set ->
        if a.(1) = Val V.Z then "" else
          (
            match a.(0) with
            | Var n -> Printf.sprintf "%s = %s" (string_of_var n) (emit_expr a.(1))
            | Field(t,e,n) -> Printf.sprintf "%s.%s = %s" (emit_expr e) (record_field prog t n) (emit_expr a.(1))
            | Cell(e,n) -> Printf.sprintf "%s[%s] = %s" (emit_expr e) (emit_expr n) (emit_expr a.(1))
          )
      | Record t ->
        assert (Array.length t = Array.length a);
        let rf = record_field prog t in
        let r = List.init (Array.length a) (fun i -> Printf.sprintf "%s = %s;" (rf i) (emit_expr a.(i))) in
        let r = String.concat " " r in
        Printf.sprintf "{ %s }" r
      | _ ->
        let a = Array.map emit_expr a in
        match o with
        | Eq -> Printf.sprintf "(%s == %s)" a.(0) a.(1)
        | Add -> Printf.sprintf "(%s + %s)" a.(0) a.(1)
        | Sub -> Printf.sprintf "(%s - %s)" a.(0) a.(1)
        | Mul -> Printf.sprintf "(%s * %s)" a.(0) a.(1)
        | Div -> Printf.sprintf "(%s / %s)" a.(0) a.(1)
        | Sin -> Printf.sprintf "sin(%s)" a.(0)
        | Cos -> Printf.sprintf "cos(%s)" a.(0)
        | Pi -> Printf.sprintf "PI"
        | External ext -> ext.ext_c a
    )
  | If (b,t,e) ->
    let b = emit_expr b in
    let t = emit_cmds t in
    let e =
      match e with
      | [Val V.U] -> ""
      | _ -> " else " ^ emit_cmds e
    in
    Printf.sprintf "if %s then %s%s" b t e
  | While (b,e) -> Printf.sprintf "(while %s do\n%s\ndone)" (emit_expr b) (emit_cmds e)
  | For(i,a,b,e) ->
    let i = string_of_var i in
    Printf.sprintf "(%s := %s;\nwhile !%s <= %s do\n%s;\nincr %s\ndone)" i (emit_expr a) i (emit_expr b) (emit_cmds e) i
  | Return e -> emit_expr e

and emit_cmds prog cmds =
  String.concat ";\n" (List.map (emit_expr prog) cmds)

let emit prog =
  let p =
    {
      prog;
      records = [];
    }
  in
  let vars = Array.to_list prog.vars in
  let vars =
    List.may_mapi
      (fun i t ->
        if t = T.Unit then
          None
        else
          Some (Printf.sprintf "let %s = ref %s" (string_of_var i) (default_value p t))
      ) vars
  in
  let vars = String.concat "\n" vars in
  let cmds = emit_cmds p prog.cmds in
  let recs =
    String.concat_map "\n" (fun (r,n) ->
      let r = Array.to_list r in
      let r = List.mapi (fun i t -> Printf.sprintf "mutable %s_%d : %s;" n i (emit_type p t)) r in
      let r = String.concat " " r in
      Printf.sprintf "type %s = { %s }" n r
    ) p.records
  in
  Printf.sprintf "open Samlrun\n\n%s\n\n%s\n\nlet () =\n%s\n" recs vars cmds
