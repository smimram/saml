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
