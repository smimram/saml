(** OCaml backend. *)

open Stdlib
open Backend

type t =
  {
    prog : prog; (** The program. *)
    mutable records : (T.t array * string) list; (** OCaml types for records. *)
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
  | T.Unit -> "()"
  | T.Int -> "0"
  | T.Bool -> "false"
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

let emit_op = function
  | Add -> "( +. )"
  | Sub -> "( -. )"
  | Mul -> "( *. )"
  | Div -> "( /. )"
  | Sin -> "sin"
  | Pi -> "(4. *. atan 1.)"
  | Le -> "( <= )"
  | Lt -> "( < )"
  | Eq -> "( = )"
  | Exp -> "exp"
  | Print t ->
    (
      match t with
      | T.Float -> "Printf.printf \"%F\\n%!\""
      | T.Int -> "Printf.printf \"%d\n%!\""
      | T.String -> "Printf.printf \"%s%!\""
    )
  | External ext -> ext.ext_ocaml ()
  | op -> failwith (Printf.sprintf "TODO: OCaml.emit_op for %s." (string_of_op op))

let rec emit_type prog = function
  | T.Int -> "int"
  | T.Float -> "float"
  | T.Unit -> "unit"
  | T.Record r -> record_type_name prog r

let emit_value v =
  match v with
  | V.I n -> Printf.sprintf "(%d)" n
  | V.F f -> Printf.sprintf "(%F)" f
  | V.B b -> Printf.sprintf "%b" b
  | V.S s -> Printf.sprintf "\"%s\"" s

let rec emit_expr prog e =
  (* Printf.printf "B.OCaml.emit_expr: %s\n%!" (string_of_expr e); *)
  let emit_expr = emit_expr prog in
  let emit_cmds cmds = Printf.sprintf "(%s)" (emit_cmds prog cmds) in
  match e with
  | Val v -> emit_value v
  | Var n -> Printf.sprintf "(!%s)" (string_of_var n)
  | Field (t,e,n) -> Printf.sprintf "%s.%s" (emit_expr e) (record_field prog t n)
  | Cell (e,n) -> Printf.sprintf "%s.(%s)" (emit_expr e) (emit_expr n)
  | Op (Alloc t, a) ->
    if Array.length a > 0 then
      Printf.sprintf "(Array.make %s %s)" (emit_expr a.(0)) (default_value prog t)
    else
      Printf.sprintf "(%s)" (default_value prog t)
  | Op (Get,a) ->
    (
      match a.(0) with
      | Var n -> Printf.sprintf "(!%s)" (string_of_var n)
      | Field _ | Cell _ -> (emit_expr a.(0))
    )
  | Op (Set,a) ->
    if a.(1) = Val V.Z then "()" else
      (
        match a.(0) with
        | Var n -> Printf.sprintf "(%s := %s)" (string_of_var n) (emit_expr a.(1))
        | Field(t,e,n) -> Printf.sprintf "(%s.%s <- %s)" (emit_expr e) (record_field prog t n) (emit_expr a.(1))
        | Cell(e,n) -> Printf.sprintf "(%s.(%s) <- %s)" (emit_expr e) (emit_expr n) (emit_expr a.(1))
      )
  | Op (Record t, a) ->
    assert (Array.length t = Array.length a);
    let rf = record_field prog t in
    let r = List.init (Array.length a) (fun i -> Printf.sprintf "%s = %s;" (rf i) (emit_expr a.(i))) in
    let r = String.concat " " r in
    Printf.sprintf "{ %s }" r
  | Op (op, args) ->
    let args = Array.to_list args in
    let args = List.map emit_expr args in
    let args = String.concat " " args in
    Printf.sprintf "(%s %s)" (emit_op op) args
  | If (b,t,e) ->
    let b = emit_expr b in
    let t = emit_cmds t in
    let e =
      match e with
      | [Val V.U] -> ""
      | _ -> " else " ^ emit_cmds e
    in
    Printf.sprintf "(if %s then %s%s)" b t e
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
