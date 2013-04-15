open Stdlib
open Backend

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

let rec emit_type = function
  | T.Int -> "int"
  | T.Float -> "float"
  | T.Unit -> "unit"

let emit_value v =
  match v with
  | V.I n -> Printf.sprintf "(%d)" n
  | V.F f -> Printf.sprintf "(%F)" f
  | V.B b -> Printf.sprintf "%b" b
  | V.S s -> Printf.sprintf "\"%s\"" s

let rec emit_expr prog e =
  (* Printf.printf "B.OCaml.emit_expr: %s\n%!" (string_of_expr e); *)
  let emit_cmds prog cmds = Printf.sprintf "(%s)" (emit_cmds prog cmds) in
  match e with
  | Val v -> emit_value v
  | Var n -> Printf.sprintf "(!%s)" (string_of_var n)
  | Op (op, args) ->
    let args = Array.to_list args in
    let args = List.map (emit_expr prog) args in
    let args = String.concat " " args in
    Printf.sprintf "(%s %s)" (emit_op op) args
  | If (b,t,e) ->
    let b = emit_expr prog b in
    let t = emit_cmds prog t in
    let e =
      match e with
      | [Val V.U] -> ""
      | _ -> " else " ^ emit_cmds prog e
    in
    Printf.sprintf "(if %s then %s%s)" b t e
  | Return e -> emit_expr prog e

and emit_cmds prog cmds =
  String.concat ";\n" (List.map (emit_expr prog) cmds)

(*
  (** Get names for fields of a record of a given type. *)
  let record =
  let n = ref (-1) in
  let r = ref [] in
  fun tr ->
  try
  List.assoc tr !r
  with
  | Not_found ->
  let fields = Array.map (fun
*)

let default_value t =
  Printf.printf "default_value: %s\n%!" (T.to_string t);
  match t with
  | T.Unit -> "()"
  | T.Int -> "0"
  | T.Bool -> "false"
  | T.Float -> "0."
(* | T.Record r -> *)

let emit prog =
  let vars = Array.to_list prog.vars in
  let vars =
    List.may_mapi
      (fun i t ->
        if t = T.Unit then
          None
        else
          Some (Printf.sprintf "let %s = ref %s" (string_of_var i) (default_value t))
      ) vars
  in
  let vars = String.concat "\n" vars in
  let cmds = emit_cmds prog prog.cmds in
  Printf.sprintf "%s\n\nlet () =\n%s\n" vars cmds
