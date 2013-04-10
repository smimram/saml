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

let rec emit_expr prog e =
  (* Printf.printf "B.OCaml.emit_expr: %s\n%!" (string_of_expr e); *)
  match e with
  | Int n -> Printf.sprintf "(%d)" n
  | Float f -> Printf.sprintf "(%F)" f
  | Bool b -> Printf.sprintf "%b" b
  | String s -> Printf.sprintf "\"%s\"" s
  | Var n -> Printf.sprintf "(!%s)" (string_of_var n)
  | Op (op, args) ->
    let args = Array.to_list args in
    let args = List.map (emit_expr prog) args in
    let args = String.concat " " args in
    Printf.sprintf "(%s %s)" (emit_op op) args
  | If (b,t,e) ->
    let b = emit_expr prog b in
    let emit_eqs prog eqs = "(" ^ String.concat "; " (List.map (emit_eq prog) eqs) ^ ")" in
    let t = emit_eqs prog t in
    let e =
      match e with
      | [_,Unit] -> ""
      | _ -> " else " ^ emit_eqs prog e
    in
    Printf.sprintf "(if %s then %s%s)" b t e
  | Return x -> emit_expr prog (Var x)

and emit_eq prog (x,e) =
  (* if static then Printf.sprintf "let %s = %s in" (string_of_var x) (emit_expr prog e) else *)
  if typ prog x = T.Unit then
    Printf.sprintf "%s" (emit_expr prog e)
  else
    Printf.sprintf "%s := %s" (string_of_loc x) (emit_expr prog e)

and emit_eqs prog eqs =
  String.concat ";\n" (List.map (emit_eq prog) eqs)

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
          Some (Printf.sprintf "let %s = ref %s in" (string_of_var i) (default_value t))
      ) vars
  in
  let vars = String.concat "\n" vars in
  let init = Printf.sprintf "let init () =\n%s\nin" (emit_eqs prog prog.init) in
  let loop =  Printf.sprintf "let loop () =\n%s\nin" (emit_eqs prog prog.loop) in
  Printf.sprintf "let program () =\n\n%s\n\n%s\n\n%s\n\nlet first = ref true in\nfun () -> if !first then (first := false; init ()) else loop()" vars init loop
