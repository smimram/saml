open Llvm

type context =
  {
    context : llcontext;
    builder : llbuilder;
    modul : llmodule;
    mutable env : (string * llvalue) list;
  }

let create () =
  let context = global_context () in
  {
    context = context;
    builder = builder context;
    modul = create_module context "SAML";
    env = [];
  }

let typ c = function
  | TInt -> i64_type c.context
  | TFloat -> float_type c.context
  | TVoid -> void_type c.context

let rec emit_expr ?(deref=true) c e =
  match e with
  | Int n -> const_int (typ c TInt) n
  | Float f -> const_float (typ c TFloat) f
  | Ident x ->
    let v = List.assoc x c.env in
    (* TODO: it would be better to emit Loads... *)
    if deref && classify_type (type_of v) = TypeKind.Pointer then
      build_load v "loadtmp" c.builder
    else
      v
  | Op (o, a) ->
    let a =
      if o = Store then
        [|emit_prog ~deref:false c a.(0); emit_prog c a.(1)|]
      else
        Array.map (emit_prog c) a
    in
    (
      match o with
      | FAdd -> build_fadd a.(0) a.(1) "addtmp" c.builder
      | FMul -> build_fmul a.(0) a.(1) "multmp" c.builder
      (* | Alloc (x, t) -> *)
      (* let v = build_alloca (typ c t) "alloctmp" c.builder in *)
      (* c.env <- (x,v)::c.env; *)
      (* v *)
      | Store -> build_store a.(1) a.(0) c.builder
      | Call f ->
        let f =
          match lookup_function f c.modul with
          | Some f -> f
          | None -> assert false
        (* raise (Error "unknown function referenced") *)
        in
        let params = params f in
        if Array.length params <> Array.length a then assert false;
        (* raise (Error "incorrect # arguments passed"); *)
        build_call f a "calltmp" c.builder
    )

and emit_prog ?(deref=true) c p =
  (* Printf.printf "emit_prog: %s\n%!" (to_string p); *)
  match p with
  | [e] ->
    emit_expr ~deref c e
  | e::p ->
    ignore (emit_expr ~deref c e);
    emit_prog ~deref c p
  | [] -> assert false

let emit_proto c (name,args,ret) =
  let targs = Array.map (fun (_,t) -> typ c t) args in
  let ret = typ c ret in
  let ft = function_type ret targs in
  let f = declare_function name ft c.modul in
  Array.iteri
    (fun i a ->
      let n = fst args.(i) in
      set_value_name n a;
      c.env <- (n,a) :: c.env
    ) (params f);
  f

let emit_decl c = function
  | Decl (proto, body) ->
    (* Create a new basic block to start insertion into. *)
    let the_function = emit_proto c proto in
    let bb = append_block c.context "entry" the_function in
    position_at_end bb c.builder;
    (
      try
        let ret_val = emit_prog c body in
        (* Finish off the function. *)
        if thd3 proto = TVoid then
          ignore (build_ret_void c.builder)
        else
          ignore (build_ret ret_val c.builder);
        (* Validate the generated code, checking for consistency. *)
        Llvm_analysis.assert_valid_function the_function;
      with e ->
        delete_function the_function;
        raise e
    )
  | External proto ->
    ignore (emit_proto c proto)

let emit m =
  let c = create () in
  List.iter (emit_decl c) m;
  c.modul

let with_emit f m =
  let m = emit m in
  let ans = f m in
  dispose_module m;
  ans

let dump m =
  with_emit dump_module m

let write m fname =
  with_emit (fun m -> assert (Llvm_bitwriter.write_bitcode_file m fname)) m
