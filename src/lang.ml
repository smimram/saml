(** Internal representation of the language and operations to manipulate it
    (typechecking, reduction, etc.). *)

open Common
open Stdlib

module T = Type

(** Expressions. *)
module Expr = struct
  (** Special identifiers. *)
  module Ident = struct
    type t = string

    (** Prefix for special variables, also called meta-variables (prefixed
        variables are guaranteed not to occur in saml files). *)
    (* let prefix = "#" *)

    (** Is a variable a meta-variable? *)
    (* let is_meta x = x.[0] = '#' *)

    (* let numbered s = *)
      (* let n = ref (-1) in *)
      (* fun () -> incr n; prefix ^ s ^ string_of_int !n *)

    (** Dt meta-variable. *)
    let dt = "#dt"

    (** Boolean meta-variable indicating whether we are on first round. *)
    let init = "#init"

    (** Meta-variable for state record. *)
    let state = "#state"
  end

  (** A value. *)
  type value =
    | Int of int
    | Float of float
    | Bool of bool
    | String of string

  (** An expression. *)
  type t =
    {
      desc : desc; (** The expression. *)
      pos : pos; (** Position in source file. *)
    }
   (** Contents of an expression. *)
   and desc =
     | Value of value (** A value. *)
     | Ident of Ident.t (** A variable. *)
     | Fun of (string * (string * t option)) list * t
     (** A function. Arguments are labelled (or not if the label is ""), have a
      variable, and optionally a default value. *)
     | Decl of string * t (** A variable declaration (i.e. a let). *)
     | App of t * (string * t) list
     | Seq of t list
     | External of extern
     | Module of (string * t) list
     (** Modules are basically the same as records except that members can use
      previously defined values, e.g. \{ a = 5; b = 2*a \}. *)
     (* | Field of t * string *)
     (* | For of string * t * t * t *)
     (* | While of t * t *)
     (* | If of t * t * t *)
     | Alloc of T.t (** Dynamically allocate a value. *)
     | Monadic of monadic (** A monadic operation. *)
   (** Monadic operations. *)
   and monadic =
     | Dt
     | Ref of t (** A static reference. *)
     | RefGet of string (** Retrieve the value of a reference. *)
     | RefSet of string * t (** Set the value of a reference. *)
     | Expand of t (** Expand the monad implementation. *)
   (** External values. *)
   and extern =
     {
       ext_name : string; (** Name of the external as useable in scripts. *)
       ext_type : T.t; (** Type given the type of its arguments. *)
       (* The mutable is to be able to fill in when there is no reduction. It
       should not be mutated otherwise. *)
       mutable ext_reduce : (string * t) list -> t; (** Reduction. *)
       ext_exec : (string * t) list -> t; (** Execution. *)
     }

  (** Create an expression. *)
  let make ?(pos=dummy_pos) e =
    {
      desc = e;
      pos = pos;
    }

  let value ?pos v =
    make ?pos (Value v)

  let fct ?pos args e =
    make ?pos (Fun (args, e))

  let app ?pos e l =
    make ?pos (App (e, l))

  let seq ?pos ee =
    make ?pos (Seq ee)

  let decl ?pos x e =
    make ?pos (Decl (x, e))

  (** String representation of an expression. *)
  let to_string e =
    let pa p s = if p then Printf.sprintf "(%s)" s else s in
    let rec to_string ~tab p e =
      let tabs ?(tab=tab) () = String.make (2*tab) ' ' in
      let tabss () = tabs ~tab:(tab+1) () in
      match e.desc with
      | Ident x -> x
      | Value (Int n) -> string_of_int n
      | Value (Float f) -> string_of_float f
      | Value (Bool b) -> string_of_bool b
      | Value (String s) -> Printf.sprintf "%S" s
      | Fun (a, e) ->
         let a =
           String.concat_map
             ", "
             (fun (l,(x,d)) ->
               let l = if l = "" || l = x then "" else l ^ ":" in
               let d = match d with None -> "" | Some d -> "=" ^ to_string ~tab:(tab+1) false d in
               Printf.sprintf "%s%s%s" l x d
             ) a
         in
         let e = to_string ~tab:(tab+1) false e in
         pa p (Printf.sprintf "fun (%s) ->%s%s" a (if String.contains e '\n' then ("\n"^(tabs ~tab:(tab+1) ())) else " ") e)
      | App (e, a) ->
         let a = String.concat_map ", " (fun (l,e) -> (if l = "" then "" else (l ^ "=")) ^ to_string ~tab:(tab+1) false e) a in
         pa p (Printf.sprintf "%s(%s)" (to_string ~tab true e) a)
      | Seq [] -> "()"
      | Seq ee ->
         let s = String.concat_map ("\n"^tabs ()) (to_string ~tab false) ee in
         pa p s
      | Decl (x, e) ->
         let e = to_string ~tab:(tab+1) false e in
         let e =
           if String.contains e '\n' then
             Printf.sprintf "\n%s%s\n%s" (tabss ()) e (tabs())
           else
             Printf.sprintf " %s " e
         in
         pa p (Printf.sprintf "%s =%s" x e)
      | Alloc t -> Printf.sprintf "alloc[%s]" (T.to_string t)
      | Module r ->
         if r = [] then "()" else
           let r = List.map (fun (x,v) -> Printf.sprintf "%s%s = %s;" (tabss()) x (to_string ~tab:(tab+1) false v)) r in
           let r = String.concat "\n" r in
           Printf.sprintf "(\n%s\n%s)" r (tabs())
      (* | Field (r,x) -> Printf.sprintf "%s.%s" (to_string ~tab true r) x *)
      | External e -> e.ext_name
      | Monadic Dt -> "dt"
      | Monadic (Ref e) -> pa p (Printf.sprintf "ref(%s)" (to_string ~tab false e))
      | Monadic (RefGet x) -> pa p (Printf.sprintf "!%s" x)
      | Monadic (RefSet (x, e)) -> pa p (Printf.sprintf "%s = %s" x (to_string ~tab false e))
      | Monadic (Expand e) -> pa p (Printf.sprintf "expand(%s)" (to_string ~tab false e))
    in
    to_string ~tab:0 false e

  (** {2 Type inference} *)

  (** Typing error. *)
  exception Typing of pos * string

  let rec infer_type env e =
    Printf.printf "infer_type:\n%s\n\n\n%!" (to_string e);
    let (<:) = T.subtype env in
    let type_error e s =
      Printf.ksprintf (fun s -> raise (Typing (e.pos, s))) s
    in
    match e.desc with
    | Value (Float _) -> T.float ()
    | Value (Int _) -> T.int ()
    | Ident x ->
       let t = try T.Env.typ env x with Not_found -> type_error e "Unbound variable %s." x in
       T.instantiate t
  (*
    | Seq ee ->
       let rec aux env = function
         | [] -> T.unit ()
         | [e] -> infer_type env e
         | e::ee ->
            let te = infer_type env e in
            if not (te <: T.unit ()) then type_error e "This expression has type %s but unit is expected." (T.to_string te);
            aux ee
       in
       aux ee
    | Fun (a,e) ->
       let a =
         List.map
           (fun (l,(x,d)) ->
             let d,t =
               match d with
               | Some d ->
                  let dt = infer_type env d in
                  Some d, dt
               | None ->
                  None, T.var (T.Env.level env)
             in
             let o = d <> None in
             (l,(x,d)), (l,x,t,o)
           ) a
       in
       let a, ta = List.split a in
       let env' = List.map (fun (l,x,t,o) -> x,([],t)) ta in
       let env = T.Env.bind env env' in
       let te = infer_type env e in
       let ta = List.map (fun (l,x,t,o) -> l,(t,o)) ta in
       T.arr ta te
            *)

  let infer_type e = infer_type T.Env.empty e
end

module E = Expr

(* This wil be filled later on. *)
let parse_file_fun = ref ((fun _ -> failwith "Parse file function should have been filled") : string -> E.t)
