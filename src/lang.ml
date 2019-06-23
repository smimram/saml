(** Internal representation of the language and operations to manipulate it
   (typechecking, reduction, etc.). *)

open Extralib
open Common

module T = Type

(** An expression. *)
type t =
  {
    desc : desc; (** The expression. *)
    pos : pos; (** Position in source file. *)
    t : T.t; (** Type. *)
  }
(** Contents of an expression. *)
and desc =
  | Bool of bool
  | Int of int
  | Float of float
  | String of string
  | Var of string (** A variable. *)
  | Fun of pattern * t (** A function. *)
  | FFI of ffi
  | Let of pattern * t * t (** A variable declaration. *)
  | App of t * t
  | Seq of t * t
  | Record of bool * (string * t) list
  (** A record, the boolean indicates whether it is recursive (= a module) or
     not (normal forms are never recursive). *)
  | Closure of environment * t (** A closure. *)
and pattern =
  | PVar of string
  | PRecord of (string * string * t option) list (** A record pattern: label, variable, default value. *)
and ffi =
  {
    ffi_name : string;
    ffi_itype : T.t; (** type of the input *)
    ffi_otype : T.t; (** type of the output *)
    ffi_eval : t -> t; (** evaluation *)
  }
(** An environment. *)
and environment = (string * t) list
type expr = t

let tenv = ref ([] : T.environment)
let env = ref ([] : environment)

(** Create an expression. *)
let make ?(pos=dummy_pos) ?t e =
  let t =
    match t with
    | Some t -> t
    | None -> T.evar max_int
  in
  {
    desc = e;
    pos;
    t
  }

let var ?pos s = make ?pos (Var s)

let bool ?pos b = make ?pos (Bool b)

let float ?pos x = make ?pos (Float x)

let string ?pos x = make ?pos (String x)

let fct ?pos args e = make ?pos (Fun (args, e))

let app ?pos f x = make ?pos (App (f, x))

let seq ?pos e1 e2 = make ?pos (Seq (e1, e2))

let letin ?pos pat def body = make ?pos (Let (pat, def, body))

let record ?pos r l = make ?pos (Record (r, l))

let field ?pos l r =
  let f = fct ?pos(PRecord [l,l,None]) (var ?pos l) in
  app ?pos f r

let unit ?pos () = record ?pos false []

let pair ?pos x y = record ?pos false ["x",x; "y",y]

let fst ?pos r = field ?pos "x" r

let snd ?pos r = field ?pos "y" r

let ffi ?pos name ?(eval=fun _ -> error "Not implemented: %s" name) a b =
  let f =
    FFI
      {
        ffi_name = name;
        ffi_itype = a;
        ffi_otype = b;
        ffi_eval = eval;
      }
  in
  make ?pos f

(** String representation of an expression. *)
let rec to_string ~tab p e =
  let pa p s = if p then Printf.sprintf "(%s)" s else s in
  let tabs ?(tab=tab) () = String.make (2*tab) ' ' in
  let tabss () = tabs ~tab:(tab+1) () in
  match e.desc with
  | Var x -> x
  | Bool b -> string_of_bool b
  | Int n -> string_of_int n
  | Float f -> string_of_float f
  | String s -> Printf.sprintf "%S" s
  | FFI ffi -> Printf.sprintf "<%s>" ffi.ffi_name
  | Fun (pat, e) ->
     let pat = string_of_pattern ~tab pat in 
     let e = to_string ~tab:(tab+1) false e in
     pa p (Printf.sprintf "fun %s ->%s%s" pat (if String.contains e '\n' then ("\n"^(tabs ~tab:(tab+1) ())) else " ") e)
  | Closure (env, e) -> Printf.sprintf "<closure>%s" (to_string ~tab true e)
  | App (e, a) ->
     let e = to_string ~tab true e in
     let a = to_string ~tab:(tab+1) true a in
     pa p (Printf.sprintf "%s %s" e a)
  | Seq (e1, e2) ->
     let e1 = to_string ~tab false e1 in
     let e2 = to_string ~tab false e2 in
     pa p (Printf.sprintf "%s%s\n%s%s" e1 (if !Config.Debug.Lang.show_seq then ";" else "") (tabs ()) e2)
  | Let (pat, def, body) ->
     let pat = string_of_pattern ~tab pat in
     let def = to_string ~tab:(tab+1) false def in
     let def =
       if String.contains def '\n' then Printf.sprintf "\n%s%s" (tabss ()) def
       else Printf.sprintf " %s " def
     in
     let body = to_string ~tab false body in
     if !Config.Debug.Lang.show_let then
       pa p (Printf.sprintf "let %s =%s in\n%s%s" pat def (tabs ()) body)
     else
       pa p (Printf.sprintf "%s =%s\n%s%s" pat def (tabs ()) body)
  | Record (r,l) ->
     if l = [] then (if r then "module end" else "()") else
       let l = List.map (fun (x,v) -> Printf.sprintf "%s%s = %s" (tabss()) x (to_string ~tab:(tab+1) false v)) l in
       let l = String.concat "\n" l in
       if r then Printf.sprintf "module\n%s\n%send" l (tabs())
       else Printf.sprintf "(\n%s\n%s)" l (tabs())
and string_of_pattern ~tab = function
  | PVar x -> x
  | PRecord l ->
     let l =
       List.map
         (fun (l,x,v) ->
           let v =
             match v with
             | Some v -> "="^to_string ~tab:(tab+1) false v
             | None -> ""
           in
           (* TODO: optionally display x *)
           Printf.sprintf "%s%s" l v) l
     in
     let l = String.concat ", " l in
     Printf.sprintf "(%s)" l

let to_string e = to_string ~tab:0 false e

let get_float t =
  match t.desc with
  | Float x -> x
  | _ ->
     error "Expected float but got %s" (to_string t)

let get_string t =
  match t.desc with
  | String s -> s
  | _ -> assert false

(** Free variables of a pattern. *)
let pattern_variables = function
  | PVar x -> [x]
  | PRecord l -> List.map (fun (_,x,_) -> x) l

(** {2 Type inference} *)

(** Typing error. *)
exception Typing of pos * string

let type_error e s =
  Printf.ksprintf (fun s -> raise (Typing (e.pos, s))) s

(** Check the type of an expression. *)
let rec check level (env:T.environment) e =
  (* Printf.printf "infer_type:\n%s\n\n\n%!" (to_string e); *)
  (* Printf.printf "env: %s\n\n" (String.concat_map " , " (fun (x,(_,t)) -> x ^ ":" ^ T.to_string t) env.T.Env.t); *)
  let (<:) e a = if not (T.( <: ) e.t a) then error "%s: %s has type %s but %s expected." (Common.string_of_pos e.pos) (to_string e) (T.to_string e.t) (T.to_string a) in
  let (>:) e a = if not (T.( <: ) a e.t) then error "%s: %s has type %s but %s expected." (Common.string_of_pos e.pos) (to_string e) (T.to_string e.t) (T.to_string a) in
  let type_of_pattern env = function
    | PVar x ->
       let a = T.evar level in
       let env = (x,a)::env in
       env, a
    | PRecord l ->
       let env, l =
         List.fold_left
           (fun (env, l) (lab,x,d) ->
             let a = T.evar level in
             (
               match d with
               | Some d ->
                  check level env d;
                  d <: a
               | None -> ()
             );
             let env = (x,a)::env in
             env, (lab,a)::l
           ) (env,[]) l
       in
       let l = List.rev l in
       env, { desc = Record l }
  in
  match e.desc with
  | Bool _ -> e >: T.bool ()
  | Int _ -> e >: T.int ()
  | Float _ -> e >: T.float ()
  | String _ -> e >: T.string ()
  | FFI f -> e >: T.arr f.ffi_itype f.ffi_otype
  | Var x ->
     let t = try List.assoc x env with Not_found -> type_error e "Unbound variable %s." x in
     (* e >: T.instantiate level t; *)
     e >: t
  | Seq (e1, e2) ->
     check level env e1;
     e1 <: T.unit ();
     check level env e2;
     e >: e2.t
  | Let (pat,def,body) ->
     check (level+1) env def;
     let env, a = type_of_pattern env pat in
     def >: a;
     let env =
       (* Generalize the bound variables. *)
       (List.map
          (fun x -> x, T.generalize level (List.assoc x env))
          (pattern_variables pat)
       )@env
     in
     check level env body;
     e >: body.t
  | Fun (pat,v) ->
     let env, a = type_of_pattern env pat in
     check level env v;
     e >: T.arr a v.t
  | Closure _ -> assert false
  | App (f, v) ->
     let b = T.evar level in
     check level env f;
     check level env v;
     f <: T.arr v.t b;
     e >: b
  | Record (r,l) ->
     let env, l =
       List.fold_left
         (fun (env,l) (x,e) ->
           check level env e;
           let env = if r then (x,e.t)::env else env in
           env, (x,e.t)::l
         ) (env,[]) l
     in
     let l = List.rev l in
     e >: T.record l

let check t = check 0 !tenv t

(** Evaluate a term to a value *)
let rec reduce env t =
  match t.desc with
  | Bool _ | Int _ | Float _ | String _ | FFI _ -> t
  | Var x -> (try List.assoc x env with Not_found -> error "Unbound variable during reduction: %s" x)
  | Fun _ -> make ~pos:t.pos (Closure (env, t))
  | Closure (env, t) -> reduce env t
  | Let (pat, def, body) ->
     let def = reduce env def in
     let env = reduce_pattern env pat def in
     reduce env body
  | App (t, u) ->
     let u = reduce env u in
     let t = reduce env t in
     (
       match t.desc with
       | Closure (env, {desc = Fun (pat, t)}) ->
          let env = reduce_pattern env pat u in
          reduce env t
       | FFI f -> f.ffi_eval u
       | _ -> error "Unexpected term during application: %s" (to_string t)
     )
  | Seq (t, u) ->
     let _ = reduce env t in
     reduce env u
  | Record (r, l) ->
     let l =
       List.fold_left
         (fun l (x,t) ->
           let env = if r then l@env else env in
           (x, reduce env t)::l
         ) [] l
     in
     make ~pos:t.pos (Record (false, List.rev l))

and reduce_pattern env pat v =
  match pat, v.desc with
  | PVar x, _ -> (x,v)::env
  | PRecord p, Record (false, l) ->
     let env' =
       List.map
         (fun (lab,x,d) ->
           let v =
             try List.assoc lab l
             with Not_found ->
               reduce env (Option.get d)
           in
           x, v
         ) p
     in
     env'@env
  | _ -> assert false

let reduce t = reduce !env t

module Run = struct
  let fst t = reduce (fst t)

  let snd t = reduce (snd t)
end
