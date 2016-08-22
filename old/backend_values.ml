(** Values used by the internal interpreter. *)

open Stdlib

module T = Backend_types

type t =
| F of float
| I of int
| B of bool
| R of t array
| S of string
| U (** Unit *)
| Z (** Bottom *)

let rec to_string = function
  | U -> "unit"
  | S s -> s
  | B b -> Printf.sprintf "%B" b
  | I n -> Printf.sprintf "%d" n
  | F x -> Printf.sprintf "%F" x
  | R r ->
    let r = Array.to_list r in
    let r = String.concat_map ", " to_string r in
    Printf.sprintf "{ %s }" r
  | Z -> "⊥"

(** Default value for a given type. The bot argument ensures that values are
    initialized to bot so that usages of uninitialized values are detected. *)
let rec default ?(bot=true) t =
  let default = default ~bot in
  let bot v = if bot then Z else v in
  match t with
  | T.Float -> bot (F 0.)
  | T.Int -> bot (I 0)
  | T.Unit -> bot (U)
  | T.String -> bot (S "")
  | T.Bool -> bot (B false)
  | T.Record r -> R (Array.map default r)
  | T.Array _ -> bot (R [||])
  | t -> failwith (T.to_string t)

let unit = U

let bool b = B b

let int n = I n

let float x = F x

let string s = S s

let bot = Z

let record r = R r

let array n t =
  R (Array.init n (fun _ -> default t))

let get_float = function
  | F x -> x
  | e -> failwith (Printf.sprintf "Backend expected a float but got %s." (to_string e))

let get_int = function
  | I n -> n
  | e -> failwith (Printf.sprintf "Backend expected an int but got %s." (to_string e))

let get_bool = function
  | B b -> b
  | _ -> assert false

let get_string = function
  | S s -> s
  | _ -> assert false

let get_record = function
  | R r -> r
  | e -> failwith (Printf.sprintf "Backend expected a record but got %s." (to_string e))

let get_array = get_record
