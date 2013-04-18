open Stdlib

type t =
| Int
| Float
| Bool
| Unit
| String
| Record of t array
| Array of t
| Ptr of t

let rec to_string = function
  | Int -> "int"
  | Float -> "float"
  | Bool -> "bool"
  | Unit -> "unit"
  | String -> "string"
  | Record t ->
    let t = Array.to_list t in
    let t = String.concat_map ", " to_string t in
    Printf.sprintf "{ %s }" t
  | Array t -> Printf.sprintf "%s array" (to_string t)
  | Ptr t -> Printf.sprintf "*%s" (to_string t)

let get_record = function
  | Record r -> r
  | _ -> assert false
