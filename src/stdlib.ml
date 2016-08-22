let id x = x

module List = struct
  include List

  let indexq x l =
    let rec aux n = function
      | [] -> raise Not_found
      | y::_ when x == y -> n
      | _::t -> aux (n+1) t
    in
    aux 0 l

  let rec may_map f = function
    | x::l ->
       begin
         match f x with
         | Some y -> y::(may_map f l)
         | None -> may_map f l
       end
    | [] -> []
end

module String = struct
  include String

  let concat_map c f l =
    let l = List.map f l in
    String.concat c l
end
