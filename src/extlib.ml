let id x = x

let pi = 4. *. atan 1.

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

  let flatten_map f l =
    let rec aux = function
      | x::t -> (f x)@(aux t)
      | [] -> []
    in
    aux l

  let concat_map = flatten_map

  let fold_map f s l =
    let s = ref s in
    let l =
      List.map
        (fun x ->
          let s', v = f !s x in
          s := s';
          v) l
    in
    !s, l

  let rec remove_all_assocs xx = function
    | (x,_ as p)::l -> if List.mem x xx then remove_all_assocs xx l else p::(remove_all_assocs xx l)
    | [] -> []

  let assoc_rm x l =
    let ans = ref None in
    let l =
      may_map
        (fun (y,v) ->
          if !ans = None && x = y then
            (
              ans := Some v;
              None
            )
          else
            Some (y,v)
        ) l
    in
    match !ans with
    | Some v -> v,l
    | None -> raise Not_found

  let find_nth n p l =
    let n = ref n in
    List.find (fun x -> if p x then (decr n; !n < 0) else false) l

  let assoc_nth n x l =
    snd (find_nth n (fun (y,_) -> y = x) l)
end

module String = struct
  include String

  let concat_map c f l =
    let l = List.map f l in
    String.concat c l
end

module Pair = struct
  let map f g (x,y) = (f x, f y)
end
