let id x = x

let pi = 4. *. atan 1.

let get_some x =
  match x with
    | Some x -> x
    | None -> assert false

let may f x =
  match x with
  | Some x -> Some (f x)
  | None -> None

let maybe d = function
  | Some x -> x
  | None -> d

let fst3 (x,_,_) = x

let snd3 (_,x,_) = x

let thd3 (_,_,x) = x

let fixpoint ?(compare=compare) f x =
  let x = ref x in
  let loop = ref true in
  while !loop do
    let y = f !x in
    if compare !x y = 0 then loop := false;
    x := y
  done;
  !x

module Array = struct
  include Array

  let index x a =
    let ans = ref (-1) in
    try
      for i = 0 to Array.length a - 1 do
        if a.(i) = x then
          (
            ans := i;
            raise Exit
          )
      done;
      raise Not_found
    with
      | Exit -> !ans

  let map2 f a1 a2 =
    assert (Array.length a1 = Array.length a2);
    Array.init (Array.length a1) (fun i -> f a1.(i) a2.(i))

  let exists f a =
    try
      Array.iter (fun x -> if f x then raise Exit) a;
      false
    with
    | Exit -> true

  let for_all f a =
    try
      Array.iter (fun x -> if not (f x) then raise Exit) a;
      true
    with
    | Exit -> false
end

module List = struct
  include List

  let rec iter_right f = function
    | x::t -> iter_right f t; f x
    | [] -> ()

  let mapi f l =
    let rec aux n = function
      | x::t -> (f n x)::(aux (n+1) t)
      | [] -> []
    in
    aux 0 l

  let rec last = function
    | [x] -> x
    | _::t -> last t
    | [] -> raise Not_found

  let diff b a =
    List.filter (fun x -> not (List.mem x a)) b

  let index x l =
    let rec aux n = function
      | [] -> raise Not_found
      | y::_ when x = y -> n
      | _::t -> aux (n+1) t
    in
    aux 0 l

  let indexq x l =
    let rec aux n = function
      | [] -> raise Not_found
      | y::_ when x == y -> n
      | _::t -> aux (n+1) t
    in
    aux 0 l

  let may_map f l =
    let rec aux = function
      | x::t ->
        (
          match f x with
            | Some y -> y::(aux t)
            | None -> aux t
        )
      | [] -> []
    in
    aux l

  let may_mapi f l =
    let l = mapi f l in
    may_map id l

  let assoc_all x l =
    let rec aux = function
      | (y,v)::t -> if y = x then v::(aux t) else aux t
      | [] -> []
    in
    aux l

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

  let rec remove_all_assoc x = function
    | (y,_ as p)::l -> if x = y then remove_all_assoc x l else p::(remove_all_assoc x l)
    | [] -> []

  let rec remove_all_assocs xx = function
    | (x,_ as p)::l -> if List.mem x xx then remove_all_assocs xx l else p::(remove_all_assocs xx l)
    | [] -> []

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

  let count p l =
    let ans = ref 0 in
    List.iter (fun x -> if p x then incr ans) l;
    !ans

  let rec nth n l =
    match l with
    | x::_ when n = 0 -> x
    | _::t -> nth (n-1) t
    | [] -> raise Not_found

  let assoc_nth n x l =
    let n = ref n in
    let rec aux = function
      | (y,v)::l when x = y ->
        if !n = 0 then v
        else (decr n; aux l)
      | _::l -> aux l
      | [] -> raise Not_found
    in
    aux l

  let init n f =
    let rec aux k =
      if k = n then []
      else (f k)::(aux (k+1))
    in
    aux 0
end

module String = struct
  include String

  let count c s =
    let ans = ref 0 in
    for i = 0 to String.length s - 1 do
      if s.[i] = c then incr ans
    done;
    !ans

  let concat_map c f l =
    let l = List.map f l in
    String.concat c l

  let spaces n =
    String.make n ' '
end
