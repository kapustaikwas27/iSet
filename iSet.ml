type t = Empty | Node of int * int * t * t * int * int
(* poczatek przedzialu, koniec przedzialu, 
lewe poddrzewo, prawe poddrzewo,
wysokosc poddrzewa, 
suma dlugosci przedzialow w poddrzewie *)

let plus n m =
    if n > max_int - m then
        max_int
    else
        n + m
    
let height = function
    | Empty -> 0
    | Node (_, _, _, _, h, _) -> h
    
let length = function
    | Empty -> 0
    | Node (_, _, _, _, _, l) -> l
    
let make a b l r =
    Node (a, b, l, r, max (height l) (height r) + 1, plus (plus (length l) (length r)) (b - a + 1))

let balance a b l r =
    let hl = height l in
    let hr = height r in
  
    if hl > hr + 2 then
        match l with
        | Empty -> assert false
        | Node (la, lb, ll, lr, _, _) ->
            if height ll >= height lr then
                make la lb ll (make a b lr r)
            else
                (match lr with
                | Empty -> assert false
                | Node (lra, lrb, lrl, lrr, _, _) -> make lra lrb (make la lb ll lrl) (make a b lrr r))
    else if hr > hl + 2 then
        match r with
        | Empty -> assert false
        | Node (ra, rb, rl, rr, _, _) ->
            if height rr >= height rl then
                make ra rb (make a b l rl) rr
            else
                (match rl with
                | Empty -> assert false
                | Node (rla, rlb, rll, rlr, _, _) -> make rla rlb (make a b l rll) (make ra rb rlr rr))
    else 
        make a b l r
 
let rec min_elt = function
    | Empty -> raise Not_found
    | Node (a, b, Empty, _, _, _) -> (a, b)
    | Node (_, _, l, _, _, _) -> min_elt l

let rec remove_min_elt = function
    | Empty -> invalid_arg "ISet.remove_min_elt"
    | Node (_, _, Empty, r, _, _) -> r
    | Node (a, b, l, r, _, _) -> balance a b (remove_min_elt l) r

let merge set1 set2 =
    match (set1, set2) with
    | (Empty, _) -> set2
    | (_, Empty) -> set1
    | _ ->
        let (a, b) = min_elt set2 in
        balance a b set1 (remove_min_elt set2)

let add_one a b set = 
    let rec aux = function
        | Empty -> make a b Empty Empty
        | Node (c, d, l, r, _, _) ->
            if a < c then
                balance c d (aux l) r
            else 
                balance c d l (aux r)
    in 
    aux set

let remove_one a b set =
    let rec aux = function
        | Empty -> Empty 
        | Node (c, d, l, r, _, _) ->
            if a = c && b = d then 
                merge l r 
            else if a < c then 
                balance c d (aux l) r 
            else 
                balance c d l (aux r)
    in
    aux set

let pre_add a b set =
    let rec aux (min_a, max_b, lst) = function
        | Empty -> (min_a, max_b, lst)
        | Node (c, d, l, r, _, _) ->
            if plus d 1 < a then
                aux (min_a, max_b, lst) r
            else if c <= a && a <= plus d 1 && d < b then
                aux (c, max_b, (c, d)::lst) r
            else if a < c && d < b then
                aux (aux (min_a, max_b, (c, d)::lst) r) l
            else if a < c && c <= plus b 1 && b <= d then
                aux (min_a, d, (c, d)::lst) l
            else if plus b 1 < c then
                aux (min_a, max_b, lst) l
            else
                (c, d, (c, d)::lst)
    in
    aux (a, b, []) set

let pre_remove a b set =
    let rec aux (lsta, lstr) = function
        | Empty -> (lsta, lstr)
        | Node (c, d, l, r, _, _) ->
            if d < a then
                aux (lsta, lstr) r
            else if c < a && a <= d && d <= b then
                aux ((c, a - 1)::lsta, (c, d)::lstr) r
            else if a <= c && d <= b then
                aux (aux (lsta, (c, d)::lstr) r) l
            else if a <= c && c <= b && b < d then
                aux ((b + 1, d)::lsta, (c, d)::lstr) l
            else if b < c then
                aux (lsta, lstr) l
            else 
                ((c, a - 1)::(b + 1, d)::lsta, (c, d)::lstr)
    in
    aux ([], []) set
            
let empty =
    Empty

let is_empty set =
    set = Empty

let add (a, b) set = 
    let (c, d, lst) = pre_add a b set in
    add_one c d (List.fold_left (fun acc h -> remove_one (fst h) (snd h) acc) set lst)
    
let remove (a, b) set = 
    let (lsta, lstr) = pre_remove a b set in
    List.fold_left (fun acc h -> add_one (fst h) (snd h) acc) (List.fold_left (fun a h -> remove_one (fst h) (snd h) a) set lstr) lsta

let mem n set =
    let rec aux = function
        | Empty -> false
        | Node (a, b, l, r, _, _) -> 
            if n < a then
                aux l
            else if a <= n && n <= b then
                true
            else
                aux r
    in
    aux set
    
let iter f set =
    let rec aux = function
        | Empty -> ()
        | Node (a, b, l, r, _, _) -> aux l; f (a, b); aux r 
    in
    aux set
    
let fold f set acc = 
    let rec aux acc = function 
        | Empty -> acc
        | Node (a, b, l, r, _, _) -> aux (f (a, b) (aux acc l)) r
    in
    aux acc set
        
let elements set = 
    let rec aux acc = function
        | Empty -> acc
        | Node (a, b, l, r, _, _) -> aux ((a, b)::(aux acc r)) l
    in
    aux [] set
    
let below n set =
    let rec aux set acc =
        match set with
        | Empty -> acc
        | Node (a, b, l, r, _, _) ->
            if n < a then
                aux l acc
            else if a <= n && n <= b then
                plus acc (plus (length l) (n - a + 1))
            else
                aux r (plus acc (plus (length l) (b - a + 1)))
    in
    aux set 0
