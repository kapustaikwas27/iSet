(******************************************)
(*             ZADANIE ISET               *)
(*        ROZWIAZANIE: MARCIN ŻOŁEK       *)
(*          RIWJU: JAKUB KLIMEK           *)
(******************************************)

type t = Empty | Node of int * int * t * t * int * int
(** typ t jest pustym poddrzewem (Empty) albo niepustym poddrzewem (Node) 
i wtedy składa się z lewego końca przedziału, prawego końca przedziału,
lewego poddrzewa, prawego poddrzewa, wysokości poddrzewa,
sumy długości przedziałów w poddrzewie *) 

let plus n m = (** min (n + m) max_int *)
    if n > max_int - m then
        max_int
    else
        n + m
        
let distance a b = (** min (b - a + 1) max_int *)
    if (a >= 0 && b >= 0 && -a > max_int - 1 - b)
    || (a < 0 && 0 < b && -(a + 1) > max_int - b - 2) 
    || (a <= 0 && b <= 0 && b > max_int - 1 + a) then
        max_int
    else
        b - a + 1
    
let height = function
    | Empty -> 0
    | Node (_, _, _, _, h, _) -> h
    
let length = function
    | Empty -> 0
    | Node (_, _, _, _, _, l) -> l
    
let make a b l r =
    Node (a, b, l, r, max (height l) (height r) + 1, plus (plus (length l) (length r)) (distance a b))

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
    (** dodaje wierzchołek reprezentujący przedział [a, b] do drzewa, w którym nie ma elementów z [a - 1, b + 1] *)
    let rec aux = function
        | Empty -> make a b Empty Empty
        | Node (c, d, l, r, _, _) ->
            if a < c then
                balance c d (aux l) r
            else 
                balance c d l (aux r)
    in 
    aux set

let pre_add a b set = 
    let rec aux_min min_a = function
        (** oblicza min_a takie, że jest minimalnym lewym końcem przedziału, ktory nachodzi na [a, b] *)
        | Empty -> min_a
        | Node (c, d, l, r, _, _) ->
            if plus d 1 < a then
                aux_min min_a r
            else if a < c then
                aux_min min_a l
            else
                c
    in
    let rec aux_max max_b = function
        (** obicza max_b takie, że jest maksymalnym końcem przedziału, który nachodzi na [a, b] *)
        | Empty -> max_b
        | Node (c, d, l, r, _, _) ->
            if d < b then
                aux_max max_b r
            else if plus b 1 < c then
                aux_max max_b l
            else 
                d
    in
    (aux_min a set, aux_max b set)
    
let rec join a b l r =
    match (l, r) with
    | (Empty, _) -> add_one a b r
    | (_, Empty) -> add_one a b l
    | (Node (la, lb, ll, lr, lh, _), Node (ra, rb, rl, rr, rh, _)) ->
        if lh > rh + 2 then 
            balance la lb ll (join a b lr r) 
        else if rh > lh + 2 then 
            balance ra rb (join a b l rl) rr
        else
            make a b l r
            
let empty =
    Empty

let is_empty set =
    set = Empty
    
let split n set =
    let rec aux = function
        | Empty -> (Empty, false, Empty)
        | Node (a, b, l, r, _, _) ->
            if n < a then
                let (ll, pres, lr) = aux l in
                (ll, pres, join a b lr r)
            else if b < n then
                let (rl, pres, rr) = aux r in
                (join a b l rl, pres, rr)
            else if a = n && n < b then 
                (l, true, add_one (n + 1) b r)
            else if a = n && n = b then
                (l, true, r)
            else if a < n && n = b then
                (add_one a (n - 1) l, true, r)
            else 
                (add_one a (n - 1) l, true, add_one (n + 1) b r)
    in
    aux set

let add (a, b) set = 
    (** znajduje przedział do dodania *)
    let (c, d) = pre_add a b set in
    (** tworzy drzewo z przedziałami ostro mniejszymi od c *)
    let (l, _, _) = split c set in
    (** tworzy drzewo z przedziałami ostro większymi od d *)
    let (_, _, r) = split d set in
    (** łączy te dwa drzewa *)
    join c d l r
    
let remove (a, b) set = 
    (** tworzy drzewo z przedziałami ostro mniejszymi od a *)
    let (l, _, _) = split a set in
    (** tworzy drzewo z przedziałami ostro większymi od b *)
    let (_, _, r) = split b set in
    (** łączy te dwa drzewa *)
    match (l, r) with
    | (Empty, _) -> r
    | (_, Empty) -> l
    | (_, _) -> 
        let (c, d) = min_elt r in
        join c d l (remove_min_elt r)

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
        | Node (a, b, l, r, _, _) -> aux ((a, b) :: (aux acc r)) l
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
                plus acc (plus (length l) (distance a n))
            else
                aux r (plus acc (plus (length l) (distance a b)))
    in
    aux set 0
