(******************************************)
(*             ZADANIE ISET               *)
(*        ROZWIĄZANIE: MARCIN ŻOŁEK       *)
(*          RIWJU: JAKUB KLIMEK           *)
(******************************************)

type t = Empty | Node of int * int * t * t * int * int
(** typ t jest pustym poddrzewem (Empty) albo niepustym poddrzewem (Node) 
i wtedy składa sie z lewego końca przedziału, prawego końca przedziału,
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

let remove_one a b set = 
    (** usuwa z drzewa wierzchołek reprezentujący przedział [a, b] *)
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
        (** oblicza (min_a, max_b, lst) takie, że
        min_a jest minimalnym lewym końcem przedziału, ktory nachodzi na [a, b];
        max_b jest maksymalnym końcem przedziału, który nachodzi na [a, b];
        lst jest listą przedziałów w drzewie, które nachodzą na [a, b] *)
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
        (** oblicza (lsta, lstr) takie, że 
        lstr jest listą przedziałów nachodzących na [a, b], czyli takich, 
        które trzeba będzie potem usunąć, długość lsta może być maksymalnie 2,
        bo może do niej należeć tylko przedział nachodzący od lewej na [a, b] lub od prawej;
        lsta jest listą przedziałów, które trzeba będzie potem dodać do drzewa, 
        po usunięciu wierzchołków z lstr *)
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

let add (a, b) set = 
    let (c, d, lst) = pre_add a b set in
    (** usuwa z drzewa przedziały z lst i dodaje przedział [c, d] *)
    add_one c d (List.fold_left (fun acc h -> remove_one (fst h) (snd h) acc) set lst)
    
let remove (a, b) set = 
    let (lsta, lstr) = pre_remove a b set in
    (** usuwa z drzewa przedziały z lstr i dodaje przedziały z lsta *)
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
                plus acc (plus (length l) (distance a n))
            else
                aux r (plus acc (plus (length l) (distance a b)))
    in
    aux set 0

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
