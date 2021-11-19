type t

val empty : t
(** The empty set *)

val is_empty : t -> bool
(** returns true if the set is empty. *)

val add : int * int -> t -> t
(** [add (x, y) s] returns a set containing the same elements as [s],
    plus all elements of the interval [[x,y]] including [x] and [y].
    Assumes [x <= y]. *)

val remove : int * int -> t -> t
(** [remove (x, y) s] returns a set containing the same elements as [s],
    except for all those which are included between [x] and [y].
    Assumes [x <= y]. *)

val mem : int -> t -> bool
(** [mem x s] returns [true] if [s] contains [x], and [false] otherwise. *)

val iter : (int * int -> unit) -> t -> unit
(** [iter f s] applies [f] to all continuous intervals in the set [s].
    The intervals are passed to [f] in increasing order. *)

val fold : (int * int -> 'a -> 'a) -> t -> 'a -> 'a
(** [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)], where x1
    ... xN are all continuous intervals of s, in increasing order. *)

val elements : t -> (int * int) list
(** Return the list of all continuous intervals of the given set.
    The returned list is sorted in increasing order. *)

val below : int -> t -> int
(** [below n s] returns the number of elements of [s] that are lesser
    or equal to [n]. If there are more than max_int such elements, 
    the result should be max_int. *)

val split : int -> t -> t * bool * t
(** [split x s] returns a triple [(l, present, r)], where
    [l] is the set of elements of [s] that are strictly lesser than [x];
    [r] is the set of elements of [s] that are strictly greater than [x];
    [present] is [false] if [s] contains no element equal to [x],
    or [true] if [s] contains an element equal to [x]. *)
