module Selectors.LList3

module C = Steel.ST.Combinators
open Steel.ST.Reference
open Steel.ST.Effect

/// This module provides the same interface as Selectors.LList and Selectors.LList2.
/// The difference is in the implementation, it uses a newer, promising style to handle vprop.
/// Instead of going down all the way to the underlying slprop representation, it uses different
/// combinators to define the core list vprop

/// Abstract type of a list cell containing a value of type [a]
val cell (a:Type0) : Type0
/// The type of a list: A reference to a cell
[@__steel_reduce__]
let t (a:Type0) = ref (cell a)

(* Helpers to manipulate cells while keeping its definition abstract *)

val next (#a:Type0) (c:cell a) : t a
val data (#a:Type0) (c:cell a) : a
val mk_cell (#a:Type0) (n: t a) (d:a)
  : Pure (cell a)
    (requires True)
    (ensures fun c ->
      next c == n /\
      data c == d)


/// The null list pointer
val null_llist (#a:Type) : t a

/// Lifting the null pointer check to empty lists
val is_null (#a:Type) (ptr:t a) : (b:bool{b <==> ptr == null_llist})


/// Separation logic predicate stating that reference [r] points to a valid list in memory
val llist0 (#a:Type0) (r:t a) : Pure vprop (requires True) (ensures (fun y -> t_of y == list a))

[@@__steel_reduce__]
let llist (#a:Type0) (r:t a) : Tot vprop = C.vunit (llist0 r) (list a)

(** Stateful lemmas to fold and unfold the llist predicate **)

let equals = unit

val intro_llist_nil (a:Type0)
  : STT unit emp (fun _ -> llist (null_llist #a) `C.vselect` [])

val is_nil (#a:Type0) (#l: Ghost.erased (list a)) (ptr:t a)
  : ST bool (llist ptr `C.vselect` l) (fun _ -> llist ptr `C.vselect` l)
          (requires True)
          (ensures fun res ->
            (res == true <==> ptr == null_llist #a) /\
            res == Nil? l)

val intro_llist_cons (#a:Type0) (#hd: Ghost.erased (cell a)) (#tl: Ghost.erased (list a)) (ptr1 ptr2:t a)
  : ST unit ((vptr ptr1 `C.vselect` hd) `star` (llist ptr2 `C.vselect` tl))
            (fun _ -> llist ptr1 `C.vselect` (data hd :: tl))
                  (requires (next hd == ptr2))
                  (ensures fun _ -> True)

module L = FStar.List.Tot

let tail_postcond
  (#a:Type0) (l: Ghost.erased (list a)) (ptr:t a)
  (n: t a)
  (x: (t_of (vptr ptr `star` llist n)))
: Tot prop
=
         let (hd, tl) = x in
         Cons? l /\
         hd == mk_cell n (L.hd (Ghost.reveal l)) /\
         tl == L.tl l

module C = Steel.ST.Combinators

val tail (#a:Type0) (#l: Ghost.erased (list a)) (ptr:t a)
  : ST (t a)
       (llist ptr `C.vselect` l)
       (fun (n: t a) -> (vptr ptr `star` llist n) `C.vrefine` tail_postcond l ptr n)
       (requires ptr =!= null_llist)
       (ensures fun _ -> True)
