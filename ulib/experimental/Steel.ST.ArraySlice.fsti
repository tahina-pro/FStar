module Steel.ST.ArraySlice
open Steel.ST.Util

#set-options "--ide_id_info_off"

module U32 = FStar.UInt32
module P = Steel.FractionalPermission

val array_slice (elt: Type0) : Tot (Type0)

val base_length (#elt: Type0) (a: array_slice elt) : GTot nat

val offset (#elt: Type0) (a: array_slice elt) : Ghost nat
  (requires True)
  (ensures (fun y -> y <= base_length a))

val invariant (#elt: Type0) (a: array_slice elt) : Tot vprop

val invariant_of (#elt: Type0) (a: array_slice elt) : Tot (inv (invariant a))

val pts_to (#elt: Type) (a: array_slice elt) ([@@@ smt_fallback ] p: P.perm) ([@@@ smt_fallback ] s: Seq.seq elt) : Tot vprop

inline_for_extraction
[@@noextract_to "krml"]
val alloc
  (#elt: Type)
  (x: elt)
  (n: U32.t)
: ST (array_slice elt)
    emp
    (fun a -> pts_to a P.full_perm (Seq.create (U32.v n) x))
    True
    (fun a ->
      base_length a == U32.v n /\
      offset a == 0
    )

val share
  (#opened: _)
  (#elt: Type)
  (#x: Seq.seq elt)
  (a: array_slice elt)
  (p p1 p2: P.perm)
: STGhost unit opened
    (pts_to a p x)
    (fun _ -> pts_to a p1 x `star` pts_to a p2 x)
    (p == p1 `P.sum_perm` p2)
    (fun _ -> True)

val gather
  (#opened: _)
  (#elt: Type)
  (a: array_slice elt)
  (#x1: Seq.seq elt) (p1: P.perm)
  (#x2: Seq.seq elt) (p2: P.perm)
: STGhost unit opened
    (pts_to a p1 x1 `star` pts_to a p2 x2)
    (fun _ -> pts_to a (p1 `P.sum_perm` p2) x1)
    (requires (Seq.length x1 == Seq.length x2))
    (ensures (fun _ -> x1 == x2))

[@@noextract_to "krml"]
let seq_index
  (#t: Type)
  (s: Seq.seq t)
  (i: nat)
: Pure t
    (requires (i < Seq.length s))
    (ensures (fun _ -> True))
= Seq.index s i

inline_for_extraction
[@@noextract_to "krml"]
val atomic_read (#t:Type) (#p:perm) (#opened: _)
         (a:array_slice t)
         (#s:Ghost.erased (Seq.seq t))
         (i:U32.t)
: STAtomic t opened
       (pts_to a p s)
       (fun _ -> pts_to a p s)
       (requires (
         not (mem_inv opened (invariant_of a)) /\ // FIXME: HOW HOW HOW to prove this precondition if atomicity is needed?
         U32.v i < Seq.length s
       ))
       (ensures fun v ->
         U32.v i < Seq.length s /\
         v == seq_index s (U32.v i))

inline_for_extraction
[@@noextract_to "krml"]
let read (#t:Type) (#p:perm)
         (a:array_slice t)
         (#s:Ghost.erased (Seq.seq t))
         (i:U32.t)
: ST t
       (pts_to a p s)
       (fun _ -> pts_to a p s)
       (requires (
         U32.v i < Seq.length s
       ))
       (ensures fun v ->
         U32.v i < Seq.length s /\
         v == seq_index s (U32.v i))
= atomic_read a i

inline_for_extraction
[@@noextract_to "krml"]
val atomic_write (#t:Type) (#opened: _)
         (a:array_slice t)
         (#s:Ghost.erased (Seq.seq t))
         (i:U32.t)
         (v: t)
: STAtomic (Ghost.erased (Seq.seq t)) opened
       (pts_to a P.full_perm s)
       (fun s' -> pts_to a P.full_perm s')
       (requires (
         not (mem_inv opened (invariant_of a)) /\ // FIXME: HOW HOW HOW to prove this precondition if atomicity is needed?
         U32.v i < Seq.length s
       ))
       (ensures fun s' ->
         U32.v i < Seq.length s /\
         Ghost.reveal s' == Seq.upd s (U32.v i) v)

inline_for_extraction
[@@noextract_to "krml"]
let write (#t:Type)
         (a:array_slice t)
         (#s:Ghost.erased (Seq.seq t))
         (i:U32.t)
         (v: t)
: ST (Ghost.erased (Seq.seq t))
       (pts_to a P.full_perm s)
       (fun s' -> pts_to a P.full_perm s')
       (requires (
         U32.v i < Seq.length s
       ))
       (ensures fun s' ->
         U32.v i < Seq.length s /\
         Ghost.reveal s' == Seq.upd s (U32.v i) v)
= atomic_write a i v

val ptr_le (#elt: Type) (a1 a2: array_slice elt) : Tot prop

val ptr_diff (#elt: Type) (a2 a1: array_slice elt) : Pure U32.t
  (requires (ptr_le a1 a2))
  (ensures (fun n ->
    base_length a2 == base_length a1 /\
    offset a1 + U32.v n == offset a2
  ))

let has_ptr_diff (#elt: Type) (a2 a1: array_slice elt) (diff: nat) : Tot prop =
  ptr_le a1 a2 /\
  U32.v (ptr_diff a2 a1) == diff

val ptr_shift
  (#elt: Type)
  (a: array_slice elt)
  (i: U32.t)
: Pure (array_slice elt)
    (requires (offset a + U32.v i <= base_length a))
    (ensures (fun y -> has_ptr_diff y a (U32.v i)))

val ptr_le_trans
  (#elt: Type)
  (a1 a2 a3: array_slice elt)
: Lemma
  (requires (ptr_le a1 a2 /\ ptr_le a2 a3))
  (ensures (
    ptr_le a1 a3 /\
    U32.v (ptr_diff a3 a1) == U32.v (ptr_diff a3 a2) + U32.v (ptr_diff a2 a1)
  ))

val ptr_shift_assoc
  (#elt: Type)
  (a: array_slice elt)
  (i1 i2: U32.t)
: Ghost U32.t
    (requires (offset a + U32.v i1 + U32.v i2 <= base_length a))
    (ensures (fun y ->
      U32.v y == U32.v i1 + U32.v i2 /\
      ptr_shift (ptr_shift a i1) i2 == ptr_shift a y
    ))

val join
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: Seq.seq elt)
  (#p: perm)
  (a1 a2: array_slice elt)
: STGhost unit opened
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun _ -> pts_to a1 p (x1 `Seq.append` x2))
    (has_ptr_diff a2 a1 (Seq.length x1))
    (fun _ -> True)

val ghost_split
  (#opened: _)
  (#elt: Type)
  (#x: Seq.seq elt)
  (#p: perm)
  (a: array_slice elt)
  (i: U32.t)
: STGhost (Ghost.erased (array_slice elt)) opened
    (pts_to a p x)
    (fun res -> exists_ (fun x1 -> exists_ (fun x2 ->
      pts_to a p x1 `star`
      pts_to res p x2 `star`
      pure (
        U32.v i <= Seq.length x /\
        x1 == Seq.slice x 0 (U32.v i) /\
        x2 == Seq.slice x (U32.v i) (Seq.length x) /\
        x == x1 `Seq.append` x2 /\
        offset a + Seq.length x <= base_length a /\
        Ghost.reveal res == ptr_shift a i
    ))))
    (U32.v i <= Seq.length x)
    (fun _ -> True)

inline_for_extraction
[@@noextract_to "krml"]
val split
  (#opened: _)
  (#elt: Type)
  (#x: Ghost.erased (Seq.seq elt))
  (#p: perm)
  (a: array_slice elt)
  (i: U32.t)
: STAtomicBase (array_slice elt) false opened Unobservable
    (pts_to a p x)
    (fun res -> exists_ (fun x1 -> exists_ (fun x2 ->
      pts_to a p x1 `star`
      pts_to res p x2 `star`
      pure (
        U32.v i <= Seq.length x /\
        x1 == Seq.slice x 0 (U32.v i) /\
        x2 == Seq.slice x (U32.v i) (Seq.length x) /\
        Ghost.reveal x == x1 `Seq.append` x2 /\
        offset a + Seq.length x <= base_length a /\
        Ghost.reveal res == ptr_shift a i
    ))))
    (U32.v i <= Seq.length x)
    (fun _ -> True)
