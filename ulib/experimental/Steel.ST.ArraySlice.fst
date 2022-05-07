module Steel.ST.ArraySlice
open Steel.ST.Util

module A = Steel.ST.Array
module R = Steel.ST.GhostPCMReference
module P = Steel.PCMFrac
module M = FStar.Map
module PM = Steel.PCMMap
module U32 = FStar.UInt32

/// Gather permissions on reference [r]
let derive_composable (#o:inames)
           (#a:Type)
           (#p:P.pcm a)
           (r:R.ref a p)
           (v0:a)
           (v1:a)
  : STGhost unit o
           (R.pts_to r v0 `star` R.pts_to r v1)
           (fun _ -> R.pts_to r v0 `star` R.pts_to r v1)
           True
           (fun _ -> FStar.PCM.composable p v0 v1)
= R.gather r v0 v1;
  R.share r _ v0 v1

[@@noextract_to "krml"]
let index_t (len: nat) : Tot eqtype = (i: nat { i < len })

[@@noextract_to "krml"]
let carrier (elt: Type u#a) (len: nat) : Tot Type =
  PM.map (index_t len) (P.fractional elt)

[@@noextract_to "krml"]
let pcm (elt: Type u#a) (len: nat) : Tot (P.pcm (carrier elt len)) =
  PM.pointwise (index_t len) (P.pcm_frac #elt)

[@@noextract_to "krml"]
let one (#elt: Type) (#len: nat) = (pcm elt len).P.p.P.one
let composable (#elt: Type) (#len: nat) = (pcm elt len).P.p.P.composable
[@@noextract_to "krml"]
let compose (#elt: Type) (#len: nat) = (pcm elt len).P.p.P.op

[@@noextract_to "krml"]
let mk_carrier
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p: P.perm)
: Tot (carrier elt len)
= let f (i: index_t len) : Tot (P.fractional elt) =
    if offset + Seq.length s > len || i < offset || i >= offset + Seq.length s
    then None
    else Some (Seq.index s (i - offset), p)
  in
  M.map_literal f

[@@__reduce__]
let invariant0
  (#elt: Type)
  (base: A.array elt)
  (gr: R.ref _ (pcm elt (A.length base)))
: Tot vprop
= exists_ (fun (whole_seq: Seq.seq elt) ->
    A.pts_to base P.full_perm whole_seq `star`
    R.pts_to gr (mk_carrier (A.length base) 0 whole_seq (P.half_perm P.full_perm)) `star`
    pure (Seq.length whole_seq == A.length base)
  )

let invariant
  (#elt: Type)
  (base: A.array elt)
  (gr: R.ref _ (pcm elt (A.length base)))
: Tot vprop
= invariant0 base gr

noeq
type array_slice (elt: Type) = {
  base: A.array elt;
  base_gr: R.ref _ (pcm elt (A.length base));
  base_inv: inv (invariant base base_gr);
  base_len: Ghost.erased U32.t; // to prove that A.read, A.write offset computation does not overflow
  offset: U32.t;
  length: Ghost.erased U32.t;
  prf: squash (U32.v offset + U32.v length <= A.length base /\ U32.v base_len == A.length base);
}

let len (#elt: Type) (a: array_slice elt) : GTot U32.t =
  a.length

let length (#elt: Type) (a: array_slice elt) : GTot nat =
  U32.v (len a)

let valid_perm
  (len: nat)
  (offset: nat)
  (slice_len: nat)
  (p: P.perm) : Tot prop =
  let open FStar.Real in
  ((offset + slice_len <= len /\ slice_len > 0) ==> (p.P.v <=. one))

[@@__reduce__]
let pts_to0 (#elt: Type) (a: array_slice elt) (p: P.perm) (s: Seq.seq elt) : Tot vprop =
  R.pts_to a.base_gr (mk_carrier (A.length a.base) (U32.v a.offset) s (P.half_perm p)) `star`
  pure (
    valid_perm (A.length a.base) (U32.v a.offset) (Seq.length s) (P.half_perm p) /\
    Seq.length s == length a
  )

let pts_to (#elt: Type) (a: array_slice elt) ([@@@ smt_fallback ] p: P.perm) ([@@@ smt_fallback ] s: Seq.seq elt) : Tot vprop =
  pts_to0 a p s

let valid_sum_perm
  (len: nat)
  (offset: nat)
  (slice_len: nat)
  (p1 p2: perm)
: Tot prop
= let open FStar.Real in
  valid_perm len offset slice_len (P.sum_perm p1 p2)

let mk_carrier_valid_sum_perm
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p1 p2: P.perm)
: Lemma
  (let c1 = mk_carrier len offset s p1 in
   let c2 = mk_carrier len offset s p2 in
   composable c1 c2 <==> valid_sum_perm len offset (Seq.length s) p1 p2)
= let c1 = mk_carrier len offset s p1 in
  let c2 = mk_carrier len offset s p2 in
  if Seq.length s > 0 && offset + Seq.length s <= len
  then
    let open FStar.Real in
    assert (P.composable (M.sel c1 offset) (M.sel c2 offset) <==> valid_perm len offset (Seq.length s) (P.sum_perm p1 p2))
  else ()

let mk_carrier_perm
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p1 p2: P.perm)
: Lemma
  (requires (valid_sum_perm len offset (Seq.length s) p1 p2))
  (ensures (
    let c1 = mk_carrier len offset s p1 in
    let c2 = mk_carrier len offset s p2 in
      composable c1 c2 /\
      mk_carrier len offset s (p1 `P.sum_perm` p2) `M.equal` (c1 `compose` c2)
  ))
= ()

inline_for_extraction
[@@noextract_to "krml"]
let alloc
  (#elt: Type)
  (x: elt)
  (n: U32.t)
: ST (array_slice elt)
    emp
    (fun a -> pts_to a P.full_perm (Seq.create (U32.v n) x))
    True
    (fun a -> len a == n)
=
  let base = A.alloc x n in
  let c = Ghost.hide (mk_carrier (A.length base) 0 (Seq.create (U32.v n) x) P.full_perm) in
  let base_gr : R.ref _ (pcm elt (A.length base)) = R.alloc (Ghost.reveal c) in
  mk_carrier_perm (A.length base) 0 (Seq.create (U32.v n) x) (P.half_perm P.full_perm) (P.half_perm P.full_perm);
  let c_h = Ghost.hide (mk_carrier (A.length base) 0 (Seq.create (U32.v n) x) (P.half_perm P.full_perm)) in
  R.share base_gr c c_h c_h;
  rewrite
    (invariant0 base base_gr)
    (invariant base base_gr);
  let i = new_invariant (invariant base base_gr) in
  let a = {
    base = base;
    base_gr = base_gr;
    base_len = Ghost.hide n;
    base_inv = i;
    offset = 0ul;
    length = Ghost.hide n;
    prf = ();
  }
  in
  rewrite
    (R.pts_to base_gr c_h)
    (R.pts_to a.base_gr c_h);
  rewrite
    (pts_to0 a P.full_perm (Seq.create (U32.v n) x))
    (pts_to a P.full_perm (Seq.create (U32.v n) x));
  return a

let share
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
= rewrite
    (pts_to a p x)
    (pts_to0 a p x);
  let _ = gen_elim () in
  mk_carrier_perm (A.length a.base) (U32.v a.offset) x (P.half_perm p1) (P.half_perm p2);
  R.share a.base_gr _
    (mk_carrier (A.length a.base) (U32.v a.offset) x (P.half_perm p1))
    (mk_carrier (A.length a.base) (U32.v a.offset) x (P.half_perm p2));
  rewrite
    (pts_to0 a p1 x)
    (pts_to a p1 x);
  rewrite
    (pts_to0 a p2 x)
    (pts_to a p2 x)

let gather
  (#opened: _)
  (#elt: Type)
  (#x: Seq.seq elt)
  (a: array_slice elt)
  (p1 p2: P.perm)
: STGhostT unit opened
    (pts_to a p1 x `star` pts_to a p2 x)
    (fun _ -> pts_to a (p1 `P.sum_perm` p2) x)
= rewrite
    (pts_to a p1 x)
    (pts_to0 a p1 x);
  rewrite
    (pts_to a p2 x)
    (pts_to0 a p2 x);
  let _ = gen_elim () in
  derive_composable
    a.base_gr
    (mk_carrier (A.length a.base) (U32.v a.offset) x (P.half_perm p1))
    (mk_carrier (A.length a.base) (U32.v a.offset) x (P.half_perm p2));
  mk_carrier_valid_sum_perm (A.length a.base) (U32.v a.offset) x (P.half_perm p1) (P.half_perm p2);
  mk_carrier_perm (A.length a.base) (U32.v a.offset) x (P.half_perm p1) (P.half_perm p2);
  R.gather a.base_gr
    (mk_carrier (A.length a.base) (U32.v a.offset) x (P.half_perm p1))
    (mk_carrier (A.length a.base) (U32.v a.offset) x (P.half_perm p2));
  rewrite
    (pts_to0 a (p1 `P.sum_perm` p2) x)
    (pts_to a (p1 `P.sum_perm` p2) x)

let mk_carrier_index
  (#elt: Type)
  (len: nat)
  (offset1: nat)
  (s1: Seq.seq elt)
  (p1: P.perm)
  (offset2: nat)
  (s2: Seq.seq elt)
  (p2: P.perm)
  (i1: nat)
  (i2: nat)
  (_: squash (
    composable
      (mk_carrier len offset1 s1 p1)
      (mk_carrier len offset2 s2 p2) /\
    offset1 + Seq.length s1 <= len /\
    i1 < Seq.length s1 /\
    offset2 + Seq.length s2 <= len /\
    i2 < Seq.length s2 /\
    offset1 + i1 == offset2 + i2
  ))
: Lemma
  (ensures (
    let o_l = mk_carrier len offset1 s1 p1 in
    let o_r = mk_carrier len offset2 s2 p2 in
    M.sel o_l (offset1 + i1) == Some (Seq.index s1 i1, p1) /\
    M.sel o_r (offset2 + i2) == Some (Seq.index s2 i2, p2) /\
    M.sel (compose o_l o_r) (offset1 + i1) == Some (Seq.index s1 i1, p1 `P.sum_perm` p2) /\
    M.sel (compose o_l o_r) (offset2 + i2) == Some (Seq.index s2 i2, p1 `P.sum_perm` p2) /\
    Seq.index s1 i1 == Seq.index s2 i2
  ))
= ()

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
let read_body
  (#t: Type) (#p: perm) (#opened: _)
  (a: array_slice t)
  (#s: Ghost.erased (Seq.seq t))
  (i: U32.t)
  (_: unit)
: STAtomicT t opened
    (invariant a.base a.base_gr `star` (pts_to a p s `star` pure ((U32.v i < length a) == true)))
    (fun res -> invariant a.base a.base_gr `star` (pts_to a p s `star` pure (U32.v i < Seq.length s /\ res == seq_index s (U32.v i))))
=
  rewrite
    (invariant a.base a.base_gr)
    (invariant0 a.base a.base_gr);
  rewrite
    (pts_to a p s)
    (pts_to0 a p s);
  let _ = gen_elim () in
  derive_composable #_ #(carrier t (A.length a.base))
    a.base_gr
    (mk_carrier (A.length a.base) 0 _ (P.half_perm P.full_perm))
    (mk_carrier (A.length a.base) (U32.v a.offset) s (P.half_perm p));
  let full = vpattern_erased (fun full -> A.pts_to a.base P.full_perm full) in
  mk_carrier_index (A.length a.base)
    0 full (P.half_perm P.full_perm)
    (U32.v a.offset) s (P.half_perm p)
    (U32.v a.offset + U32.v i) (U32.v i) ();
  let res = A.read a.base (a.offset `U32.add` i) in
  rewrite
    (invariant0 a.base a.base_gr)
    (invariant a.base a.base_gr);
  rewrite
    (pts_to0 a p s)
    (pts_to a p s);
  return res

inline_for_extraction
[@@noextract_to "krml"]
let atomic_read (#t:Type) (#p:perm) (#opened: _)
         (a:array_slice t)
         (#s:Ghost.erased (Seq.seq t))
         (i:U32.t)
: STAtomic t opened
       (pts_to a p s)
       (fun _ -> pts_to a p s)
       (requires (
         not (mem_inv opened a.base_inv) /\ // FIXME: HOW HOW HOW to prove this precondition if atomicity is needed?
         U32.v i < length a
       ))
       (ensures fun v ->
         U32.v i < Seq.length s /\
         v == seq_index s (U32.v i))
= noop ();
  let res = with_invariant a.base_inv (read_body a i) in
  let _ = gen_elim () in
  return res

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
         U32.v i < length a
       ))
       (ensures fun v ->
         U32.v i < Seq.length s /\
         v == seq_index s (U32.v i))
= atomic_read a i

let mk_carrier_upd
  (#elt: Type)
  (full: Seq.seq elt)
  (offset: nat)
  (s: Seq.seq elt)
  (i: nat)
  (v: elt)
  (_: squash (
    composable
      (mk_carrier (Seq.length full) 0 full (P.half_perm P.full_perm))
      (mk_carrier (Seq.length full) offset s (P.half_perm P.full_perm)) /\
    offset + Seq.length s <= Seq.length full /\
    i < Seq.length s
  ))
: Lemma
  (ensures (
    let o = compose
      (mk_carrier (Seq.length full) 0 full (P.half_perm P.full_perm))
      (mk_carrier (Seq.length full) offset s (P.half_perm P.full_perm))
    in
    let nl = mk_carrier (Seq.length full) 0 (Seq.upd full (offset + i) v) (P.half_perm P.full_perm) in
    let nr = mk_carrier (Seq.length full) offset (Seq.upd s i v) (P.half_perm P.full_perm) in
    composable nl nr /\
    compose nl nr `Map.equal` Map.upd o (offset + i) (Some (v, P.full_perm))
  ))
= ()

inline_for_extraction
[@@noextract_to "krml"]
let write_body
  (#t: Type) (#opened: _)
  (a: array_slice t)
  (s: Ghost.erased (Seq.seq t))
  (i: U32.t)
  (sq: squash (U32.v i < Seq.length s))
  (v: t)
  (_: unit)
: STAtomicT unit opened
    (invariant a.base a.base_gr `star` pts_to a P.full_perm s)
    (fun res -> invariant a.base a.base_gr `star` pts_to a P.full_perm (Seq.upd s (U32.v i) v))
=
  rewrite
    (invariant a.base a.base_gr)
    (invariant0 a.base a.base_gr);
  rewrite
    (pts_to a P.full_perm s)
    (pts_to0 a P.full_perm s);
  let _ = gen_elim () in
  let o_r = Ghost.hide (mk_carrier (A.length a.base) (U32.v a.offset) s (P.half_perm P.full_perm)) in
  let _ = R.gather #_ #(carrier t (A.length a.base))
    a.base_gr _ (mk_carrier (A.length a.base) (U32.v a.offset) s (P.half_perm P.full_perm))
  in
  let full = vpattern_erased (fun full -> A.pts_to a.base P.full_perm full) in
  let o_l = Ghost.hide (mk_carrier (A.length a.base) 0 full (P.half_perm P.full_perm)) in
  let o = Ghost.hide (compose o_l o_r <: carrier t (A.length a.base)) in
  mk_carrier_index (A.length a.base)
    0 full (P.half_perm P.full_perm)
    (U32.v a.offset) s (P.half_perm P.full_perm)
    (U32.v a.offset + U32.v i) (U32.v i) ();
  mk_carrier_upd full
    (U32.v a.offset) s
    (U32.v i) v ();
  A.write a.base (a.offset `U32.add` i) v;
  R.upd_gen
    a.base_gr
    _ _
    (PM.lift_frame_preserving_upd
      _ _
      (P.mk_frame_preserving_upd
        (Seq.index s (U32.v i))
        v
      )
      o (U32.v a.offset + U32.v i)
    );
  R.share
    a.base_gr
    _
    (mk_carrier (A.length a.base) 0 (Seq.upd full (U32.v a.offset + U32.v i) v) (P.half_perm P.full_perm))
    (mk_carrier (A.length a.base) (U32.v a.offset) (Seq.upd s (U32.v i) v) (P.half_perm P.full_perm));
  rewrite
    (pts_to0 a P.full_perm (Seq.upd s (U32.v i) v))
    (pts_to a P.full_perm (Seq.upd s (U32.v i) v));
  assert_ (A.pts_to a.base P.full_perm (Seq.upd full (U32.v a.offset + U32.v i) v)); // FIXME: WHY WHY WHY?
  rewrite
    (invariant0 a.base a.base_gr)
    (invariant a.base a.base_gr)

inline_for_extraction
[@@noextract_to "krml"]
let atomic_write (#t:Type) (#opened: _)
         (a:array_slice t)
         (#s:Ghost.erased (Seq.seq t))
         (i:U32.t)
         (v: t)
: STAtomic (Ghost.erased (Seq.seq t)) opened
       (pts_to a P.full_perm s)
       (fun s' -> pts_to a P.full_perm s')
       (requires (
         not (mem_inv opened a.base_inv) /\ // FIXME: HOW HOW HOW to prove this precondition if atomicity is needed?
         U32.v i < length a
       ))
       (ensures fun s' ->
         U32.v i < Seq.length s /\
         Ghost.reveal s' == Seq.upd s (U32.v i) v)
= rewrite
    (pts_to a P.full_perm s)
    (pts_to0 a P.full_perm s);
  let _ = gen_elim () in
  rewrite
    (pts_to0 a P.full_perm s)
    (pts_to a P.full_perm s);
  with_invariant a.base_inv (write_body a s i () v);
  let _ = gen_elim () in
  vpattern_replace_erased (fun s' -> pts_to a P.full_perm s')

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
         U32.v i < length a
       ))
       (ensures fun s' ->
         U32.v i < Seq.length s /\
         Ghost.reveal s' == Seq.upd s (U32.v i) v)
= atomic_write a i v

let adjacent (#elt: Type) (a1 a2: array_slice elt) : Tot prop =
  a1.base == a2.base /\
  a1.base_gr == a2.base_gr /\
  a1.base_inv == a2.base_inv /\
  U32.v a1.offset + U32.v a1.length == U32.v a2.offset

inline_for_extraction
[@@noextract_to "krml"]
let merge (#elt: Type) (a1 a2: array_slice elt)
: Pure (array_slice elt)
  (requires (adjacent a1 a2))
  (ensures (fun y -> length y == length a1 + length a2))
= {
  base = a1.base;
  base_gr = a1.base_gr;
  base_inv = a1.base_inv;
  base_len = a1.base_len;
  offset = a1.offset;
  length = U32.add a1.length a2.length;
  prf = ();
}

let merge_assoc (#elt: Type) (a1 a2 a3: array_slice elt) : Lemma
  (requires (adjacent a1 a2 /\ adjacent a2 a3))
  (ensures (
    adjacent (merge a1 a2) a3 /\ adjacent a1 (merge a2 a3) /\
    merge (merge a1 a2) a3 == merge a1 (merge a2 a3)
  ))
= ()

let merge_into (#elt: Type) (a1 a2 a: array_slice elt) : Tot prop =
  adjacent a1 a2 /\
  merge a1 a2 == a

let mk_carrier_merge
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s1 s2: Seq.seq elt)
  (p: P.perm)
: Lemma
  (requires (
    offset + Seq.length s1 + Seq.length s2 <= len
  ))
  (ensures (
    let c1 = mk_carrier len offset s1 p in
    let c2 = mk_carrier len (offset + Seq.length s1) s2 p in
      composable c1 c2 /\
      mk_carrier len offset (s1 `Seq.append` s2) p `M.equal` (c1 `compose` c2)
  ))
= ()

let ghost_join
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: Seq.seq elt)
  (#p: perm)
  (a1 a2: array_slice elt)
: STGhost (Ghost.erased (array_slice elt)) opened
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun res -> pts_to res p (x1 `Seq.append` x2))
    (adjacent a1 a2)
    (fun res -> merge_into a1 a2 res)
= rewrite
    (pts_to a1 p x1)
    (pts_to0 a1 p x1);
  rewrite
    (pts_to a2 p x2)
    (pts_to0 a2 p x2);
  let _ = gen_elim () in
  mk_carrier_merge (A.length a1.base) (U32.v a1.offset) x1 x2 (P.half_perm p);
  rewrite
    (R.pts_to a2.base_gr (mk_carrier (A.length a2.base) (U32.v a2.offset) x2 (P.half_perm p)))
    (R.pts_to a1.base_gr (mk_carrier (A.length a1.base) (U32.v a1.offset + Seq.length x1) x2 (P.half_perm p)));
  R.gather a1.base_gr
    (mk_carrier (A.length a1.base) (U32.v a1.offset) x1 (P.half_perm p))
    (mk_carrier (A.length a1.base) (U32.v a1.offset + Seq.length x1) x2 (P.half_perm p));
  let res = Ghost.hide (merge a1 a2) in
  rewrite
    (R.pts_to a1.base_gr _)
    (R.pts_to res.base_gr (mk_carrier (A.length res.base) (U32.v res.offset) (x1 `Seq.append` x2) (P.half_perm p)));
  rewrite
    (pts_to0 res p (Seq.append x1 x2))
    (pts_to res p (Seq.append x1 x2));
  res

inline_for_extraction
[@@noextract_to "krml"]
let join
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: Ghost.erased (Seq.seq elt))
  (#p: perm)
  (a1 a2: array_slice elt)
: STAtomicBase (array_slice elt) false opened Unobservable
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun res -> pts_to res p (x1 `Seq.append` x2))
    (adjacent a1 a2)
    (fun res -> merge_into a1 a2 res)
= let g = ghost_join a1 a2 in
  let res = merge a1 a2 in
  rewrite
    (pts_to g p (x1 `Seq.append` x2))
    (pts_to res p (x1 `Seq.append` x2));
  return res

let mk_carrier_split
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p: P.perm)
  (i: nat)
: Lemma
  (requires (
    offset + Seq.length s <= len /\
    i <= Seq.length s
  ))
  (ensures (
    let c1 = mk_carrier len offset (Seq.slice s 0 i) p in
    let c2 = mk_carrier len (offset + i) (Seq.slice s i (Seq.length s)) p in
      composable c1 c2 /\
      mk_carrier len offset s p `M.equal` (c1 `compose` c2)
  ))
= ()

inline_for_extraction
[@@noextract_to "krml"]
let tsplit (#elt: Type) (a: array_slice elt)
  (i: U32.t)
: Pure (array_slice elt & array_slice elt)
  (requires (U32.v i <= length a))
  (ensures (fun y -> merge_into (fst y) (snd y) a))
= (
    {
      base = a.base;
      base_gr = a.base_gr;
      base_inv = a.base_inv;
      base_len = a.base_len;
      offset = a.offset;
      length = i;
      prf = ();
    }, {
      base = a.base;
      base_gr = a.base_gr;
      base_inv = a.base_inv;
      base_len = a.base_len;
      offset = a.offset `U32.add` i;
      length = a.length `U32.sub` i;
      prf = ();
    }
  )
    
#set-options "--ide_id_info_off"

let ghost_split
  (#opened: _)
  (#elt: Type)
  (#x: Seq.seq elt)
  (#p: perm)
  (a: array_slice elt)
  (i: U32.t)
: STGhost (Ghost.erased (array_slice elt & array_slice elt)) opened
    (pts_to a p x)
    (fun res -> exists_ (fun x1 -> exists_ (fun x2 ->
      pts_to (fst res) p x1 `star`
      pts_to (snd res) p x2 `star`
      pure (
        U32.v i <= length a /\
        U32.v i <= Seq.length x /\
        x1 == Seq.slice x 0 (U32.v i) /\
        x2 == Seq.slice x (U32.v i) (Seq.length x) /\
        x == x1 `Seq.append` x2 /\
        Ghost.reveal res == tsplit a i
    ))))
    (U32.v i <= length a)
    (fun _ -> True)
= rewrite
    (pts_to a p x)
    (pts_to0 a p x);
  let _ = gen_elim () in
  mk_carrier_split
    (A.length a.base)
    (U32.v a.offset)
    x
    (P.half_perm p)
    (U32.v i);
  Seq.lemma_split x (U32.v i);
  let xl = Seq.slice x 0 (U32.v i) in
  let xr = Seq.slice x (U32.v i) (Seq.length x) in
  let vl = mk_carrier (A.length a.base) (U32.v a.offset) xl (P.half_perm p) in
  let vr = mk_carrier (A.length a.base) (U32.v a.offset + U32.v i) xr (P.half_perm p) in
  R.share a.base_gr _ vl vr;
  let res = Ghost.hide (tsplit a i) in
  rewrite
    (R.pts_to a.base_gr vl)
    (R.pts_to (fst res).base_gr (mk_carrier (A.length (fst res).base) (U32.v (fst res).offset) xl (P.half_perm p)));
  rewrite
    (pts_to0 (fst res) p xl)
    (pts_to (fst res) p xl);
  rewrite
    (R.pts_to a.base_gr vr)
    (R.pts_to (snd res).base_gr (mk_carrier (A.length (snd res).base) (U32.v (snd res).offset) xr (P.half_perm p)));
  rewrite
    (pts_to0 (snd res) p xr)
    (pts_to (snd res) p xr);
  res

inline_for_extraction
[@@noextract_to "krml"]
let split
  (#opened: _)
  (#elt: Type)
  (#x: Ghost.erased (Seq.seq elt))
  (#p: perm)
  (a: array_slice elt)
  (i: U32.t)
: STAtomicBase (array_slice elt & array_slice elt) false opened Unobservable
    (pts_to a p x)
    (fun res -> exists_ (fun x1 -> exists_ (fun x2 ->
      pts_to (fst res) p x1 `star`
      pts_to (snd res) p x2 `star`
      pure (
        U32.v i <= length a /\
        U32.v i <= Seq.length x /\
        x1 == Seq.slice x 0 (U32.v i) /\
        x2 == Seq.slice x (U32.v i) (Seq.length x) /\
        Ghost.reveal x == x1 `Seq.append` x2 /\
        res == tsplit a i
    ))))
    (U32.v i <= length a)
    (fun _ -> True)
= let g = ghost_split a i in
  let _ = gen_elim () in
  let res = tsplit a i in
  let x1 = vpattern_erased (fun x1 -> pts_to (fst g) p x1) in
  rewrite
    (pts_to (fst g) p _)
    (pts_to (fst res) p x1);
  let x2 = vpattern_erased (fun x2 -> pts_to (snd g) p x2) in
  rewrite
    (pts_to (snd g) p _)
    (pts_to (snd res) p x2);
  return res
