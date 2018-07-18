module LowStar.Buffer

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module G = FStar.Ghost
module Seq = FStar.Seq

(* Most comments are taken from the Low* tutorial at:
   https://fstarlang.github.io/lowstar/html/LowStar.html
 *)

/// Low* buffers
/// ==============
///
/// The workhorse of Low*, this module allows modeling C arrays on the
/// stack and in the heap.  At compilation time, KreMLin implements
/// buffers using C arrays, i.e. if Low* type ``t`` is translated into C
/// type ``u``, then Low* type ``buffer t`` is translated to C type ``u*``.

val buffer (a: Type0) : Tot Type0


/// The C ``NULL`` pointer is represented as the Low* ``null`` buffer. For
/// any given type, there is exactly one ``null`` buffer of this type,
/// just like there is exactly one C ``NULL`` pointer of any given type.
///
/// The nullity test ``g_is_null`` is ghost, for proof purposes
/// only. The corresponding stateful nullity test is ``is_null``, see
/// below.

(* FIXME: The nullity test for proof purposes is currently expressed
   as a ghost predicate, `g_is_null`, but it is scheduled to be
   replaced with equality with `null` *)

val g_is_null (#a: Type) (b: buffer a) : GTot bool

val null (#a: Type) : Tot (b: buffer a { g_is_null b } )

val null_unique (#a: Type) (b: buffer a) : Lemma
  (g_is_null b <==> b == null)


/// ``unused_in b h`` holds only if buffer ``b`` has not been allocated
/// yet.

val unused_in (#a: Type) (b: buffer a) (h: HS.mem) : GTot Type0


/// ``live h b`` holds if, and only if, buffer ``b`` is currently
/// allocated in ``h`` and has not been deallocated yet.
///
/// This predicate corresponds to the C notion of "lifetime", and as
/// such, is a prerequisite for all stateful operations on buffers
/// (see below), per the C standard:
///
///   If an object is referred to outside of its lifetime, the
///   behavior is undefined.
/// 
///   -- ISO/IEC 9899:2011, Section 6.2.4 paragraph 2
/// 
/// By contrast, it is not required for the ghost versions of those
/// operators.

val live (#a: Type) (h: HS.mem) (b: buffer a) : GTot Type0


/// The null pointer is always live.

val live_null (a: Type) (h: HS.mem) : Lemma
  (live h (null #a))

let live_is_null (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (g_is_null b == true))
  (ensures (live h b))
  [SMTPat (live h b)]
= null_unique b;
  live_null a h


/// A live buffer has already been allocated.

val live_not_unused_in (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b /\ b `unused_in` h))
  (ensures False)

(* FIXME: the following definition is necessary to isolate the pattern
   because of unification. In other words, if we attached the pattern
   to `live_not_unused_in`, then we would not be able to use
   `FStar.Classical.forall_intro_`n and
   `FStar.Classical.move_requires` due to unification issues.  Anyway,
   we plan to isolate patterns in a separate module to clean up the Z3
   context.
 *)

let live_not_unused_in' (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b /\ b `unused_in` h))
  (ensures False)
  [SMTPat (live h b); SMTPat (b `unused_in` h)]
= live_not_unused_in h b


/// Buffers live in the HyperStack model, which is an extension of
/// the HyperHeap model, a hierarchical memory model that divides the
/// heap into a tree of regions. This coarse-grained separation
/// allows the programmer to state modifies clauses at the level of
/// regions, rather than on individual buffers.
///
/// The HyperHeap memory model is described:
///  - in the 2016 POPL paper: https://www.fstar-lang.org/papers/mumon/
///  - in the relevant section of the F* tutorial: http://www.fstar-lang.org/tutorial/
///
/// ``frameOf b`` returns the identifier of the region in which the
/// buffer ``b`` lives.

val frameOf (#a: Type) (b: buffer a) : GTot HS.rid


/// ``as_addr b`` returns the abstract address of the buffer in its
/// region, as an allocation unit: two buffers that are allocated
/// separately in the same region will actually have different
/// addresses, but a sub-buffer of a buffer will actually have the
/// same address as its enclosing buffer.

val as_addr (#a: Type) (b: buffer a) : GTot nat


/// A buffer is unused if, and only if, its address is unused.

val unused_in_equiv (#a: Type) (b: buffer a) (h: HS.mem) : Lemma
  (ensures (unused_in b h <==> (HS.live_region h (frameOf b) ==> as_addr b `Heap.addr_unused_in` (Map.sel (HS.get_hmap h) (frameOf b)))))


/// If a buffer is live, then so is its region.

val live_region_frameOf (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b))
  (ensures (HS.live_region h (frameOf b)))
  [SMTPatOr [
    [SMTPat (live h b)];
    [SMTPat (HS.live_region h (frameOf b))];
  ]]


/// The length of a buffer ``b`` is available as a machine integer ``len
/// b`` or as a mathematical integer ``length b``, but both in ghost
/// (proof) code only: just like in C, one cannot compute the length
/// of a buffer at run-time.

val len (#a: Type) (b: buffer a) : GTot U32.t

let length (#a: Type) (b: buffer a) : GTot nat = U32.v (len b)


/// The null pointer has length 0.

val len_null (a: Type) : Lemma
  (len (null #a) == 0ul)

let length_null_1 (#a: Type) (b: buffer a) : Lemma
  (requires (length b <> 0))
  (ensures (g_is_null b == false))
  [SMTPat (length b)]
= len_null a;
  null_unique b

let length_null_2 (#a: Type) (b: buffer a) : Lemma
  (requires (g_is_null b == true))
  (ensures (length b == 0))
  [SMTPat (g_is_null b)]
= len_null a;
  null_unique b


/// For functional correctness, buffers are reflected at the proof
/// level using sequences, via ``as_seq b h``, which returns the
/// contents of a given buffer ``b`` in a given heap ``h``. If ``b`` is not
/// live in ``h``, then the result is unspecified.

val as_seq (#a: Type) (h: HS.mem) (b: buffer a) : GTot (Seq.seq a)


/// The contents of a buffer ``b`` has the same length as ``b`` itself.

val length_as_seq (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (Seq.length (as_seq h b) == length b)
  [SMTPat (Seq.length (as_seq h b))]


/// ``get`` is an often-convenient shorthand to index the value of a
/// given buffer in a given heap, for proof purposes.

let get (#a: Type) (h: HS.mem) (p: buffer a) (i: nat) : Ghost a
  (requires (i < length p))
  (ensures (fun _ -> True))
= Seq.index (as_seq h p) i


/// ``gsub`` is the way to carve a sub-buffer out of a given
/// buffer. ``gsub b i len`` return the sub-buffer of ``b`` starting from
/// offset ``i`` within ``b``, and with length ``len``. Of course ``i`` and
/// ``len`` must fit within the length of ``b``.
///
/// ``gsub`` is the ghost version, for proof purposes. Its stateful
/// counterpart is ``sub``, see below.

val gsub (#a: Type) (b: buffer a) (i: U32.t) (len: U32.t) : Ghost (buffer a)
  (requires (U32.v i + U32.v len <= length b))
  (ensures (fun y -> True))

// goffset

/// A buffer is live exactly at the same time as all of its sub-buffers.

val live_gsub (#a: Type) (h: HS.mem) (b: buffer a) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (live h (gsub b i len) <==> live h b))
  [SMTPat (live h (gsub b i len))]

val gsub_is_null (#t: Type) (b: buffer t) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (g_is_null (gsub b i len) <==> g_is_null b))
  [SMTPat (g_is_null (gsub b i len))]

/// The length of a sub-buffer is exactly the one provided at ``gsub``.

val len_gsub (#a: Type) (b: buffer a) (i: U32.t) (len': U32.t) : Lemma
  (requires (U32.v i + U32.v len' <= length b))
  (ensures (len (gsub b i len') == len'))
  [SMTPatOr [
    [SMTPat (len (gsub b i len'))];
    [SMTPat (length (gsub b i len'))];
  ]]


/// Nesting two ``gsub`` collapses into one ``gsub``, transitively.

val gsub_gsub (#a: Type) (b: buffer a) (i1: U32.t) (len1: U32.t) (i2: U32.t) (len2: U32.t) : Lemma
  (requires (U32.v i1 + U32.v len1 <= length b /\ U32.v i2 + U32.v len2 <= U32.v len1))
  (ensures (
    U32.v i1 + U32.v len1 <= length b /\ U32.v i2 + U32.v len2 <= U32.v len1 /\
    gsub (gsub b i1 len1) i2 len2 == gsub b (U32.add i1 i2) len2
  ))
  [SMTPat (gsub (gsub b i1 len1) i2 len2)]


/// A buffer ``b`` is equal to its "largest" sub-buffer, at index 0 and
/// length ``len b``.

val gsub_zero_length (#a: Type) (b: buffer a) : Lemma
  (b == gsub b 0ul (len b))


/// The contents of a sub-buffer is the corresponding slice of the
/// contents of its enclosing buffer.

val as_seq_gsub (#a: Type) (h: HS.mem) (b: buffer a) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (as_seq h (gsub b i len) == Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len)))
  [SMTPat (as_seq h (gsub b i len))]


/// # The modifies clause
///
/// The modifies clause for regions, references and buffers.
/// ==========================================================
///
/// This module presents the modifies clause, a way to track the set
/// of memory locations modified by a stateful Low* (or even F*)
/// program. The basic principle of modifies clauses is that any
/// location that is disjoint from a set of memory locations modified
/// by an operation is preserved by that operation.
///
/// We start by specifying a monoid of sets of memory locations. From
/// a rough high-level view, ``loc`` is the type of sets of memory
/// locations, equipped with an identity element ``loc_none``,
/// representing the empty set, and an associative and commutative
/// operator, ``loc_union``, representing the union of two sets of
/// memory locations.
///
/// Moreover, ``loc_union`` is idempotent, which is useful to cut SMT
/// matching loops with ``modifies_trans`` and ``modifies_refl`` below.

val loc : Type0

val loc_none: loc

val loc_union
  (s1 s2: loc)
: GTot loc

val loc_union_idem
  (s: loc)
: Lemma
  (loc_union s s == s)
  [SMTPat (loc_union s s)]

val loc_union_comm
  (s1 s2: loc)
: Lemma
  (loc_union s1 s2 == loc_union s2 s1)
  [SMTPat (loc_union s1 s2)]

val loc_union_assoc
  (s1 s2 s3: loc)
: Lemma
  (loc_union s1 (loc_union s2 s3) == loc_union (loc_union s1 s2) s3)

let loc_union_idem_1
  (s1 s2: loc)
: Lemma
  (loc_union s1 (loc_union s1 s2) == loc_union s1 s2)
  [SMTPat (loc_union s1 (loc_union s1 s2) == loc_union s1 s2)]
= loc_union_assoc s1 s1 s2

let loc_union_idem_2
  (s1 s2: loc)
: Lemma
  (loc_union (loc_union s1 s2) s2 == loc_union s1 s2)
  [SMTPat (loc_union (loc_union s1 s2) s2)]
= loc_union_assoc s1 s2 s2

val loc_union_loc_none_l
  (s: loc)
: Lemma
  (loc_union loc_none s == s)
  [SMTPat (loc_union loc_none s)]

val loc_union_loc_none_r
  (s: loc)
: Lemma
  (loc_union s loc_none == s)
  [SMTPat (loc_union s loc_none)]


/// ``loc_buffer b`` is the set of memory locations associated to a buffer ``b``.

val loc_buffer
  (#t: Type)
  (b: buffer t)
: GTot loc

val loc_buffer_null
  (t: Type)
: Lemma
  (loc_buffer (null #t) == loc_none)
  [SMTPat (loc_buffer (null #t))]


/// ``loc_addresses r n`` is the set of memory locations associated to a
/// set of addresses ``n`` in a given region ``r``.

val loc_addresses
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: GTot loc

unfold
let loc_addr_of_buffer (#t: Type) (b: buffer t) : GTot loc =
  loc_addresses false (frameOf b) (Set.singleton (as_addr b))

/// ``loc_regions r`` is the set of memory locations associated to a set
/// ``r`` of regions.

val loc_regions
  (preserve_liveness: bool)
  (r: Set.set HS.rid)
: GTot loc


/// ``loc_mreference b`` is the set of memory locations associated to a
/// reference ``b``, which is actually the set of memory locations
/// associated to the address of ``b``.

unfold
let loc_mreference
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot loc
= loc_addresses true (HS.frameOf b) (Set.singleton (HS.as_addr b))

unfold
let loc_freed_mreference
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot loc
= loc_addresses false (HS.frameOf b) (Set.singleton (HS.as_addr b))


/// ``loc_region_only r`` is the set of memory locations associated to a
/// region ``r`` but not any region ``r'`` that extends ``r`` (in the sense
/// of ``FStar.HyperStack.extends``.)

unfold
let loc_region_only
  (preserve_liveness: bool)
  (r: HS.rid)
: GTot loc
= loc_regions preserve_liveness (Set.singleton r)


/// ``loc_all_regions_from r`` is the set of all memory locations
/// associated to a region ``r`` and any region ``r'`` that transitively
/// extends ``r`` (in the sense of ``FStar.HyperStack.extends``,
/// e.g. nested stack frames.)

unfold
let loc_all_regions_from
  (preserve_liveness: bool)
  (r: HS.rid)
: GTot loc
= loc_regions preserve_liveness (HS.mod_set (Set.singleton r))


/// We equip the ``loc`` monoid of sets of memory locations with an
/// inclusion relation, ``loc_includes``, which is a preorder compatible
/// with ``loc_union``. Although we consider sets of memory locations,
/// we do not specify them using any F* set library such as
/// ``FStar.Set``, ``FStar.TSet`` or ``FStar.GSet``, because ``loc_includes``
/// encompasses more than just set-theoretic inclusion.

val loc_includes
  (s1 s2: loc)
: GTot Type0

val loc_includes_refl
  (s: loc)
: Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]

val loc_includes_trans
  (s1 s2 s3: loc)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))

val loc_includes_union_r
  (s s1 s2: loc)
: Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2)))
  [SMTPat (loc_includes s (loc_union s1 s2))]

val loc_includes_union_l
  (s1 s2 s: loc)
: Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))

val loc_includes_none
  (s: loc)
: Lemma
  (loc_includes s loc_none)
  [SMTPat (loc_includes s loc_none)]


/// If a buffer ``b1`` includes a buffer ``b2`` in the sense of the buffer
/// theory (see ``LowStar.Buffer.includes``), then so are their
/// corresponding sets of memory locations.

val loc_includes_gsub_buffer_r
  (l: loc)
  (#t: Type)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= (length b) /\ loc_includes l (loc_buffer b)))
  (ensures (UInt32.v i + UInt32.v len <= (length b) /\ loc_includes l (loc_buffer (gsub b i len))))
  [SMTPat (loc_includes l (loc_buffer (gsub b i len)))]

val loc_includes_gsub_buffer_l
  (#t: Type)
  (b: buffer t)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (UInt32.v i1 + UInt32.v len1 <= (length b) /\ UInt32.v i1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1))
  (ensures (UInt32.v i1 + UInt32.v len1 <= (length b) /\ UInt32.v i1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1 /\ loc_includes (loc_buffer (gsub b i1 len1)) (loc_buffer (gsub b i2 len2))))
  [SMTPat (loc_includes (loc_buffer (gsub b i1 len1)) (loc_buffer (gsub b i2 len2)))]

/// If the contents of a buffer are equal in two given heaps, then so
/// are the contents of any of its sub-buffers.

val loc_includes_as_seq (#a: Type) (h1 h2: HS.mem) (larger smaller: buffer a) : Lemma
  (requires (loc_includes (loc_buffer larger) (loc_buffer smaller) /\ as_seq h1 larger == as_seq h2 larger /\ (live h1 larger \/ live h1 smaller) /\ (live h2 larger \/ live h2 smaller)))
  (ensures (as_seq h1 smaller == as_seq h2 smaller))


/// Given a buffer ``b``, if its address is in a set ``s`` of addresses in
/// the region of ``b``, then the set of memory locations corresponding
/// to ``b`` is included in the set of memory locations corresponding to
/// the addresses in ``s`` in region ``r``.
///
/// In particular, the set of memory locations corresponding to a
/// buffer is included in the set of memory locations corresponding to
/// its region and address.

val loc_includes_addresses_buffer
  (#t: Type)
  (preserve_liveness: bool)
  (r: HS.rid)
  (s: Set.set nat)
  (p: buffer t)
: Lemma
  (requires (frameOf p == r /\ Set.mem (as_addr p) s))
  (ensures (loc_includes (loc_addresses preserve_liveness r s) (loc_buffer p)))
  [SMTPat (loc_includes (loc_addresses preserve_liveness r s) (loc_buffer p))]


/// The set of memory locations corresponding to a buffer is included
/// in the set of memory locations corresponding to its region.

val loc_includes_region_buffer
  (#t: Type)
  (preserve_liveness: bool)
  (s: Set.set HS.rid)
  (b: buffer t)
: Lemma
  (requires (Set.mem (frameOf b) s))
  (ensures (loc_includes (loc_regions preserve_liveness s) (loc_buffer b)))
  [SMTPat (loc_includes (loc_regions preserve_liveness s) (loc_buffer b))]


/// If a region ``r`` is in a set of regions ``s``, then the set of memory
/// locations corresponding to a set of addresses ``a`` in ``r`` is
/// included in the set of memory locations corresponding to the
/// regions in ``s``.
///
/// In particular, the the set of memory locations corresponding to a
/// set of addresses ``a`` in a given region ``r`` is included in the set
/// of memory locations corresponding to region ``r``.

val loc_includes_region_addresses
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (s: Set.set HS.rid)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes (loc_regions preserve_liveness1 s) (loc_addresses preserve_liveness2 r a)))
  [SMTPat (loc_includes (loc_regions preserve_liveness1 s) (loc_addresses preserve_liveness2 r a))]

/// If a set of region identifiers ``s1`` includes a set of region
/// identifiers ``s2``, then so are their corresponding sets of memory
/// locations.

val loc_includes_region_region
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires ((preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes (loc_regions preserve_liveness1 s1) (loc_regions preserve_liveness2 s2)))
  [SMTPat (loc_includes (loc_regions preserve_liveness1 s1) (loc_regions preserve_liveness2 s2))]

/// The following lemma can act as a cut when reasoning with sets of
/// memory locations corresponding to sets of regions.

val loc_includes_region_union_l
  (preserve_liveness: bool)
  (l: loc)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (loc_includes l (loc_regions preserve_liveness (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union (loc_regions preserve_liveness s1) l) (loc_regions preserve_liveness s2)))
  [SMTPat (loc_includes (loc_union (loc_regions preserve_liveness s1) l) (loc_regions preserve_liveness s2))]


/// If a set of addresses ``s1`` includes a set of addresses ``s2``,
/// then so are their corresponding memory locations
val loc_includes_addresses_addresses
  (preserve_liveness1 preserve_liveness2: bool)
  (r: HS.rid)
  (s1 s2: Set.set nat)
: Lemma
  (requires ((preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes (loc_addresses preserve_liveness1 r s1) (loc_addresses preserve_liveness2 r s2)))

/// Patterns with loc_includes, union on the left

let loc_includes_union_l_buffer
  (s1 s2: loc)
  (#t: Type)
  (b: buffer t)
: Lemma
  (requires (loc_includes s1 (loc_buffer b) \/ loc_includes s2 (loc_buffer b)))
  (ensures (loc_includes (loc_union s1 s2) (loc_buffer b)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_buffer b))]
= loc_includes_union_l s1 s2 (loc_buffer b)

let loc_includes_union_l_addresses
  (s1 s2: loc)
  (prf: bool)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (loc_includes s1 (loc_addresses prf r a) \/ loc_includes s2 (loc_addresses prf r a)))
  (ensures (loc_includes (loc_union s1 s2) (loc_addresses prf r a)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_addresses prf r a))]
= loc_includes_union_l s1 s2 (loc_addresses prf r a)

let loc_includes_union_l_regions
  (s1 s2: loc)
  (prf: bool)
  (r: Set.set HS.rid)
: Lemma
  (requires (loc_includes s1 (loc_regions prf r) \/ loc_includes s2 (loc_regions prf r)))
  (ensures (loc_includes (loc_union s1 s2) (loc_regions prf r)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_regions prf r))]
= loc_includes_union_l s1 s2 (loc_regions prf r)

/// Since inclusion encompasses more than just set-theoretic
/// inclusion, we also need to specify disjointness accordingly, as a
/// symmetric relation compatible with union.

val loc_disjoint
  (s1 s2: loc)
: GTot Type0

val loc_disjoint_sym
  (s1 s2: loc)
: Lemma
  (requires (loc_disjoint s1 s2))
  (ensures (loc_disjoint s2 s1))

let loc_disjoint_sym'
  (s1 s2: loc)
: Lemma
  (loc_disjoint s1 s2 <==> loc_disjoint s2 s1)
  [SMTPat (loc_disjoint s1 s2)]
= Classical.move_requires (loc_disjoint_sym s1) s2;
  Classical.move_requires (loc_disjoint_sym s2) s1

val loc_disjoint_none_r
  (s: loc)
: Lemma
  (ensures (loc_disjoint s loc_none))
  [SMTPat (loc_disjoint s loc_none)]

val loc_disjoint_union_r
  (s s1 s2: loc)
: Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))


/// If two sets of memory locations are disjoint, then so are any two
/// included sets of memory locations.

val loc_disjoint_includes
  (p1 p2 p1' p2' : loc)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))

let loc_disjoint_union_r'
  (s s1 s2: loc)
: Lemma
  (ensures (loc_disjoint s (loc_union s1 s2) <==> (loc_disjoint s s1 /\ loc_disjoint s s2)))
  [SMTPat (loc_disjoint s (loc_union s1 s2))]
= Classical.move_requires (loc_disjoint_union_r s s1) s2;
  loc_includes_union_l s1 s2 s1;
  loc_includes_union_l s1 s2 s2;
  Classical.move_requires (loc_disjoint_includes s (loc_union s1 s2) s) s1;
  Classical.move_requires (loc_disjoint_includes s (loc_union s1 s2) s) s2

let loc_disjoint_includes_l (b1 b1' : loc) (b2: loc) : Lemma
  (requires (loc_includes b1 b1' /\ loc_disjoint b1 b2))
  (ensures (loc_disjoint b1' b2))
  [SMTPat (loc_disjoint b1' b2); SMTPat (loc_includes b1 b1')]
= loc_disjoint_includes b1 b2 b1' b2

let loc_disjoint_includes_r (b1 : loc) (b2 b2': loc) : Lemma
  (requires (loc_includes b2 b2' /\ loc_disjoint b1 b2))
  (ensures (loc_disjoint b1 b2'))
  [SMTPat (loc_disjoint b1 b2'); SMTPat (loc_includes b2 b2')]
= loc_disjoint_includes b1 b2 b1 b2'


val loc_disjoint_gsub_buffer
  (#t: Type)
  (b: buffer t)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 + UInt32.v len1 <= (length b) /\
    UInt32.v i2 + UInt32.v len2 <= (length b) /\ (
    UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 \/
    UInt32.v i2 + UInt32.v len2 <= UInt32.v i1
  )))
  (ensures (
    UInt32.v i1 + UInt32.v len1 <= (length b) /\
    UInt32.v i2 + UInt32.v len2 <= (length b) /\
    loc_disjoint (loc_buffer (gsub b i1 len1)) (loc_buffer (gsub b i2 len2))
  ))
  [SMTPat (loc_disjoint (loc_buffer (gsub b i1 len1)) (loc_buffer (gsub b i2 len2)))]


/// If two sets of addresses correspond to different regions or are
/// disjoint, then their corresponding sets of memory locations are
/// disjoint.

val loc_disjoint_addresses
  (preserve_liveness1 preserve_liveness2: bool)
  (r1 r2: HS.rid)
  (n1 n2: Set.set nat)
: Lemma
  (requires (r1 <> r2 \/ Set.subset (Set.intersect n1 n2) Set.empty))
  (ensures (loc_disjoint (loc_addresses preserve_liveness1 r1 n1) (loc_addresses preserve_liveness2 r2 n2)))
  [SMTPat (loc_disjoint (loc_addresses preserve_liveness1 r1 n1) (loc_addresses preserve_liveness2 r2 n2))]

/// If the region of a buffer ``p`` is not ``r``, or its address is not in
/// the set ``n`` of addresses, then their corresponding sets of memory
/// locations are disjoint.

val loc_disjoint_buffer_addresses
  (#t: Type)
  (p: buffer t)
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (requires (r <> frameOf p \/ (~ (Set.mem (as_addr p) n))))
  (ensures (loc_disjoint (loc_buffer p) (loc_addresses preserve_liveness r n)))
  [SMTPat (loc_disjoint (loc_buffer p) (loc_addresses preserve_liveness r n))]

val loc_disjoint_buffer_regions
  (#t: Type)
  (p: buffer t)
  (preserve_liveness: bool)
  (r: Set.set HS.rid)
: Lemma
  (requires (~ (frameOf p `Set.mem` r)))
  (ensures (loc_disjoint (loc_buffer p) (loc_regions preserve_liveness r)))
  [SMTPat (loc_disjoint (loc_buffer p) (loc_regions preserve_liveness r))]

/// If two sets of region identifiers are disjoint, then so are their
/// corresponding sets of memory locations.

val loc_disjoint_regions
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (rs1 rs2: Set.set HS.rid)
: Lemma
  (requires (Set.subset (Set.intersect rs1 rs2) Set.empty))
  (ensures (loc_disjoint (loc_regions preserve_liveness1 rs1) (loc_regions preserve_liveness2 rs2)))
  [SMTPat (loc_disjoint (loc_regions preserve_liveness1 rs1) (loc_regions preserve_liveness2 rs2))]


/// The modifies clauses proper.
///
/// Let ``s`` be a set of memory locations, and ``h1`` and ``h2`` be two
/// memory states. Then, ``s`` is modified from ``h1`` to ``h2`` only if,
/// any memory location disjoint from ``s`` is preserved from ``h1`` into
/// ``h2``. Elimination lemmas illustrating this principle follow.

val modifies
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0

/// If a region ``r`` is disjoint from a set ``s`` of memory locations
/// which is modified, then its liveness is preserved.

val modifies_live_region
  (s: loc)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies s h1 h2 /\ loc_disjoint s (loc_region_only false r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

/// If a reference ``b`` is disjoint from a set ``p`` of memory locations
/// which is modified, then its liveness and contents are preserved.

val modifies_mreference_elim
  (#t: Type)
  (#pre: Preorder.preorder t)
  (b: HS.mreference t pre)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_mreference b) p /\
    HS.contains h b /\
    modifies p h h'
  ))
  (ensures (
    HS.contains h' b /\
    HS.sel h b == HS.sel h' b
  ))

/// If a buffer ``b`` is disjoint from a set ``p`` of
/// memory locations which is modified, then its liveness and contents
/// are preserved.

val modifies_buffer_elim
  (#t1: Type)
  (b: buffer t1)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_buffer b) p /\
    live h b /\
    modifies p h h'
  ))
  (ensures (
    live h' b /\ (
    as_seq h b == as_seq h' b
  )))

/// If the memory state does not change, then any memory location is
/// modified (and, in particular, the empty set, ``loc_none``.)

val modifies_refl
  (s: loc)
  (h: HS.mem)
: Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]


/// If a set ``s2`` of memory locations is modified, then so is any set
/// ``s1`` that includes ``s2``. In other words, it is always possible to
/// weaken a modifies clause by widening its set of memory locations.

val modifies_loc_includes
  (s1: loc)
  (h h': HS.mem)
  (s2: loc)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))
  [SMTPat (modifies s1 h h'); SMTPat (modifies s2 h h')]

/// Some memory locations are tagged as liveness-insensitive: the
/// liveness preservation of a memory location only depends on its
/// disjointness from the liveness-sensitive memory locations of a
/// modifies clause.

val address_liveness_insensitive_locs: loc

val region_liveness_insensitive_locs: loc

val address_liveness_insensitive_buffer (#t: Type) (b: buffer t) : Lemma
  (address_liveness_insensitive_locs `loc_includes` (loc_buffer b))
  [SMTPat (address_liveness_insensitive_locs `loc_includes` (loc_buffer b))]

val address_liveness_insensitive_addresses (r: HS.rid) (a: Set.set nat) : Lemma
  (address_liveness_insensitive_locs `loc_includes` (loc_addresses true r a))
  [SMTPat (address_liveness_insensitive_locs `loc_includes` (loc_addresses true r a))]

val region_liveness_insensitive_buffer (#t: Type) (b: buffer t) : Lemma
  (region_liveness_insensitive_locs `loc_includes` (loc_buffer b))
  [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_buffer b))]

val region_liveness_insensitive_addresses (preserve_liveness: bool) (r: HS.rid) (a: Set.set nat) : Lemma
  (region_liveness_insensitive_locs `loc_includes` (loc_addresses preserve_liveness r a))
  [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_addresses preserve_liveness r a))]

val region_liveness_insensitive_regions (rs: Set.set HS.rid) : Lemma
  (region_liveness_insensitive_locs `loc_includes` (loc_regions true rs))
  [SMTPat (region_liveness_insensitive_locs `loc_includes` (loc_regions true rs))]

val region_liveness_insensitive_address_liveness_insensitive:
  squash (region_liveness_insensitive_locs `loc_includes` address_liveness_insensitive_locs)

val modifies_liveness_insensitive_mreference
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_mreference x) /\ address_liveness_insensitive_locs `loc_includes` l2 /\ h `HS.contains` x))
  (ensures (h' `HS.contains` x))
  (* TODO: pattern *)

val modifies_liveness_insensitive_buffer
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (x: buffer t)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_buffer x) /\ address_liveness_insensitive_locs `loc_includes` l2 /\ live h x))
  (ensures (live h' x))
  (* TODO: pattern *)

let modifies_liveness_insensitive_mreference_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ h `HS.contains` x))
  (ensures (h' `HS.contains` x))
= modifies_liveness_insensitive_mreference loc_none l h h' x

let modifies_liveness_insensitive_buffer_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (x: buffer t)
: Lemma
  (requires (modifies l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ live h x))
  (ensures (live h' x))
= modifies_liveness_insensitive_buffer loc_none l h h' x

val modifies_liveness_insensitive_region
  (l1 l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_region_only false x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  (* TODO: pattern *)

val modifies_liveness_insensitive_region_mreference
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_mreference x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (HS.frameOf x)))
  (ensures (HS.live_region h' (HS.frameOf x)))
  (* TODO: pattern *)

val modifies_liveness_insensitive_region_buffer
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (x: buffer t)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_buffer x) /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (frameOf x)))
  (ensures (HS.live_region h' (frameOf x)))
  (* TODO: pattern *)

let modifies_liveness_insensitive_region_weak
  (l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
= modifies_liveness_insensitive_region loc_none l2 h h' x

let modifies_liveness_insensitive_region_mreference_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (HS.frameOf x)))
  (ensures (HS.live_region h' (HS.frameOf x)))
= modifies_liveness_insensitive_region_mreference loc_none l2 h h' x

let modifies_liveness_insensitive_region_buffer_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (x: buffer t)
: Lemma
  (requires (modifies l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (frameOf x)))
  (ensures (HS.live_region h' (frameOf x)))
= modifies_liveness_insensitive_region_buffer loc_none l2 h h' x


/// Modifies clauses are transitive. This lemma is the most general
/// one.

val modifies_trans
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s23 h2 h3)]

/// Regions that are not live can be removed from sets of memory
/// locations that are modified.

val modifies_only_live_regions
  (rs: Set.set HS.rid)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions false rs) l) h h' /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))

/// As a consequence, fresh regions can be removed from modifies
/// clauses.

val no_upd_fresh_region: r:HS.rid -> l:loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (HS.fresh_region r h0 h1 /\ modifies (loc_union (loc_all_regions_from false r) l) h0 h1))
  (ensures  (modifies l h0 h1))
  [SMTPat (HS.fresh_region r h0 h1); SMTPat (modifies l h0 h1)]

val fresh_frame_modifies (h0 h1: HS.mem) : Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (modifies loc_none h0 h1))

val popped_modifies (h0 h1: HS.mem) : Lemma
  (requires (HS.popped h0 h1))
  (ensures (modifies (loc_region_only false (HS.get_tip h0)) h0 h1))

/// Stack discipline: any stack frame (and all its transitively
/// extending regions) that is pushed, modified and popped can be
/// removed from a modifies clause.

val modifies_fresh_frame_popped
  (h0 h1: HS.mem)
  (s: loc)
  (h2 h3: HS.mem)
: Lemma
  (requires (
    HS.fresh_frame h0 h1 /\
    modifies (loc_union (loc_all_regions_from false (HS.get_tip h1)) s) h1 h2 /\
    (HS.get_tip h2) == (HS.get_tip h1) /\
    HS.popped h2 h3
  ))
  (ensures (
    modifies s h0 h3 /\
    (HS.get_tip h3) == HS.get_tip h0
  ))
  [SMTPat (HS.fresh_frame h0 h1); SMTPat (HS.popped h2 h3); SMTPat (modifies s h0 h3)]

/// Compatibility lemmas to rescue modifies clauses specified in the
/// standard F* HyperStack library.

val modifies_loc_regions_intro
  (rs: Set.set HS.rid)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.modifies rs h1 h2))
  (ensures (modifies (loc_regions true rs) h1 h2))

val modifies_loc_addresses_intro
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_region_only false r) l) h1 h2 /\
    HS.modifies_ref r a h1 h2
  ))
  (ensures (modifies (loc_union (loc_addresses true r a) l) h1 h2))

/// Modifies clauses for allocating a reference: nothing is
/// modified. (In particular, a modifies clause does not track
/// memory locations that are created.)

val modifies_ralloc_post
  (#a: Type)
  (#rel: Preorder.preorder a)
  (i: HS.rid)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HST.is_eternal_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.ralloc_post i init h x h'))
  (ensures (modifies loc_none h h'))
  [SMTPat (HST.ralloc_post i init h x h')]

val modifies_salloc_post
  (#a: Type)
  (#rel: Preorder.preorder a)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HS.is_stack_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.salloc_post init h x h'))
  (ensures (modifies loc_none h h'))
  [SMTPat (HST.salloc_post init h x h')]

/// Modifies clause for freeing a reference: the address is modified.

val modifies_free
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel { HS.is_mm r } )
  (m: HS.mem { m `HS.contains` r } )
: Lemma
  (modifies (loc_freed_mreference r) m (HS.free r m))
  [SMTPat (HS.free r m)]

/// Another compatibility lemma

val modifies_none_modifies
  (h1 h2: HS.mem)
: Lemma
  (requires (HST.modifies_none h1 h2))
  (ensures (modifies loc_none h1 h2))
  [SMTPat (HST.modifies_none h1 h2)]

/// Compatibility with HS.upd

val modifies_upd
  (#t: Type) (#pre: Preorder.preorder t)
  (r: HS.mreference t pre)
  (v: t)
  (h: HS.mem)
: Lemma
  (requires (HS.contains h r))
  (ensures (modifies (loc_mreference r) h (HS.upd h r v)))
  [SMTPat (HS.upd h r v)]

///  A memory ``h`` does not contain address ``a`` in region ``r``, denoted
///  ``does_not_contain_addr h (r, a)``, only if, either region ``r`` is
///  not live, or address ``a`` is unused in region ``r``.

(* BEGIN TODO: move to FStar.Monotonic.HyperStack *)

val does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid * nat)
: GTot Type0

val not_live_region_does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid * nat)
: Lemma
  (requires (~ (HS.live_region h (fst ra))))
  (ensures (h `does_not_contain_addr` ra))

val unused_in_does_not_contain_addr
  (h: HS.mem)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (h `does_not_contain_addr` (HS.frameOf r, HS.as_addr r)))

val addr_unused_in_does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid * nat)
: Lemma
  (requires (HS.live_region h (fst ra) ==> snd ra `Heap.addr_unused_in` (Map.sel (HS.get_hmap h) (fst ra))))
  (ensures (h `does_not_contain_addr` ra))

val free_does_not_contain_addr
  (#a: Type0)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
  (m: HS.mem)
  (x: HS.rid * nat)
: Lemma
  (requires (
    HS.is_mm r /\
    m `HS.contains` r /\
    fst x == HS.frameOf r /\
    snd x == HS.as_addr r
  ))
  (ensures (
    HS.free r m `does_not_contain_addr` x
  ))
  [SMTPat (HS.free r m `does_not_contain_addr` x)]

val does_not_contain_addr_elim
  (#a: Type0)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
  (m: HS.mem)
  (x: HS.rid * nat)
: Lemma
  (requires (
    m `does_not_contain_addr` x /\
    HS.frameOf r == fst x /\
    HS.as_addr r == snd x
  ))
  (ensures (~ (m `HS.contains` r)))

(** END TODO *)

/// Addresses that have not been allocated yet can be removed from
/// modifies clauses.

val modifies_only_live_addresses
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_addresses false r a) l) h h' /\
    (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x))
  ))
  (ensures (modifies l h h'))


(* Generic way to ensure that a buffer just allocated is disjoint from
   any other object, however the latter's liveness is defined. *)

val loc_not_unused_in (h: HS.mem) : GTot loc

val loc_unused_in (h: HS.mem) : GTot loc

val loc_unused_in_not_unused_in_disjoint (h: HS.mem) : Lemma
  (loc_disjoint (loc_unused_in h) (loc_not_unused_in h))

val live_loc_not_unused_in (#t: Type) (b: buffer t) (h: HS.mem) : Lemma
  (requires (live h b))
  (ensures (loc_not_unused_in h `loc_includes` loc_buffer b))
  [SMTPat (live h b)]

val unused_in_loc_unused_in (#t: Type) (b: buffer t) (h: HS.mem) : Lemma
  (requires (unused_in b h))
  (ensures (loc_unused_in h `loc_includes` loc_buffer b))
  [SMTPat (unused_in b h)]

val modifies_address_liveness_insensitive_unused_in
  (h h' : HS.mem)
: Lemma
  (requires (modifies (address_liveness_insensitive_locs) h h'))
  (ensures (loc_not_unused_in h' `loc_includes` loc_not_unused_in h /\ loc_unused_in h `loc_includes` loc_unused_in h'))

val mreference_live_loc_not_unused_in
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (h `HS.contains` r))
  (ensures (loc_not_unused_in h `loc_includes` loc_freed_mreference r /\ loc_not_unused_in h `loc_includes` loc_mreference r))
  [SMTPat (HS.contains h r)]

val mreference_unused_in_loc_unused_in
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (loc_unused_in h `loc_includes` loc_freed_mreference r /\ loc_unused_in h `loc_includes` loc_mreference r))
  [SMTPat (HS.unused_in r h)]


let unused_in_not_unused_in_disjoint_2
  (l1 l2 l1' l2': loc)
  (h: HS.mem)
: Lemma
  (requires (loc_unused_in h `loc_includes` l1 /\ loc_not_unused_in h `loc_includes` l2 /\ l1 `loc_includes` l1' /\ l2 `loc_includes` l2' ))
  (ensures (loc_disjoint l1'  l2' ))
  [SMTPat (loc_disjoint l1' l2'); SMTPat (loc_unused_in h `loc_includes` l1); SMTPat (loc_not_unused_in h `loc_includes` l2); SMTPat (l1 `loc_includes` l1') ; SMTPat (l2 `loc_includes` l2' )]
= loc_includes_trans (loc_unused_in h) l1 l1' ;
  loc_includes_trans (loc_not_unused_in h) l2 l2'  ;
  loc_unused_in_not_unused_in_disjoint h ;
  loc_disjoint_includes (loc_unused_in h) (loc_not_unused_in h) l1' l2' 

let unused_in_not_unused_in_disjoint_1
  (l1 l2 l1'  : loc)
  (h: HS.mem)
: Lemma
  (requires (
    loc_unused_in h `loc_includes` l1 /\
    loc_not_unused_in h `loc_includes` l2 /\
    l1 `loc_includes` l1' 
  ))
  (ensures (l1' `loc_disjoint` l2))
  [SMTPat (loc_disjoint l1' l2); SMTPat (loc_unused_in h `loc_includes` l1); SMTPat (loc_not_unused_in h `loc_includes` l2)]
= assert (loc_includes l2 l2)

let unused_in_not_unused_in_disjoint_0
  (l1 l2: loc)
  (h: HS.mem)
: Lemma
  (requires (loc_unused_in h `loc_includes` l1 /\ loc_not_unused_in h `loc_includes` l2))
  (ensures (loc_disjoint l1 l2))
  [SMTPat (loc_disjoint l1 l2); SMTPat (loc_unused_in h `loc_includes` l1); SMTPat (loc_not_unused_in h `loc_includes` l2)]
= assert (loc_includes l1 l1);
  assert (loc_includes l2 l2)



(* Duplicate the modifies clause to cope with cases that must not be used with transitivity *)

abstract
let modifies_inert
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= modifies s h1 h2

abstract
let modifies_inert_intro
  (s: loc)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies s h1 h2))
  (ensures (modifies_inert s h1 h2))
  [SMTPat (modifies s h1 h2)]
= ()

let modifies_inert_live_region
  (s: loc)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies_inert s h1 h2 /\ loc_disjoint s (loc_region_only false r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))
  [SMTPatOr [
    [SMTPat (modifies_inert s h1 h2); SMTPat (HS.live_region h1 r)];
    [SMTPat (modifies_inert s h1 h2); SMTPat (HS.live_region h2 r)];
  ]]
= modifies_live_region s h1 h2 r

let modifies_inert_mreference_elim
  (#t: Type)
  (#pre: Preorder.preorder t)
  (b: HS.mreference t pre)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_mreference b) p /\
    HS.contains h b /\
    modifies_inert p h h'
  ))
  (ensures (
    HS.contains h' b /\
    HS.sel h b == HS.sel h' b
  ))
  [SMTPatOr [
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.sel h b) ] ;
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.contains h b) ];
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.sel h' b) ] ;
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.contains h' b) ]
  ] ]
= modifies_mreference_elim b p h h'

let modifies_inert_buffer_elim
  (#t1: Type)
  (b: buffer t1)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_buffer b) p /\
    live h b /\
    modifies_inert p h h'
  ))
  (ensures (
    live h' b /\ (
    as_seq h b == as_seq h' b
  )))
  [SMTPatOr [
    [ SMTPat (modifies_inert p h h'); SMTPat (as_seq h b) ] ;
    [ SMTPat (modifies_inert p h h'); SMTPat (live h b) ];
    [ SMTPat (modifies_inert p h h'); SMTPat (as_seq h' b) ] ;
    [ SMTPat (modifies_inert p h h'); SMTPat (live h' b) ]
  ] ]
= modifies_buffer_elim b p h h'

let modifies_inert_liveness_insensitive_mreference_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies_inert l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ h `HS.contains` x))
  (ensures (h' `HS.contains` x))
  [SMTPatOr [
    [SMTPat (h `HS.contains` x); SMTPat (modifies_inert l h h');];
    [SMTPat (h' `HS.contains` x); SMTPat (modifies_inert l h h');];
  ]]
= modifies_liveness_insensitive_mreference_weak l h h' x

let modifies_inert_liveness_insensitive_buffer_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (x: buffer t)
: Lemma
  (requires (modifies_inert l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ live h x))
  (ensures (live h' x))
  [SMTPatOr [
    [SMTPat (live h x); SMTPat (modifies_inert l h h');];
    [SMTPat (live h' x); SMTPat (modifies_inert l h h');];
  ]]
= modifies_liveness_insensitive_buffer_weak l h h' x

let modifies_inert_liveness_insensitive_region_weak
  (l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies_inert l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  [SMTPatOr [
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h x)];
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h' x)];
  ]]
= modifies_liveness_insensitive_region_weak l2 h h' x

let modifies_inert_liveness_insensitive_region_mreference_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies_inert l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (HS.frameOf x)))
  (ensures (HS.live_region h' (HS.frameOf x)))
  [SMTPatOr [
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h (HS.frameOf x))];
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h' (HS.frameOf x))];
  ]]
= modifies_liveness_insensitive_region_mreference_weak l2 h h' x

let modifies_inert_liveness_insensitive_region_buffer_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (x: buffer t)
: Lemma
  (requires (modifies_inert l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (frameOf x)))
  (ensures (HS.live_region h' (frameOf x)))
  [SMTPatOr [
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h (frameOf x))];
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h' (frameOf x))];
  ]]
= modifies_liveness_insensitive_region_buffer_weak l2 h h' x

let fresh_frame_modifies_inert
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (modifies_inert loc_none h0 h1))
  [SMTPat (HS.fresh_frame h0 h1)]
= fresh_frame_modifies h0 h1

let popped_modifies_inert
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.popped h0 h1))
  (ensures (modifies_inert (loc_region_only false (HS.get_tip h0)) h0 h1))
  [SMTPat (HS.popped h0 h1)]
= popped_modifies h0 h1

let modifies_inert_loc_unused_in
  (l: loc)
  (h1 h2: HS.mem)
  (l' : loc)
: Lemma
  (requires (
    modifies_inert l h1 h2 /\
    address_liveness_insensitive_locs `loc_includes` l /\
    loc_unused_in h2 `loc_includes` l'
  ))
  (ensures (loc_unused_in h1 `loc_includes` l'))
  [SMTPat (modifies_inert l h1 h2); SMTPat (loc_unused_in h2 `loc_includes` l')]
= modifies_loc_includes address_liveness_insensitive_locs h1 h2 l;
  modifies_address_liveness_insensitive_unused_in h1 h2;
  loc_includes_trans (loc_unused_in h1) (loc_unused_in h2) l'


/// Legacy shorthands for disjointness and inclusion of buffers
///
let disjoint (#t1 #t2: Type) (b1: buffer t1) (b2: buffer t2) : GTot Type0 =
  loc_disjoint (loc_buffer b1) (loc_buffer b2)

let includes (#t: Type) (b1 b2: buffer t) : GTot Type0 =
  loc_includes (loc_buffer b1) (loc_buffer b2) /\
  (g_is_null b1 <==> g_is_null b2)

val disjoint_neq (#a1 #a2: Type) (b1 : buffer a1) (b2 : buffer a2) : Lemma
  (requires (disjoint b1 b2 /\ U32.v (len b1) > 0))
  (ensures (~(b1 === b2)))

/// The liveness of a sub-buffer is exactly equivalent to the liveness
/// of its enclosing buffer.

val includes_live (#a: Type) (h: HS.mem) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (live h larger <==> live h smaller))
  [SMTPatOr [
    [SMTPat (includes larger smaller); SMTPat (live h larger)];
    [SMTPat (includes larger smaller); SMTPat (live h smaller)];
  ]]

val includes_frameOf_as_addr (#a: Type) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (g_is_null larger == g_is_null smaller /\ frameOf larger == frameOf smaller /\ as_addr larger == as_addr smaller))
  [SMTPat (larger `includes` smaller)]
/// 
/// Useful shorthands for pointers, or maybe-null pointers

inline_for_extraction
type pointer (t: Type0) =
  b:buffer t { length b == 1 }

inline_for_extraction
type pointer_or_null (t: Type0) =
  b:buffer t { if g_is_null b then True else length b == 1 }

unfold
let deref #a (h: HS.mem) (x: pointer a) =
  get h x 0

/// Two pointers having different contents are disjoint. This is valid
/// only for pointers, i.e. buffers of size 1.

val pointer_distinct_sel_disjoint
  (#a: Type)
  (b1: pointer a)
  (b2: pointer a)
  (h: HS.mem)
: Lemma
  (requires (
    live h b1 /\
    live h b2 /\
    get h b1 0 =!= get h b2 0
  ))
  (ensures (
    disjoint b1 b2
  ))


/// The following stateful operations on buffers do not change the
/// memory, but, as required by the C standard, they all require the
/// buffer in question to be live.

/// The nullity test, ``is_null b``, which KreMLin compiles to C as ``b == NULL``.

val is_null (#a: Type) (b: buffer a) : HST.Stack bool
  (requires (fun h -> live h b))
  (ensures (fun h y h' -> h == h' /\ y == g_is_null b))


/// ``sub b i len`` constructs the sub-buffer of ``b`` starting from
/// offset ``i`` with length ``len``. KreMLin extracts this operation as
/// ``b + i`` (or, equivalently, ``&b[i]``.)

val sub (#a: Type) (b: buffer a) (i: U32.t) (len: U32.t) : HST.Stack (buffer a)
  (requires (fun h -> U32.v i + U32.v len <= length b /\ live h b))
  (ensures (fun h y h' -> h == h' /\ y == gsub b i len))


/// ``offset b i`` construct the tail of the buffer ``b`` starting from
/// offset ``i``, i.e. the sub-buffer of ``b`` starting from offset ``i``
/// with length ``U32.sub (len b) i``. KreMLin compiles it as ``b + i`` or
/// ``&b[i]``.
///
/// This stateful operation cannot be derived from ``sub``, because the
/// length cannot be computed outside of proofs.

val offset (#a: Type) (b: buffer a) (i: U32.t) : HST.Stack (buffer a)
  (requires (fun h -> U32.v i <= length b /\ live h b))
  (ensures (fun h y h' -> h == h' /\ y == gsub b i (U32.sub (len b) i)))
// goffset


/// ``index b i`` reads the value of ``b`` at offset ``i`` from memory and
/// returns it. KreMLin compiles it as b[i].
val index (#a: Type) (b: buffer a) (i: U32.t) : HST.Stack a
  (requires (fun h -> live h b /\ U32.v i < length b))
  (ensures (fun h y h' -> h == h' /\ y == Seq.index (as_seq h b) (U32.v i)))


/// The following stateful operations on buffers modify the memory,
/// and, as usual, require the liveness of the buffer.

/// ``g_upd_seq b s h`` updates the entire buffer `b`'s contents in
/// heap `h` to correspond to the sequence `s`
val g_upd_seq (#a:Type)
              (b:buffer a)
              (s:Seq.lseq a (length b))
              (h:HS.mem{live h b})
  : GTot HS.mem

/// A lemma specifying `g_upd_seq` in terms of its effect on the
/// buffer's underlying sequence
val g_upd_seq_as_seq (#a:Type)
                     (b:buffer a)
                     (s:Seq.lseq a (length b))
                     (h:HS.mem{live h b})
  : Lemma (let h' = g_upd_seq b s h in
           modifies (loc_buffer b) h h' /\
           live h' b /\
           as_seq h' b == s)

/// ``g_upd b i v h`` updates the buffer `b` in heap `h` at location
/// `i` writing ``v`` there. This is the spec analog of the stateful
/// update `upd` below.
let g_upd (#a:Type)
          (b:buffer a)
          (i:nat{i < length b})
          (v:a)
          (h:HS.mem{live h b})
  : GTot HS.mem
  = g_upd_seq b (Seq.upd (as_seq h b) i v) h
            
/// ``upd b i v`` writes ``v`` to the memory, at offset ``i`` of
/// buffer ``b``. KreMLin compiles it as ``b[i] = v``.
val upd
  (#a: Type)
  (b: buffer a)
  (i: U32.t)
  (v: a)
: HST.Stack unit
  (requires (fun h -> live h b /\ U32.v i < length b))
  (ensures (fun h _ h' ->
    (not (g_is_null b)) /\
    modifies (loc_buffer b) h h' /\
    live h' b /\
    as_seq h' b == Seq.upd (as_seq h b) (U32.v i) v
  ))

(* FIXME: Comment on `recall` *)

val recallable (#a: Type) (b: buffer a) : GTot Type0

val recallable_includes (#a: Type) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (recallable larger <==> recallable smaller))
  [SMTPatOr [
    [SMTPat (recallable larger); SMTPat (recallable smaller);];
    [SMTPat (larger `includes` smaller)];
  ]]

val recall
  (#a:Type)
  (b:buffer a)
: HST.Stack unit
  (requires (fun _ -> recallable b))
  (ensures  (fun m0 _ m1 -> m0 == m1 /\ live m1 b))


/// Deallocation. A buffer that was allocated by ``malloc`` (see below)
/// can be ``free`` d.

val freeable (#a: Type) (b: buffer a) : GTot Type0

val free
  (#a: Type)
  (b: buffer a)
: HST.ST unit
  (requires (fun h0 -> live h0 b /\ freeable b))
  (ensures (fun h0 _ h1 ->
    (not (g_is_null b)) /\
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\ 
    (HS.get_tip h1) == (HS.get_tip h0) /\
    modifies (loc_addr_of_buffer b) h0 h1 /\
    HS.live_region h1 (frameOf b)
  ))

/// Allocation. This is the common postcondition of all allocation
/// operators, which tells that the resulting buffer is fresh, and
/// specifies its initial contents.

unfold
let alloc_post_static
  (#a: Type)
  (r: HS.rid)
  (len: nat)
  (b: buffer a)
: GTot Type0
= (not (g_is_null b)) /\
  frameOf b == r /\
  length b == len

unfold
let alloc_post_common
  (#a: Type)
  (r: HS.rid)
  (len: nat)
  (b: buffer a)
  (h0 h1: HS.mem)
: GTot Type0
= alloc_post_static r len b /\
  b `unused_in` h0 /\
  live h1 b /\
  Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\ 
  (HS.get_tip h1) == (HS.get_tip h0) /\
  modifies loc_none h0 h1

/// ``gcmalloc r init len`` allocates a memory-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer cannot be
/// freed. In fact, it is eternal: it cannot be deallocated at all.

val gcmalloc
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: U32.t)
: HST.ST (b: buffer a {
    recallable b /\
    alloc_post_static r (U32.v len) b
  } )
  (requires (fun h -> HST.is_eternal_region r /\ U32.v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common r (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init
  ))


/// ``malloc r init len`` allocates a hand-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer can be
/// freed using ``free`` above. Note that the ``freeable`` permission is
/// only on the whole buffer ``b``, and is not inherited by any of its
/// strict sub-buffers.

val malloc
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: U32.t)
: HST.ST (buffer a)
  (requires (fun h -> HST.is_eternal_region r /\ U32.v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common r (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init /\     
    freeable b
  ))


/// ``alloca init len`` allocates a buffer of some positive length ``len``
/// in the current stack frame. Every cell of this buffer will have
/// initial contents ``init``. Such a buffer cannot be freed
/// individually, but is automatically freed as soon as its stack
/// frame is deallocated by ``HST.pop_frame``.

val alloca
  (#a: Type)
  (init: a)
  (len: U32.t)
: HST.StackInline (buffer a)
  (requires (fun h -> U32.v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common (HS.get_tip h) (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init
  ))


/// ``alloca_of_list init`` allocates a buffer in the current stack
/// frame. The initial values of the cells of this buffer are
/// specified by the ``init`` list, which must be nonempty, and of
/// length representable as a machine integer.

unfold let alloc_of_list_pre (#a: Type0) (init: list a) : GTot Type0 =
  normalize (0 < FStar.List.Tot.length init) /\
  normalize (FStar.List.Tot.length init <= UInt.max_int 32)

unfold let alloc_of_list_post (#a: Type) (len: nat) (buf: buffer a) : GTot Type0 =
  normalize (length buf == len)

val alloca_of_list
  (#a: Type0)
  (init: list a)
: HST.StackInline (buffer a)
  (requires (fun h -> alloc_of_list_pre #a init))
  (ensures (fun h b h' ->
    let len = FStar.List.Tot.length init in
    alloc_post_common (HS.get_tip h) len b h h' /\
    as_seq h' b == Seq.of_list init /\
    alloc_of_list_post #a len b
  ))

val gcmalloc_of_list
  (#a: Type0)
  (r: HS.rid)
  (init: list a)
: HST.ST (b: buffer a {
    let len = FStar.List.Tot.length init in
    recallable b /\
    alloc_post_static r len b /\
    alloc_of_list_post len b
  } )
  (requires (fun h -> HST.is_eternal_region r /\ alloc_of_list_pre #a init))
  (ensures (fun h b h' ->
    let len = FStar.List.Tot.length init in
    alloc_post_common r len b h h' /\
    as_seq h' b == Seq.of_list init
  ))

/// Derived operations

#set-options "--z3rlimit 16" // necessary here because of interleaving blit with the .fst file

let rec blit
  (#t: Type)
  (src: buffer t)
  (idx_src: U32.t)
  (dst: buffer t)
  (idx_dst: U32.t)
  (len: U32.t)
: HST.Stack unit
  (requires (fun h ->
    live h src /\ live h dst /\ disjoint src dst /\
    U32.v idx_src + U32.v len <= length src /\
    U32.v idx_dst + U32.v len <= length dst
  ))
  (ensures (fun h _ h' ->
    modifies (loc_buffer dst) h h' /\
    live h' dst /\
    Seq.slice (as_seq h' dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len) ==
    Seq.slice (as_seq h src) (U32.v idx_src) (U32.v idx_src + U32.v len) /\
    Seq.slice (as_seq h' dst) 0 (U32.v idx_dst) ==
    Seq.slice (as_seq h dst) 0 (U32.v idx_dst) /\
    Seq.slice (as_seq h' dst) (U32.v idx_dst + U32.v len) (length dst) ==
    Seq.slice (as_seq h dst) (U32.v idx_dst + U32.v len) (length dst)
  ))
= let h0 = HST.get () in
  if len = 0ul then ()
  else begin
    let len' = U32.(len -^ 1ul) in
    blit #t src idx_src dst idx_dst len';
    let z = U32.(index src (idx_src +^ len')) in
    upd dst (U32.(idx_dst +^ len')) z;
    let h1 = HST.get() in
    Seq.snoc_slice_index (as_seq h1 dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len');
    Seq.cons_head_tail (Seq.slice (as_seq h0 dst) (U32.v idx_dst + U32.v len') (length dst));
    Seq.cons_head_tail (Seq.slice (as_seq h1 dst) (U32.v idx_dst + U32.v len') (length dst))
  end

#set-options "--z3rlimit 16" // necessary here because of assign_list in the .fsti itself

module L = FStar.List.Tot

inline_for_extraction
let rec assign_list #a (l: list a) (b: buffer a): HST.Stack unit
  (requires (fun h0 ->
    live h0 b /\
    length b = L.length l))
  (ensures (fun h0 _ h1 ->
    live h1 b /\
    (modifies (loc_buffer b) h0 h1) /\
    as_seq h1 b == Seq.seq_of_list l))
=
  match l with
  | [] -> 
      let h = HST.get () in
      assert (length b = 0);
      assert (Seq.length (as_seq h b) = 0);
      assert (Seq.equal (as_seq h b) (Seq.empty #a));
      assert (Seq.seq_of_list [] `Seq.equal` Seq.empty #a)
  | hd :: tl ->
      let b_hd = sub b 0ul 1ul in
      let b_tl = offset b 1ul in
      let h = HST.get () in
      upd b_hd 0ul hd;
      let h0 = HST.get () in
      assign_list tl b_tl;
      let h1 = HST.get () in
      assert (as_seq h1 b_hd == as_seq h0 b_hd);
      assert (get h1 b_hd 0 == hd);
      assert (as_seq h1 b_tl == Seq.seq_of_list tl);
      assert (Seq.equal (as_seq h1 b) (Seq.append (as_seq h1 b_hd) (as_seq h1 b_tl)));
      assert ((Seq.seq_of_list l) == (Seq.cons hd (Seq.seq_of_list tl)))

#reset-options


/// Type class instantiation for compositionality with other kinds of memory locations than regions, references or buffers (just in case).
/// No usage pattern has been found yet.

module MG = FStar.ModifiesGen

val abuffer' (region: HS.rid) (addr: nat) : Tot Type0

inline_for_extraction
let abuffer (region: HS.rid) (addr: nat) : Tot Type0 = G.erased (abuffer' region addr)

val cloc_cls: MG.cls abuffer

val cloc_of_loc (l: loc) : Tot (MG.loc cloc_cls)

val loc_of_cloc (l: MG.loc cloc_cls) : Tot loc

val loc_of_cloc_of_loc (l: loc) : Lemma
  (loc_of_cloc (cloc_of_loc l) == l)
  [SMTPat (loc_of_cloc (cloc_of_loc l))]

val cloc_of_loc_of_cloc (l: MG.loc cloc_cls) : Lemma
  (cloc_of_loc (loc_of_cloc l) == l)
  [SMTPat (cloc_of_loc (loc_of_cloc l))]

val cloc_of_loc_none: unit -> Lemma (cloc_of_loc loc_none == MG.loc_none)

val cloc_of_loc_union (l1 l2: loc) : Lemma
  (cloc_of_loc (loc_union l1 l2) == MG.loc_union (cloc_of_loc l1) (cloc_of_loc l2))

val cloc_of_loc_addresses
  (preserve_liveness: bool)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (cloc_of_loc (loc_addresses preserve_liveness r n) == MG.loc_addresses preserve_liveness r n)

val cloc_of_loc_regions
  (preserve_liveness: bool)
  (r: Set.set HS.rid)
: Lemma
  (cloc_of_loc (loc_regions preserve_liveness r) == MG.loc_regions preserve_liveness r)

val loc_includes_to_cloc (l1 l2: loc) : Lemma
  (loc_includes l1 l2 <==> MG.loc_includes (cloc_of_loc l1) (cloc_of_loc l2))

val loc_disjoint_to_cloc (l1 l2: loc) : Lemma
  (loc_disjoint l1 l2 <==> MG.loc_disjoint (cloc_of_loc l1) (cloc_of_loc l2))

val modifies_to_cloc (l: loc) (h1 h2: HS.mem) : Lemma
  (modifies l h1 h2 <==> MG.modifies (cloc_of_loc l) h1 h2)
