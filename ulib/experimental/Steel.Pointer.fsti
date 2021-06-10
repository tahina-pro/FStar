module Steel.Pointer

(* An interface for C pointers and pointer arithmetic for C arrays. *)

open Steel.Memory
open Steel.FractionalPermission
open Steel.Effect
open Steel.Effect.Atomic
module U32 = FStar.UInt32

val size_t : Type0

val reveal_size_t : unit -> Lemma (size_t == U32.t)

unfold
let coerce (#a: Type) (x: a) (b: Type) : Pure b (requires (a == b)) (ensures (fun y -> a == b /\ x == y)) = x

let size_v (x: size_t) : GTot nat =
  reveal_size_t ();
  U32.v (coerce x U32.t)

val ptrdiff_t : Type0

module I32 = FStar.Int32

val reveal_ptrdiff_t : unit -> Lemma (ptrdiff_t == I32.t)

let ptrdiff_v (x: ptrdiff_t) : GTot int =
  reveal_ptrdiff_t ();
  I32.v (coerce x I32.t)

val ptrdiff_precond (x: int) : Tot prop

val reveal_ptrdiff_precond (x: int) : Lemma (ptrdiff_precond x <==> FStar.Int.size x I32.n)

val mk_ptrdiff (x: int) : Ghost ptrdiff_t
  (requires (ptrdiff_precond x))
  (ensures (fun y -> ptrdiff_v y == x))

[@@erasable]
val base_array (a: Type0) : Tot Type0

val base_array_len
  (#a: Type0)
  (b: base_array a)
: GTot size_t

val base_array_freeable
  (#a: Type0)
  (b: base_array a)
: Tot prop

val t (a: Type0) : Tot Type0

val null (a: Type0) : Tot (t a)

val g_is_null (#a: Type0) (p: t a) : Ghost bool
  (requires True)
  (ensures (fun res -> res == true <==> p == null a))

val base
  (#a: Type0)
  (p: t a)
: Pure (base_array a)
  (requires (g_is_null p == false))
  (ensures (fun _ -> True))

val offset
  (#a: Type0)
  (p: t a)
: Ghost size_t
  (requires (g_is_null p == false))
  (ensures (fun res ->
    size_v res <= size_v (base_array_len (base p))
  ))

val base_offset_inj
  (#a: Type0)
  (p1 p2: t a)
: Lemma
  (requires (g_is_null p1 == false /\ g_is_null p2 == false /\ base p1 == base p2 /\ offset p1 == offset p2))
  (ensures (p1 == p2))

val g_add
  (#a: Type0)
  (p: t a)
  (off: size_t)
: Ghost (t a)
  (requires (g_is_null p == false /\ size_v (offset p) + size_v off <= size_v (base_array_len (base p))))
  (ensures (fun res ->
    g_is_null res == false /\
    base res == base p /\
    size_v (offset res) == size_v (offset p) + size_v off
  ))

val g_sub
  (#a: Type0)
  (p: t a)
  (off: size_t)
: Ghost (t a)
  (requires (g_is_null p == false /\ size_v (offset p) >= size_v off))
  (ensures (fun res ->
    g_is_null res == false /\
    base res == base p /\
    size_v (offset res) == size_v (offset p) - size_v off
  ))

let g_le
  (#a: Type0)
  (p1 p2: t a)
: Tot prop
= g_is_null p1 == false /\
  g_is_null p2 == false /\
  base p1 == base p2 /\
  size_v (offset p1) <= size_v (offset p2)

let g_diff
  (#a: Type0)
  (p1 p2: t a)
: Ghost ptrdiff_t
  (requires (g_is_null p1 == false /\ g_is_null p2 == false /\ base p1 == base p2 /\ ptrdiff_precond (size_v (offset p2) - size_v (offset p1))))
  (ensures (fun _ -> True))
=
  mk_ptrdiff (size_v (offset p2) - size_v (offset p1))

[@@erasable]
noeq
type range = {
  range_from: int;
  range_to: int;
  range_prf: squash (range_from <= 0 /\ 0 <= range_to);
}

val slptr_range
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
: Tot (slprop u#1)

val ptr_select
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
: Tot (selector (Seq.lseq a (r.range_to - r.range_from)) (slptr_range x r p))

[@@ __steel_reduce__ ]
let vptr_range'
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
: Tot vprop'
= {
  hp = slptr_range x r p;
  t = Seq.lseq a (r.range_to - r.range_from);
  sel = ptr_select x r p;
}

[@@ __steel_reduce__ ]
let vptr_range
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
: Tot vprop
= VUnit (vptr_range' x r p)

val vptr_range_not_null
  (#opened: _)
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
: SteelGhost unit opened
    (vptr_range x r p)
    (fun _ -> vptr_range x r p)
    (fun _ -> True)
    (fun h _ h' ->
      h' (vptr_range x r p) == h (vptr_range x r p) /\
      g_is_null x == false
    )

let mk_range
  (from: int)
  (to: int)
: Pure range
  (requires (from <= 0 /\ 0 <= to))
  (ensures (fun _ -> True))
= {
  range_from = from;
  range_to = to;
  range_prf = ();
}

[@@ __steel_reduce__]
unfold
let ptr_sel (#a:Type) (#p:vprop) (#r: range) (#prm: perm) (x: t a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vptr_range x r prm)) /\ r.range_from == 0 /\ r.range_to == 1})
: GTot a 
= Seq.index (h (vptr_range x r prm)) 0

[@@ __steel_reduce__]
unfold
let ptr_sel0 (#a:Type) (#p:vprop) (r: range) (prm: perm) (x: t a)
  (h:rmem p{ (can_be_split p (vptr_range x r prm)) /\ r.range_from == 0 /\ r.range_to == 1})
: GTot a 
= Seq.index (h (vptr_range x r prm)) 0

let vptr_range_or_null
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
: Tot vprop
= if g_is_null x then emp else vptr_range x r p

val is_null
  (#opened: _)
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
: SteelAtomic bool opened
    (vptr_range_or_null x r p)
    (fun _ -> vptr_range_or_null x r p)
    (fun _ -> True)
    (fun h res h' ->
      h' (vptr_range_or_null x r p) == h (vptr_range_or_null x r p) /\
      res == g_is_null x
    )

let assert_null
  (#opened: _)
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
: SteelGhost unit opened
    (vptr_range_or_null x r p)
    (fun _ -> emp)
    (fun _ -> g_is_null x == true)
    (fun _ _ _ -> True)
=
  change_equal_slprop
    (vptr_range_or_null x r p)
    emp

let assert_not_null
  (#opened: _)
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
: SteelGhost unit opened
    (vptr_range_or_null x r p)
    (fun _ -> vptr_range x r p)
    (fun _ -> g_is_null x == false)
    (fun h _ h' ->
      g_is_null x == false /\
      h' (vptr_range x r p) == h (vptr_range_or_null x r p)
    )
=
  assert (g_is_null x == false);
  change_equal_slprop
    (vptr_range_or_null x r p)
    (vptr_range x r p)

val calloc
  (#a: Type)
  (x: a)
  (len: size_t)
: Steel (t a)
    emp
    (fun res -> vptr_range_or_null res (mk_range 0 (size_v len)) full_perm)
    (fun _ -> True)
    (fun _ res h' ->
      if g_is_null res
      then True
      else begin
        base_array_freeable (base res) /\
        base_array_len (base res) == len /\
        size_v (offset res) == 0 /\
        h' (vptr_range res (mk_range 0 (size_v len)) full_perm) == Seq.create (size_v len) x
      end
    )

val malloc
  (#a: Type)
  (x: a)
: Steel (t a)
    emp
    (fun res -> vptr_range_or_null res (mk_range 0 1) full_perm)
    (fun _ -> True)
    (fun _ res h' ->
      if g_is_null res
      then True
      else begin
        base_array_freeable (base res) /\
        size_v (base_array_len (base res)) == 1 /\
        size_v (offset res) == 0 /\
        ptr_sel0 (mk_range 0 1) full_perm res h' == x
      end
    )
// = calloc x 1ul

val free
  (#a: Type)
  (x: t a)
  (r: range)
: Steel unit
    (vptr_range x r full_perm)
    (fun _ -> emp)
    (fun _ ->
      g_is_null x == false ==> (
      let b : base_array a = base x in
      base_array_freeable b /\
      size_v (offset x) == 0 /\
      r.range_from == 0 /\
      r.range_to == size_v (base_array_len b)
    ))
    (fun _ _ _ -> True)

let test_malloc_free () : SteelT unit emp (fun _ -> emp) =
  let x = malloc false in
  if is_null x _ _
  then begin
    assert_null x _ _;
    return ()
  end else begin
    assert_not_null x _ _;
    free x _
  end

(* pointer arithmetic *)

val add
  (#opened: _)
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
  (i: size_t)
: SteelAtomic (t a) opened
    (vptr_range x r p)
    (fun _ -> vptr_range x r p)
    (fun _ ->
      size_v i <= r.range_to
    )
    (fun h res h' ->
      h' (vptr_range x r p) == h (vptr_range x r p) /\
      g_is_null x == false /\
      size_v (offset x) + size_v i <= size_v (base_array_len (base x)) /\
      res == g_add x i
    )

val sub
  (#opened: _)
  (#a: Type)
  (x: t a)
  (r: range)
  (p: perm)
  (i: size_t)
: SteelAtomic (t a) opened
    (vptr_range x r p)
    (fun _ -> vptr_range x r p)
    (fun _ ->
      r.range_from <= 0 - size_v i
    )
    (fun h res h' ->
      h' (vptr_range x r p) == h (vptr_range x r p) /\
      g_is_null x == false /\
      size_v (offset x) >= size_v i /\
      res == g_sub x i
    )

