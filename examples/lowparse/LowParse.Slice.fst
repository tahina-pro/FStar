module LowParse.Slice

// TODO: this is only for truncate_slice, which could probably be replaced with
// truncated_slice, possibly needing an SMTPat
module Seq = FStar.Seq
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = FStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32

type byte = U8.byte
type bytes = Seq.seq byte
/// the abstract model of input is a sequence of bytes, with a limit on size so
/// offsets always fit in a U32.t
let bytes32 = bs:bytes{ Seq.length bs < pow2 32}

(*** Slices: buffers with runtime length *)

// a byte buffer type indexed by size
type lbuffer (len: nat) = b:B.buffer byte{B.length b == len}

// augment a buffer with a runtime length
private
noeq type bslice_ =
  | BSlice : len:U32.t -> p:lbuffer (U32.v len) -> bslice_

let bslice = bslice_

inline_for_extraction
let length (b: bslice) : Tot U32.t = b.len
let live h (b: bslice) = B.live h b.p

inline_for_extraction
let as_buffer
  (b: bslice)
: Tot (lbuffer (U32.v (length b)))
= b.p

noextract
let as_seq h (b: bslice) : Ghost (s:bytes32)
  (requires (live h b))
  (ensures (fun s -> Seq.length s == U32.v b.len)) = B.as_seq h b.p

let length_as_seq h (b: bslice) : Lemma
  (requires (live h b))
  (ensures (Seq.length (as_seq h b) == U32.v (length b)))
= ()

noextract
let buffer_as_seq_as_buffer (h: HS.mem) (b: bslice) : Lemma
  (requires (live h b))
  (ensures (
    live h b /\
    B.live h (as_buffer b) /\
    B.as_seq h (as_buffer b) == as_seq h b
  ))
  [SMTPatOr [
    [SMTPat (B.live h (as_buffer b))];
    [SMTPat (B.as_seq h (as_buffer b))];
  ]]
= ()

inline_for_extraction
let index
  (b: bslice)
  (i: U32.t)
: HST.Stack byte
  (requires (fun h ->
    live h b /\
    U32.v i < U32.v (length b)
  ))
  (ensures (fun h v h' ->
    h' == h /\
    live h' b /\
    U32.v i < U32.v (length b) /\
    v == Seq.index (as_seq h b) (U32.v i)
  ))
= B.index b.p i

let advanced_slice (b: bslice) (off:U32.t{U32.v off <= U32.v b.len}) : GTot bslice =
  BSlice (U32.sub b.len off) (B.sub b.p off (U32.sub b.len off))

inline_for_extraction
let advance_slice (b:bslice) (off:U32.t{U32.v off <= U32.v b.len}) : HST.Stack bslice
  (requires (fun h -> live h b))
  (ensures (fun h b' h' ->
    h' == h /\
    b' == advanced_slice b off
  ))
= BSlice (U32.sub b.len off) (B.sub b.p off (U32.sub b.len off))

let advanced_slice_spec (b:bslice) (off:U32.t{U32.v off <= U32.v b.len}) h :
  Lemma (requires (live h b))
        (ensures (live h (advanced_slice b off) /\
		  as_buffer (advanced_slice b off) == B.sub (as_buffer b) off (U32.sub (length b) off) /\
                  as_seq h (advanced_slice b off) == Seq.slice (as_seq h b) (U32.v off) (Seq.length (as_seq h b))))
  = ()

let advanced_slice_advanced_slice
  (b: bslice)
  (off1: U32.t {U32.v off1 <= U32.v (length b) } )
  (off2: U32.t {U32.v off2 <= U32.v (advanced_slice b off1).len } )
: Lemma
  (requires (
    True
  ))
  (ensures (
    advanced_slice (advanced_slice b off1) off2 == advanced_slice b (U32.add off1 off2)
  ))
= let s1 = advanced_slice b off1 in
  let s2 = advanced_slice s1 off2 in
  B.sub_sub (BSlice?.p b) off1 (BSlice?.len s1) off2 (BSlice?.len s2)

// pure version of truncate_slice (which is in Stack)
val truncated_slice : b:bslice -> len:U32.t{U32.v len <= U32.v b.len} -> GTot bslice
let truncated_slice b len = BSlice len (B.sub b.p (U32.uint_to_t 0) len)

inline_for_extraction
val truncate_slice : b:bslice -> len:U32.t{U32.v len <= U32.v b.len} -> HST.Stack bslice
  (requires (fun h0 -> live h0 b))
  (ensures (fun h0 r h1 -> live h1 b /\
                        live h1 r /\
                        h0 == h1 /\
			r == truncated_slice b len /\
                        as_seq h1 r == Seq.slice (as_seq h1 b) 0 (U32.v len)))
let truncate_slice b len = BSlice len (B.sub b.p (U32.uint_to_t 0) len)

let as_buffer_truncated_slice
  (b: bslice)
  (len: U32.t{U32.v len <= U32.v b.len})
: Lemma
  (as_buffer (truncated_slice b len) == B.sub (as_buffer b) 0ul len)
= ()

let includes b b' = B.includes b.p b'.p

let includes_trans (b1 b2 b3: bslice) : Lemma
  (requires (includes b1 b2 /\ includes b2 b3))
  (ensures (includes b1 b3))
= B.includes_trans b1.p b2.p b3.p

(*! Framing slices *)

let modifies_none = B.modifies_none

(*! Splitting slices into two parts *)

let buffer_is_concat
  (#t: Type)
  (b: B.buffer t)
  (b1 b2: B.buffer t)
: GTot Type0
= B.length b == B.length b1 + B.length b2 /\
  b1 == B.sub b 0ul (U32.uint_to_t (B.length b1)) /\
  b2 == B.sub b (U32.uint_to_t (B.length b1)) (U32.uint_to_t (B.length b2))

let buffer_is_concat_intro
  (#t: Type)
  (b: B.buffer t)
  (i: U32.t)
: Lemma
  (requires (U32.v i <= B.length b))
  (ensures (
    U32.v i <= B.length b /\
    buffer_is_concat b (B.sub b 0ul i) (B.sub b i (U32.sub (U32.uint_to_t (B.length b)) i))
  ))
= ()

let buffer_is_concat_zero_l
  (#t: Type)
  (b: B.buffer t)
: Lemma
  (buffer_is_concat b (B.sub b 0ul 0ul) b)
= ()

let buffer_is_concat_zero_r
  (#t: Type)
  (b: B.buffer t)
: Lemma
  (buffer_is_concat b b (B.sub b (U32.uint_to_t (B.length b)) 0ul))
= ()

let buffer_is_concat_assoc
  (#t: Type)
  (b123 b12 b23 b1 b2 b3: B.buffer t)
: Lemma
  (requires (
    buffer_is_concat b12 b1 b2 /\
    buffer_is_concat b23 b2 b3
  ))
  (ensures (
    buffer_is_concat b123 b1 b23 <==> buffer_is_concat b123 b12 b3
  ))
= ()

let buffer_is_concat_live
  (#t: Type)
  (h: HS.mem)
  (b12 b1 b2: B.buffer t)
: Lemma
  (requires (
    buffer_is_concat b12 b1 b2 /\ (
    B.live h b1 \/
    B.live h b2 \/
    B.live h b12
  )))
  (ensures (
    B.live h b1 /\
    B.live h b2 /\
    B.live h b12
  ))
= ()

let is_concat
  (b: bslice)
  (b1 b2: bslice)
: GTot Type0
= buffer_is_concat (as_buffer b) (as_buffer b1) (as_buffer b2)

let is_concat_intro
  (#t: Type)
  (b: bslice)
  (i: U32.t)
: Lemma
  (requires (U32.v i <= U32.v (length b)))
  (ensures (
    U32.v i <= U32.v (length b) /\
    is_concat b (truncated_slice b i) (advanced_slice b i)
  ))
= ()

let is_concat_assoc
  (#t: Type)
  (b123 b12 b23 b1 b2 b3: bslice)
: Lemma
  (requires (
    is_concat b12 b1 b2 /\
    is_concat b23 b2 b3
  ))
  (ensures (
    is_concat b123 b1 b23 <==> is_concat b123 b12 b3
  ))
= ()

let is_concat_live
  (h: HS.mem)
  (b12 b1 b2: bslice)
: Lemma
  (requires (
    is_concat b12 b1 b2 /\ (
    live h b1 \/
    live h b2 \/
    live h b12
  )))
  (ensures (
    live h b1 /\
    live h b2 /\
    live h b12
  ))
= ()

let is_prefix (short long: bslice) : GTot Type0 =
  U32.v (length short) <= U32.v (length long) /\ (
    let tail = advanced_slice long (length short) in
    is_concat long short tail
  )

let is_prefix_refl (b: bslice) : Lemma (is_prefix b b) = ()

let is_prefix_truncated_slice
  (b: bslice)
  (i: U32.t)
: Lemma
  (requires (U32.v i <= U32.v (length b)))
  (ensures (
    U32.v i <= U32.v (length b) /\
    is_prefix (truncated_slice b i) b
  ))
= ()

let rec is_concat_gen
  (b: bslice)
  (l: list bslice)
: GTot Type0
  (decreases l)
= match l with
  | [] -> length b == 0ul
  | b1 :: q ->
    is_prefix b1 b /\ (
      let b' = advanced_slice b (length b1) in
      is_concat_gen b' q
    )

let is_concat_is_concat_gen
  (b b1 b2: bslice)
: Lemma
  (is_concat b b1 b2 <==> is_concat_gen b [b1; b2])
= ()

let is_prefix_is_concat_is_prefix
  (b b12 b1 b2: bslice)
: Lemma
  (requires (
    is_prefix b12 b /\
    is_concat b12 b1 b2
  ))
  (ensures (
    is_prefix b1 b
  ))
= ()

let advanced_slice_is_prefix
  (short long: bslice)
  (i: U32.t)
: Lemma
  (requires (
    U32.v i <= U32.v (length short) /\
    is_prefix short long
  ))
  (ensures (
    U32.v i <= U32.v (length short) /\
    U32.v i <= U32.v (length long) /\
    is_prefix (advanced_slice short i) (advanced_slice long i)
  ))
= ()

module L = FStar.List.Tot

let is_concat_gen_cons
  (b: bslice)
  (b1: bslice)
  (q: list bslice)
: Lemma
  (requires (
    is_prefix b1 b /\ (
      let b' = advanced_slice b (length b1) in
      is_concat_gen b' q
  )))
  (ensures (is_concat_gen b (b1 :: q)))
= ()
  
#set-options "--z3rlimit 32"

let rec is_concat_gen_append_intro_l
  (b bl: bslice)
  (ll lr: list bslice)
: Lemma
  (requires (
    is_concat_gen b (bl :: lr) /\
    is_concat_gen bl ll
  ))
  (ensures (
    is_concat_gen b (L.append ll lr)
  ))
  (decreases ll)
= match ll with
  | [] -> ()
  | (b' :: ll') ->
    assert (U32.v (length bl) <= U32.v (length b));
    assert (U32.v (length b') <= U32.v (length bl));   
    assert (is_prefix bl b);
    let bl_ = advanced_slice bl (length b') in
    let b_ = advanced_slice b (length b') in
    is_concat_gen_append_intro_l b_ bl_ ll' lr

let rec is_concat_gen_append_intro
  (b bm: bslice)
  (ll lm lr: list bslice)
: Lemma
  (requires (
    is_concat_gen b (L.append ll (bm :: lr)) /\
    is_concat_gen bm lm
  ))
  (ensures (
    is_concat_gen b (L.append ll (L.append lm lr))
  ))
  (decreases ll)
= match ll with
  | [] -> is_concat_gen_append_intro_l b bm lm lr
  | b' :: ll' ->
    is_concat_gen_append_intro (advanced_slice b (length b')) bm ll' lm lr

#set-options "--z3rlimit 32"

let rec is_concat_gen_append_elim_l
  (b bl: bslice)
  (ll lr: list bslice)
: Lemma
  (requires (
    is_concat_gen b (L.append ll lr) /\
    is_concat_gen bl ll /\
    Cons? ll
  ))
  (ensures (
    is_concat_gen b (bl :: lr)
  ))
  (decreases ll)
= match ll with
  | [_] -> ()
  | (b' :: ll') ->
    let bl_ = advanced_slice bl (length b') in
    let b_ = advanced_slice b (length b') in
    is_concat_gen_append_elim_l b_ bl_ ll' lr

let rec is_concat_gen_append_elim
  (b bm: bslice)
  (ll lm lr: list bslice)
: Lemma
  (requires (
    is_concat_gen b (L.append ll (L.append lm lr)) /\
    is_concat_gen bm lm /\
    Cons? lm
  ))
  (ensures (
    is_concat_gen b (L.append ll (bm :: lr))
  ))
  (decreases ll)
= match ll with
  | [] -> is_concat_gen_append_elim_l b bm lm lr
  | b' :: ll' ->
    is_concat_gen_append_elim (advanced_slice b (length b')) bm ll' lm lr

let rec is_prefix_gen
  (l: list bslice)
  (b: bslice)
: GTot Type0
  (decreases l)
= match l with
  | [] -> True
  | (b' :: l') ->
    is_prefix b' b /\
    is_prefix_gen l' (advanced_slice b (length b'))

let is_prefix_is_prefix_gen
  (short long: bslice)
: Lemma
  (is_prefix short long <==> is_prefix_gen [short] long)
= ()

let rec is_concat_gen_is_prefix_gen
  (l: list bslice)
  (b: bslice)
: Lemma
  (requires (is_concat_gen b l))
  (ensures (is_prefix_gen l b))
= match l with
  | [] -> ()
  | b' :: l' ->
    is_concat_gen_is_prefix_gen l' (advanced_slice b (length b'))
