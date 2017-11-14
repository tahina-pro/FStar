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
let as_seq h (b: bslice) : Ghost (s:bytes{Seq.length s == U32.v b.len})
  (requires (live h b))
  (ensures (fun _ -> True)) = B.as_seq h b.p

let length_as_seq h (b: bslice) : Lemma
  (requires (live h b))
  (ensures (Seq.length (as_seq h b) == UInt32.v (length b)))
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
