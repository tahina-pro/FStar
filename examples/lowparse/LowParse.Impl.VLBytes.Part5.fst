module LowParse.Impl.VLBytes.Part5
include LowParse.Impl.VLBytes.Part3
include LowParse.Impl.VLBytes.Part4

module Seq = FStar.Seq
module S = LowParse.Slice
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast

inline_for_extraction
val point_to_vlbytes_contents
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    parses h (parse_vlbytes_gen sz f p) b (fun _ -> True)
  ))
  (ensures (fun h0 b' h1 ->
    S.modifies_none h0 h1 /\
    point_to_vlbytes_contents_postcond sz f p b h0 b'
  ))

#set-options "--z3rlimit 16"

let point_to_vlbytes_contents sz f #b #t p b =
  let h = HST.get () in
  let (len, _) = parse_bounded_integer_st_nochk sz b in
  let b1 = S.advance_slice b (U32.uint_to_t sz) in
  let b' = S.truncate_slice b1 len in
  assert (point_to_vlbytes_contents_correct_precond sz f p b h len b1 b');
  point_to_vlbytes_contents_correct sz f p b h len b1 b';
  b'

#reset-options

#set-options "--z3rlimit 128"

let serialize_vlbytes_gen_correct
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b b1 b2: S.bslice)
  (h: HS.mem)
: Lemma
  (requires (
    S.is_concat b b1 b2 /\ (
    let len = S.length b2 in
    U32.v len < pow2 (FStar.Mul.op_Star 8 sz) /\
    f (len <: bounded_integer sz) == true /\
    exactly_parses h (parse_bounded_integer sz) b1 (fun v -> (v <: U32.t) == len) /\
    exactly_parses h p b2 (fun _ -> True)
  )))
  (ensures (
    exactly_parses h (parse_vlbytes_gen sz f p) b (fun v ->
    exactly_parses h p b2 (fun v' ->
    v == v'
  ))))
= assert (no_lookahead_on _ (parse_bounded_integer sz) (S.as_seq h b1) (S.as_seq h b));
  assert (injective_postcond (parse_bounded_integer sz) (S.as_seq h b1) (S.as_seq h b))
