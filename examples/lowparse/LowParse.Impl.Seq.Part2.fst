module LowParse.Impl.Seq.Part2
include LowParse.Impl.Seq.Part1

module Seq = FStar.Seq
module L = FStar.List.Tot
module S = LowParse.Slice
module PL = LowParse.Impl.List
module B = FStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module Classical = FStar.Classical
module G = FStar.Ghost

inline_for_extraction
val seq_slice
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (lo hi: U32.t)
: HST.Stack S.bslice
  (requires (fun h ->
    U32.v lo <= U32.v hi /\
    parses h (parse_seq p) b (fun (s, _) ->
    U32.v hi <= Seq.length s
  )))
  (ensures (fun h res h' ->
    S.modifies_none h h' /\
    U32.v lo <= U32.v hi /\
    parses h (parse_seq p) b (fun (s, _) ->
      U32.v hi <= Seq.length s
    ) /\
    res == seq_slice_spec p b h lo hi 
  ))

#set-options "--z3refresh --z3rlimit 128"

let seq_slice #b #t #p sv b lo hi =
  let h = HST.get () in
  let len1 = seq_offset_at sv b lo in
  let h1 = HST.get () in
  assert (seq_offset_at_postcond p b lo h len1 h1);
  assert (len1 == seq_offset_at_spec p b h lo);
  admit ()

(*
  assert (U32.v len1 == seq_offset_at_spec_nat p (S.as_seq h b) (U32.v lo));
  seq_offset_at_spec_nat_correct p (S.as_seq h b) (U32.v lo);
  assert (Seq.length (S.as_seq h b) == U32.v (S.length b));
  let b1 = S.advance_slice b len1 in
  let h1 = HST.get () in
  assert (S.as_seq h1 b1 == S.as_seq h b1);
  assert (Seq.length (S.as_seq h b1) == U32.v (S.length b1));
  let len2 = seq_offset_at sv b1 (U32.sub hi lo) in
  assert (U32.v len2 == seq_offset_at_spec_nat p (S.as_seq h b1) (U32.v hi - U32.v lo));
  seq_offset_at_spec_nat_correct p (S.as_seq h b1) (U32.v hi - U32.v lo);
  let b2 = S.truncate_slice b1 len2 in
  assert (b2 == seq_slice_spec p b h lo hi);
  b2
*)

#reset-options
