module LowParse.Impl.VLBytes.Part1
include LowParse.Impl.FLBytes
include LowParse.Impl.Int
include LowParse.Spec.VLBytes

module Seq = FStar.Seq
module S = LowParse.Slice
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast

val parse_bounded_vlbytes_parse_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#k: parser_kind)
  (#t: Type0)
  (h: HS.mem)
  (p: parser k t)
  (b: S.bslice)
  (pred: ((t * consumed_slice_length b) -> GTot Type0))
: Lemma
  (requires (parses h (parse_bounded_vlbytes min max p) b pred))
  (ensures (parses h (parse_vlbytes (log256 max) p) b pred))

#set-options "--z3rlimit 128 --max_fuel 8 --max_ifuel 8"

let parse_bounded_vlbytes_parse_vlbytes min max #k #t h p b pred =
  let s = S.as_seq h b in
  let sz = log256 max in
  let f = in_bounds min max in
  assert (Some? (parse (parse_vlbytes_gen sz f p) s));
  parse_flbytes_and_then_cases_injective sz f p;
  assert (Some? (parse (
    (parse_filter (parse_bounded_integer sz) f)
    `and_then`
    (parse_vlbytes_payload sz f p)
  ) s));
  assert (Some? (parse (parse_filter (parse_bounded_integer sz) f) s));
  let (Some (len1, sz1)) = parse (parse_filter (parse_bounded_integer sz) f) s in
  assert (Some? (parse (parse_bounded_integer sz) s));
  let (Some (len2, sz2)) = parse (parse_bounded_integer sz) s in
  assert (sz1 == sz2);
  assert ((len1 <: bounded_integer sz) == len2);
  let pv1: bare_parser t = parse_vlbytes_payload sz f p len1 in
  let s'1 : bytes32 = Seq.slice s sz1 (Seq.length s) in
  let s'2 : bytes32 = Seq.slice s sz2 (Seq.length s) in
  assert (s'1 == s'2);
  assert (Some? (parse pv1 s'1));
  let (Some (v1, consumed1)) = parse pv1 s'1 in
  let pv2: bare_parser t = parse_vlbytes_payload sz f p len2 in
  assert (Some? (parse pv2 s'2));
  let (Some (v2, consumed2)) = parse pv2 s'2 in
  assert (v1 == v2);
  assert ((consumed1 <: nat) == (consumed2 <: nat));
  let total1: consumed_slice_length b = U32.uint_to_t (sz1 + consumed1) in
  let total2: consumed_slice_length b = U32.uint_to_t (sz2 + consumed2) in
  assert (total1 == total2);
  assert (pred (v1, total1));
  assert (pred (v2, total2))

(*
  let (Some (len, sz')) = parse (parse_bounded_integer sz) s in
  assert ((sz' <: nat) == (sz <: nat));
  assert (in_bounds min max len);
  let len_ : (i: bounded_integer sz { in_bounds min max i == true } ) = len in
  let p' : bare_parser t = parse_vlbytes_payload sz (in_bounds min max) p len_ in
  let sz' : nat = sz' in
  let s' : bytes32 = Seq.slice s sz' (Seq.length s) in
  assert (Some? (parse (parse_filter (parse_bounded_integer sz) (in_bounds min max)) s));
  let (Some (len', sz'')) = parse (parse_filter (parse_bounded_integer sz) (in_bounds min max)) s in
  let len' : bounded_integer sz = len' in
  assert (len == len');
  assert (Some? (parse p' s'));
  admit ()

(*  
  assert (Some? (parse (parse_flbytes p (U32.v len)) s'));
  let (Some (v, len')) = parse (parse_flbytes p (U32.v len)) s' in
  assert (len' == U32.v len);
  admit ()

inline_for_extraction
let parse_bounded_integer_1_synth
  (x: U8.t)
: Tot (bounded_integer 1)
= Cast.uint8_to_uint32 x

let parse_bounded_integer_1
: parser _ (bounded_integer 1)
= parse_synth parse_u8 parse_bounded_integer_1_synth

inline_for_extraction
let parse_bounded_integer_2_synth
  (x: U16.t)
: Tot (bounded_integer 2)
= Cast.uint16_to_uint32 x

let parse_bounded_integer_2
: parser _ (bounded_integer 2)
= parse_synth parse_u16 parse_bounded_integer_2_synth

#set-options "--z3rlimit 32"

inline_for_extraction
let parse_bounded_integer_3_synth
  (hilo: U16.t * U8.t)
: Tot (bounded_integer 3)
= let (hi, lo) = hilo in
  U32.add (Cast.uint8_to_uint32 lo) (U32.mul 256ul (Cast.uint16_to_uint32 hi))

#reset-options

let parse_bounded_integer_3
: parser _ (bounded_integer 3)
= (parse_u16 `nondep_then` parse_u8) `parse_synth` parse_bounded_integer_3_synth

val parse_bounded_integer'
  (i: integer_size)
: parser (ParserStrong (StrongConstantSize i ConstantSizeTotal)) (bounded_integer i)

#set-options "--z3rlimit 16"

let parse_bounded_integer' i = match i with
  | 1 -> (parse_bounded_integer_1 <: parser (ParserStrong (StrongConstantSize i ConstantSizeTotal)) (bounded_integer i))
  | 2 -> (parse_bounded_integer_2 <: parser (ParserStrong (StrongConstantSize i ConstantSizeTotal)) (bounded_integer i))
  | 3 -> (parse_bounded_integer_3 <: parser (ParserStrong (StrongConstantSize i ConstantSizeTotal)) (bounded_integer i))
  | 4 -> (parse_u32 <: parser (ParserStrong (StrongConstantSize i ConstantSizeTotal)) (bounded_integer i))

#reset-options
