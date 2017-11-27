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

#set-options "--z3rlimit 64"

let parse_bounded_vlbytes_parse_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#b: bool)
  (#t: Type0)
  (h: HS.mem)
  (p: parser' b t)
  (b: S.bslice)
  (pred: ((t * consumed_slice_length b) -> GTot Type0))
: Lemma
  (requires (parses h (parse_bounded_vlbytes min max p) b pred))
  (ensures (parses h (parse_vlbytes (log256 max) p) b pred))
= ()

#reset-options

inline_for_extraction
let parse_bounded_integer_1_synth
  (x: U8.t)
: Tot (bounded_integer 1)
= Cast.uint8_to_uint32 x

let parse_bounded_integer_1
: parser (bounded_integer 1)
= parse_synth parse_u8 parse_bounded_integer_1_synth

inline_for_extraction
let parse_bounded_integer_2_synth
  (x: U16.t)
: Tot (bounded_integer 2)
= Cast.uint16_to_uint32 x

let parse_bounded_integer_2
: parser (bounded_integer 2)
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
: parser (bounded_integer 3)
= (parse_u16 `nondep_then` parse_u8) `parse_synth` parse_bounded_integer_3_synth

val parse_bounded_integer'
  (i: integer_size)
: parser (bounded_integer i)

let parse_bounded_integer' = function
  | 1 -> parse_bounded_integer_1
  | 2 -> parse_bounded_integer_2
  | 3 -> parse_bounded_integer_3
  | 4 -> parse_u32
