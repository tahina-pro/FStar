module LowParse.SLow.Int
include LowParse.SLow.Int.Proof

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module Cast = FStar.Int.Cast

inline_for_extraction
let serialize32_u8
: serializer32 serialize_u8
= (fun (input: U8.t) ->
    serialize32_u8_correct input;
    (serialize32_u8' input <: (res: bytes32 { serializer32_correct #_ #_ #parse_u8 serialize_u8 input res } )))

#reset-options "--z3rlimit 32"

inline_for_extraction
let serialize32_u16 : serializer32 #_ #_ #parse_u16 serialize_u16 =
  (fun (input: U16.t) -> ((
    assert_norm (U32.v 2ul == 2);
    let b = B32.create 2ul 42uy in
    serialize32_u16_correct b input;
    serialize32_u16' b input
  ) <: (res: B32.bytes { serializer32_correct #_ #_ #parse_u16 serialize_u16 input res } )))

inline_for_extraction
let serialize32_u32 : serializer32 #_ #_ #parse_u32 serialize_u32 =
  (fun (input: U32.t) -> ((
    let b = B32.create 4ul 42uy in
    serialize32_u32_correct b input;
    serialize32_u32' b input
  ) <: (res: B32.bytes { serializer32_correct #_ #_ #parse_u32 serialize_u32 input res } )))

inline_for_extraction
let parse32_u8 : parser32 parse_u8 =
  make_total_constant_size_parser32 1 1ul
    decode_u8
    ()
    (fun (b: B32.lbytes 1) ->
      let r = B32.get b 0ul in
      assert (r == B32.index b 0);
      B32.index_reveal b 0;
      (r <: (y: U8.t { y == decode_u8 (B32.reveal b) })))

// #reset-options "--z3rlimit 256 --max_fuel 64 --max_ifuel 64"

inline_for_extraction
let parse32_u16 : parser32 parse_u16 =
  decode_u16_injective ();
    make_total_constant_size_parser32 2 2ul
      #U16.t
      decode_u16
      ()
      decode32_u16

#reset-options "--z3rlimit 32"

inline_for_extraction
let parse32_u32 : parser32 parse_u32 =
    decode_u32_injective ();
    make_total_constant_size_parser32 4 4ul
      #U32.t
      decode_u32
      ()
      decode32_u32
