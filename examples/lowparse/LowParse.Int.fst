module LowParse.Int
include LowParse.Base

module Seq = FStar.Seq
module S = LowParse.Slice
module E = FStar.Kremlin.Endianness
module C = C
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

noextract
let parse_u8: total_constant_size_parser 1 U8.t =
  make_total_constant_size_parser 1 U8.t (fun b -> Seq.index b 0)

noextract
let decode_u16
  (b: bytes32 { Seq.length b == 2 } )
: Tot U16.t
= E.lemma_be_to_n_is_bounded b;
  U16.uint_to_t (E.be_to_n b)

noextract
let parse_u16: total_constant_size_parser 2 U16.t =
  make_total_constant_size_parser 2 U16.t decode_u16

noextract
let decode_u32
  (b: bytes32 { Seq.length b == 4 } )
: Tot U32.t
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)

noextract
let parse_u32: total_constant_size_parser 4 U32.t =
  make_total_constant_size_parser 4 U32.t decode_u32

let parse_u8_injective () : Lemma (injective parse_u8) =
  assert (forall (b1: bytes32 { Seq.length b1 == 1 }) (b2: bytes32 { Seq.length b2 == 1 }) .
    Seq.index b1 0 == Seq.index b2 0 ==> Seq.equal b1 b2
  );
  make_total_constant_size_parser_injective 1 U8.t (fun b -> Seq.index b 0)

let parse_u16_injective () : Lemma (injective parse_u16) =
  assert (forall (b1: bytes32 { Seq.length b1 == 2 }) (b2: bytes32 { Seq.length b2 == 2 }) .
    decode_u16 b1 == decode_u16 b2 ==> Seq.equal b1 b2
  );
  make_total_constant_size_parser_injective 2 U16.t decode_u16

#set-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8"

let parse_u32_injective () : Lemma (injective parse_u32) =
  assert (forall (b1: bytes32 { Seq.length b1 == 4 }) (b2: bytes32 { Seq.length b2 == 4 }) .
    decode_u32 b1 == decode_u32 b2 ==> (
      Seq.index b1 0 == Seq.index b2 0 /\
      Seq.index b1 1 == Seq.index b2 1 /\
      Seq.index b1 2 == Seq.index b2 2 /\
      Seq.index b1 3 == Seq.index b2 3
  ));
  assert (forall (b1: bytes32 { Seq.length b1 == 4 }) (b2: bytes32 { Seq.length b2 == 4 }) .
    decode_u32 b1 == decode_u32 b2 ==> (
      Seq.equal b1 b2
  ));
  make_total_constant_size_parser_injective 4 U32.t decode_u32

#reset-options

[@"substitute"]
inline_for_extraction
val validate_u8_st : stateful_validator parse_u8
let validate_u8_st = validate_total_constant_size 1ul parse_u8

[@"substitute"]
inline_for_extraction
val validate_u16_st: stateful_validator parse_u16
let validate_u16_st = validate_total_constant_size 2ul parse_u16

[@"substitute"]
inline_for_extraction
val validate_u32_st: stateful_validator parse_u32
let validate_u32_st = validate_total_constant_size 4ul parse_u32

[@"substitute"]
inline_for_extraction
let parse_u8_st_nochk :
    parser_st_nochk parse_u8 =
    parse_total_constant_size_nochk 1ul (fun (input: S.bslice) ->
      S.index input 0ul
    )

[@"substitute"]
inline_for_extraction
let parse_u8_st :
    parser_st parse_u8 =
    parse_total_constant_size 1ul parse_u8_st_nochk

[@"substitute"]
inline_for_extraction
let parse_u16_st_nochk :
  parser_st_nochk parse_u16 =
  parse_total_constant_size_nochk 2ul (fun (input: S.bslice) ->
    let s = S.truncate_slice input 2ul in
    C.load16_be (S.as_buffer s)
  )

[@"substitute"]
inline_for_extraction
let parse_u16_st : parser_st parse_u16 =
  parse_total_constant_size 2ul parse_u16_st_nochk

[@"substitute"]
inline_for_extraction
let parse_u32_st_nochk :
  parser_st_nochk (parse_u32) = 
  parse_total_constant_size_nochk 4ul (fun input ->
    let s = S.truncate_slice input 4ul in
    C.load32_be (S.as_buffer s)
  )

[@"substitute"]
inline_for_extraction
let parse_u32_st : parser_st (parse_u32) =
  parse_total_constant_size 4ul parse_u32_st_nochk
