module LowParse.Impl.Int
include LowParse.Impl.Combinators
include LowParse.Spec.Int

module Seq = FStar.Seq
module S = LowParse.Slice
module E = FStar.Kremlin.Endianness
module C = C
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

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
val validate_u8_st_nochk : stateful_validator_nochk parse_u8
let validate_u8_st_nochk = validate_constant_size_nochk 1ul parse_u8

[@"substitute"]
inline_for_extraction
val validate_u16_st_nochk: stateful_validator_nochk parse_u16
let validate_u16_st_nochk = validate_constant_size_nochk 2ul parse_u16

[@"substitute"]
inline_for_extraction
val validate_u32_st_nochk: stateful_validator_nochk parse_u32
let validate_u32_st_nochk = validate_constant_size_nochk 4ul parse_u32

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

#set-options "--z3rlimit 16"

[@"substitute"]
inline_for_extraction
let parse_u16_st_nochk :
  parser_st_nochk parse_u16 =
  parse_total_constant_size_nochk 2ul (fun (input: S.bslice) ->
    let s = S.truncate_slice input 2ul in
    C.load16_be (S.as_buffer s)
  )

#reset-options

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
