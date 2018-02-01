module LowParse.SLow.VLData
include LowParse.SLow.VLData.Proof

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

inline_for_extraction
let serialize32_bounded_integer_1 : serializer32 (serialize_bounded_integer 1) =
  (fun (input: bounded_integer 1) -> ((
    let b = B32.create 1ul 42uy in
    serialize32_bounded_integer_1_correct b input;
    serialize32_bounded_integer_1' b input
  ) <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 1) input res } )))

inline_for_extraction
let serialize32_bounded_integer_2 : serializer32 (serialize_bounded_integer 2) =
  (fun (input: bounded_integer 2) -> ((
    let b = B32.create 2ul 42uy in
    serialize32_bounded_integer_2_correct b input;
    serialize32_bounded_integer_2' b input
  ) <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 2) input res } )))

inline_for_extraction
let serialize32_bounded_integer_3 : serializer32 (serialize_bounded_integer 3) =
  (fun (input: bounded_integer 3) -> ((
    let b = B32.create 3ul 42uy in
    serialize32_bounded_integer_3_correct b input;
    serialize32_bounded_integer_3' b input
  ) <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 3) input res } )))

inline_for_extraction
let serialize32_bounded_integer_4 : serializer32 (serialize_bounded_integer 4) =
  serialize32_u32

inline_for_extraction
let serialize_bounded_integer_conv
  (sz sz' : integer_size)
  (s32: serializer32 (serialize_bounded_integer sz))
: Pure (serializer32 (serialize_bounded_integer sz'))
  (requires (sz == sz'))
  (ensures (fun _ -> True))
= s32

inline_for_extraction
let serialize32_bounded_integer
  (sz: integer_size)
: Tot (serializer32 (serialize_bounded_integer sz))
= match sz with
  | 1 -> serialize_bounded_integer_conv 1 sz serialize32_bounded_integer_1
  | 2 -> serialize_bounded_integer_conv 2 sz serialize32_bounded_integer_2
  | 3 -> serialize_bounded_integer_conv 3 sz serialize32_bounded_integer_3
  | 4 -> serialize_bounded_integer_conv 4 sz serialize32_bounded_integer_4

inline_for_extraction
let decode32_bounded_integer_1
 (b: B32.lbytes 1)
: Tot (y: bounded_integer 1 { y == decode_bounded_integer 1 (B32.reveal b) } )
= let r = decode32_bounded_integer_1' b in
  decode32_bounded_integer_1_correct b;
  (r <: (r: bounded_integer 1 { r == decode_bounded_integer 1 (B32.reveal b) } ))

inline_for_extraction
let parse32_bounded_integer_1 : parser32 (parse_bounded_integer 1) =
  decode_bounded_integer_injective 1;
  make_total_constant_size_parser32 1 1ul
    (decode_bounded_integer 1)
    ()
    (decode32_bounded_integer_1)

inline_for_extraction
let parse32_bounded_integer_2 : parser32 (parse_bounded_integer 2) =
  fun (input: bytes32) -> (
    let res = parse32_synth parse_u16 synth_bounded_integer_2 (fun (x: U16.t) -> (Cast.uint16_to_uint32 x <: (y: bounded_integer 2 { y == synth_bounded_integer_2 x } ))) parse32_u16 () input in
    parse_bounded_integer_2_spec ();
    (res <: (res: option (bounded_integer 2 * U32.t) { parser32_correct (parse_bounded_integer 2) input res} ))
  )

inline_for_extraction
let decode32_bounded_integer_3
 (b: B32.lbytes 3)
: Tot (y: bounded_integer 3 { y == decode_bounded_integer 3 (B32.reveal b) } )
= let r = decode32_bounded_integer_3' b in
  decode32_bounded_integer_3_correct b;
  (r <: (r: bounded_integer 3 { r == decode_bounded_integer 3 (B32.reveal b) } ))

inline_for_extraction
let parse32_bounded_integer_3 : parser32 (parse_bounded_integer 3) =
  decode_bounded_integer_injective 3;
  make_total_constant_size_parser32 3 3ul
    (decode_bounded_integer 3)
    ()
    (decode32_bounded_integer_3)

inline_for_extraction
let parse32_bounded_integer_4 : parser32 (parse_bounded_integer 4) =
  fun (input: bytes32) -> (
    let res = parse32_synth parse_u32 synth_bounded_integer_4 (fun (x: U32.t) -> (x <: (y: bounded_integer 4 { y == synth_bounded_integer_4 x } ))) parse32_u32 () input in
    parse_bounded_integer_4_spec ();
    (res <: (res: option (bounded_integer 4 * U32.t) { parser32_correct (parse_bounded_integer 4) input res} ))
  )

inline_for_extraction
let parse_bounded_integer_conv
  (sz sz' : integer_size)
  (s32: parser32 (parse_bounded_integer sz))
: Pure (parser32 (parse_bounded_integer sz'))
  (requires (sz == sz'))
  (ensures (fun _ -> True))
= s32

inline_for_extraction
let parse32_bounded_integer
  (i: integer_size)
: Tot (parser32 (parse_bounded_integer i))
= integer_size_values i;
  match i with
  | 1 -> parse_bounded_integer_conv 1 i parse32_bounded_integer_1
  | 2 -> parse_bounded_integer_conv 2 i parse32_bounded_integer_2
  | 3 -> parse_bounded_integer_conv 3 i parse32_bounded_integer_3
  | 4 -> parse_bounded_integer_conv 4 i parse32_bounded_integer_4

(* Parsers and serializers for the payload *)

(*
let parse32_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (f' : (x: bounded_integer sz) -> Tot (y: bool {y == f x}))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
: Tot (parser32 (parse_vldata_gen sz f p))
= parse_fldata_and_then_cases_injective sz f p;
  parse_vldata_gen_kind_correct sz;
  parse32_and_then (parse32_filter (parse32_bounded_integer
