module LowParse.SLow.VLData
include LowParse.Spec.VLData
include LowParse.SLow.FLData
include LowParse.SLow.Int

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 128 --max_ifuel 64 --max_fuel 64"

let pow2_8 () : Lemma (pow2 8 == 256) [SMTPat (pow2 8)] = assert_norm (pow2 8 == 256)
let pow2_16 () : Lemma (pow2 16 == 65536) [SMTPat (pow2 16)] = assert_norm (pow2 16 == 65536)
let pow2_24 () : Lemma (pow2 24 == 16777216) [SMTPat (pow2 24)] = assert_norm (pow2 24 == 16777216)
let pow2_32 () : Lemma (pow2 32 == 4294967296) [SMTPat (pow2 32)] = assert_norm (pow2 32 == 4294967296)

let serialize_bounded_integer_1_spec
  (input: bounded_integer 1)
: Lemma
  (let ser = serialize (serialize_bounded_integer 1) input in
   Seq.length ser == 1 /\
   U8.v (Seq.index ser 0) == U32.v input % 256
  )
= index_n_to_be 1ul (U32.v input) 0

let serialize32_bounded_integer_1'
  (buf: B32.lbytes 1)
  (input: bounded_integer 1)
: Tot (B32.lbytes 1)
= let byte0 = Cast.uint32_to_uint8 input in
  let buf0 = B32.set_byte buf 0ul byte0 in
  buf0

let serialize32_bounded_integer_1_correct
  (buf: B32.lbytes 1)
  (input: bounded_integer 1)
: Lemma
  (serializer32_correct (serialize_bounded_integer 1) input (serialize32_bounded_integer_1' buf input))
= let ser32 = serialize32_bounded_integer_1' buf input in
  let rser32 = B32.reveal ser32 in
  let byte0 = Cast.uint32_to_uint8 input in
  assert (U8.v byte0 == U32.v input % 256);
  assert (Seq.index rser32 0 == byte0);
  serialize_bounded_integer_1_spec input;
  let ser = serialize (serialize_bounded_integer 1) input in
  assert (Seq.length ser == 1);
  lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else ());
  assert (serializer32_correct (serialize_bounded_integer 1) input ser32)

inline_for_extraction
let serialize32_bounded_integer_1 : serializer32 (serialize_bounded_integer 1) =
  (fun (input: bounded_integer 1) -> ((
    let b = B32.create 1ul 42uy in
    serialize32_bounded_integer_1_correct b input;
    serialize32_bounded_integer_1' b input
  ) <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 1) input res } )))

let serialize_bounded_integer_2_spec
  (input: bounded_integer 2)
: Lemma
  (let ser = serialize (serialize_bounded_integer 2) input in
   Seq.length ser == 2 /\
   U8.v (Seq.index ser 1) == U32.v input % 256 /\
   U8.v (Seq.index ser 0) == (U32.v input / 256) % 256
  )
= index_n_to_be 2ul (U32.v input) 1;
  index_n_to_be 2ul (U32.v input) 0

let serialize32_bounded_integer_2'
  (buf: B32.lbytes 2)
  (input: bounded_integer 2)
: Tot (B32.lbytes 2)
= let byte1 = Cast.uint32_to_uint8 input in
  let byte0v = U32.div input 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  let buf0 = B32.set_byte buf 0ul byte0 in
  let buf1 = B32.set_byte buf0 1ul byte1 in
  buf1

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 128 --max_ifuel 64 --max_fuel 64"

let serialize32_bounded_integer_2_correct
  (buf: B32.lbytes 2)
  (input: bounded_integer 2)
: Lemma
  (serializer32_correct (serialize_bounded_integer 2) input (serialize32_bounded_integer_2' buf input))
= let ser32 = serialize32_bounded_integer_2' buf input in
  let rser32 = B32.reveal ser32 in
  let byte1 = Cast.uint32_to_uint8 input in
  assert (U8.v byte1 == U32.v input % 256);
  assert (Seq.index rser32 1 == byte1);
  let byte0v = U32.div input 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  assert (U8.v byte0 == (U32.v input / 256) % 256);
  assert (Seq.index rser32 0 == byte0);
  serialize_bounded_integer_2_spec input;
  let ser = serialize (serialize_bounded_integer 2) input in
  assert (Seq.length ser == 2);
  lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else if i = 1 then () else ());
  assert (serializer32_correct (serialize_bounded_integer 2) input ser32)

inline_for_extraction
let serialize32_bounded_integer_2 : serializer32 (serialize_bounded_integer 2) =
  (fun (input: bounded_integer 2) -> ((
    let b = B32.create 2ul 42uy in
    serialize32_bounded_integer_2_correct b input;
    serialize32_bounded_integer_2' b input
  ) <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 2) input res } )))

let serialize_bounded_integer_3_spec
  (input: bounded_integer 3)
: Lemma
  (let ser = serialize (serialize_bounded_integer 3) input in
   Seq.length ser == 3 /\
   U8.v (Seq.index ser 2) == U32.v input % 256 /\
   U8.v (Seq.index ser 1) == (U32.v input / 256) % 256 /\
   U8.v (Seq.index ser 0) == ((U32.v input / 256) / 256) % 256
  )
= let ser = serialize (serialize_bounded_integer 3) input in
  assert (Seq.length ser == 3);
  let f2 () : Lemma (U8.v (Seq.index ser 2) == U32.v input % 256) =
    index_n_to_be 3ul (U32.v input) 2;
    index_n_to_be' 3 (U32.v input) 2 
  in
  f2 ();
  let f1 () : Lemma (U8.v (Seq.index ser 1) == (U32.v input / 256) % 256) =
    index_n_to_be 3ul (U32.v input) 1;
    index_n_to_be' 3 (U32.v input) 1
  in
  f1 ();
  let f0 () : Lemma (U8.v (Seq.index ser 0) == ((U32.v input / 256) / 256) % 256) =
    index_n_to_be 3ul (U32.v input) 0;
    index_n_to_be' 3 (U32.v input) 0;
    assert (U8.v (Seq.index ser 0) == div_256 (U32.v input) 2);
    assert_norm (div_256 (U32.v input) 2 == ((U32.v input / 256) / 256) % 256);
    assert (U8.v (Seq.index ser 0) == ((U32.v input / 256) / 256) % 256)
  in
  f0 ()

let serialize32_bounded_integer_3'
  (buf: B32.lbytes 3)
  (input: bounded_integer 3)
: Tot (B32.lbytes 3)
= let byte2 = Cast.uint32_to_uint8 input in
  let byte1v = U32.div input 256ul in
  let byte1 = Cast.uint32_to_uint8 byte1v in
  let byte0v = U32.div byte1v 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  let buf0 = B32.set_byte buf 0ul byte0 in
  let buf1 = B32.set_byte buf0 1ul byte1 in
  let buf2 = B32.set_byte buf1 2ul byte2 in
  buf2

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 256 --max_ifuel 64 --max_fuel 64"

let serialize32_bounded_integer_3_correct
  (buf: B32.lbytes 3)
  (input: bounded_integer 3)
: Lemma
  (serializer32_correct (serialize_bounded_integer 3) input (serialize32_bounded_integer_3' buf input))
= let ser32 = serialize32_bounded_integer_3' buf input in
  let rser32 = B32.reveal ser32 in
  let byte2 = Cast.uint32_to_uint8 input in
  assert (U8.v byte2 == U32.v input % 256);
  assert (Seq.index rser32 2 == byte2);
  let byte1v = U32.div input 256ul in
  let byte1 = Cast.uint32_to_uint8 byte1v in
  assert (U8.v byte1 == (U32.v input / 256) % 256);
  assert (Seq.index rser32 1 == byte1);
  let byte0v = U32.div byte1v 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  assert (U8.v byte0 == ((U32.v input / 256) / 256) % 256);
  assert (Seq.index rser32 0 == byte0);
  serialize_bounded_integer_3_spec input;
  let ser = serialize (serialize_bounded_integer 3) input in
  assert (Seq.length ser == 3);
  lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else if i = 1 then () else if i = 2 then () else ());
  assert (serializer32_correct (serialize_bounded_integer 3) input ser32)

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
= assert (sz == 1 \/ sz == 2 \/ sz == 3 \/ sz == 4);
  match sz with
  | 1 -> serialize_bounded_integer_conv 1 sz serialize32_bounded_integer_1
  | 2 -> serialize_bounded_integer_conv 2 sz serialize32_bounded_integer_2
  | 3 -> serialize_bounded_integer_conv 3 sz serialize32_bounded_integer_3
  | 4 -> serialize_bounded_integer_conv 4 sz serialize32_bounded_integer_4

#reset-options "--z3rlimit 32"

inline_for_extraction
let decode32_bounded_integer_1
 (b: B32.lbytes 1)
: Tot (y: bounded_integer 1 { y == decode_bounded_integer 1 (B32.reveal b) } )
= let r = B32.get b 0ul in
  assert (r == B32.index b 0);
  B32.index_reveal b 0;
  E.be_to_n_1_spec (B32.reveal b);
  let res : U32.t = Cast.uint8_to_uint32 r in
  assert (res == (decode_bounded_integer 1 (B32.reveal b) <: U32.t));
  assert (U32.v res < pow2 (FStar.Mul.op_Star 8 1));
  let (res: bounded_integer 1) = res in
  (res <: (y: bounded_integer 1 { y == decode_bounded_integer 1 (B32.reveal b) }))

inline_for_extraction
let parse32_bounded_integer_1 : parser32 (parse_bounded_integer 1) =
  decode_bounded_integer_injective 1;
  make_total_constant_size_parser32 1 1ul
    (decode_bounded_integer 1)
    ()
    (decode32_bounded_integer_1)

let synth_bounded_integer_2
  (x: U16.t)
: GTot (bounded_integer 2)
= Cast.uint16_to_uint32 x

let synth_bounded_integer_2_inj
  ()
: Lemma
  (forall (x x' : U16.t) . synth_bounded_integer_2 x == synth_bounded_integer_2 x' ==> x == x')
= ()

#reset-options "--z3rlimit 256 --max_fuel 64 --max_ifuel 64"

let parse_bounded_integer_2_spec
  ()
: Lemma
  (forall (input: bytes) . parse (parse_bounded_integer 2) input == parse (parse_u16 `parse_synth` synth_bounded_integer_2) input)
= let f
    (input: bytes { Seq.length input == 2 })
  : Lemma
    ((decode_u16 `compose` synth_bounded_integer_2) input == decode_bounded_integer 2 input)
  = E.be_to_n_2_spec input;
    E.lemma_be_to_n_is_bounded input;
    assert (U16.v (decode_u16 input) == U32.v (decode_bounded_integer 2 input));
    assert (U32.v ((decode_u16 `compose` synth_bounded_integer_2) input) == U32.v (decode_bounded_integer 2 input));
    U32.v_inj ((decode_u16 `compose` synth_bounded_integer_2) input) (decode_bounded_integer 2 input)
  in
  Classical.forall_intro f;
  decode_u16_injective ();
  synth_bounded_integer_2_inj ();
  make_total_constant_size_parser_compose 2 U16.t (bounded_integer 2) (decode_u16) (synth_bounded_integer_2);
  assert_norm (forall (input: bytes) . parse (parse_bounded_integer 2) input == parse (make_total_constant_size_parser 2 (bounded_integer 2) (decode_u16 `compose` synth_bounded_integer_2)) input)

inline_for_extraction
let parse32_bounded_integer_2 : parser32 (parse_bounded_integer 2) =
  fun (input: bytes32) -> (
    let res = parse32_synth parse_u16 synth_bounded_integer_2 (fun (x: U16.t) -> (Cast.uint16_to_uint32 x <: (y: bounded_integer 2 { y == synth_bounded_integer_2 x } ))) parse32_u16 () input in
    parse_bounded_integer_2_spec ();
    (res <: (res: option (bounded_integer 2 * U32.t) { parser32_correct (parse_bounded_integer 2) input res} ))
  )

(*
inline_for_extraction
let decode32_bounded_integer_2
 (b: B32.lbytes 2)
: Tot (y: bounded_integer 2 { y == decode_bounded_integer 2 (B32.reveal b) } )
= let b0r = B32.get b 0ul in
  assert (b0r == B32.index b 0);
  B32.index_reveal b 0;
  let b0 = Cast.uint8_to_uint32 b0r in
  let b1r = B32.get b 1ul in
  assert (b1r == B32.index b 1);
  B32.index_reveal b 1;
  let b1 = Cast.uint8_to_uint32 b1r in
  let res = U32.add b1 (U32.mul 256ul b0) in
  E.be_to_n_2_spec (B32.reveal b);
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  assert (res == (decode_bounded_integer 2 (B32.reveal b) <: U32.t));
  assert (U32.v res < pow2 (FStar.Mul.op_Star 8 2));
  let (res: bounded_integer 2) = res in
  (res <: (y: bounded_integer 2 { y == decode_bounded_integer 2 (B32.reveal b) }))

inline_for_extraction
let parse32_bounded_integer_2 : parser32 (parse_bounded_integer 2) =
  decode_bounded_integer_injective 2;
  make_total_constant_size_parser32 2 2ul
    (decode_bounded_integer 2)
    ()
    (decode32_bounded_integer_2)
*)

#reset-options "--z3rlimit 1024 --z3refresh  --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped --max_fuel 64 --max_ifuel 64"

inline_for_extraction
let decode32_bounded_integer_3
 (b: B32.lbytes 3)
: Tot (y: bounded_integer 3 { y == decode_bounded_integer 3 (B32.reveal b) } )
= let b0r = B32.get b 0ul in
  assert (b0r == B32.index b 0);
  B32.index_reveal b 0;
  let b0 = Cast.uint8_to_uint32 b0r in
  let b1r = B32.get b 1ul in
  assert (b1r == B32.index b 1);
  B32.index_reveal b 1;
  let b1 = Cast.uint8_to_uint32 b1r in
  let b2r = B32.get b 2ul in
  assert (b2r == B32.index b 2);
  B32.index_reveal b 2;
  let b2 = Cast.uint8_to_uint32 b2r in
  let res = U32.add b2 (U32.mul 256ul (U32.add b1 (U32.mul 256ul b0))) in
  E.be_to_n_3_spec (B32.reveal b);
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  assert (U32.v res == U32.v (decode_bounded_integer 3 (B32.reveal b) <: U32.t));
  U32.v_inj res (decode_bounded_integer 3 (B32.reveal b) <: U32.t);
  assert (U32.v res < pow2 (FStar.Mul.op_Star 8 3));
  let (res: bounded_integer 3) = res in
  (res <: (y: bounded_integer 3 { y == decode_bounded_integer 3 (B32.reveal b) }))

#reset-options "--z3rlimit 256 --max_fuel 64 --max_ifuel 64"

inline_for_extraction
let parse32_bounded_integer_3 : parser32 (parse_bounded_integer 3) =
  decode_bounded_integer_injective 3;
  make_total_constant_size_parser32 3 3ul
    (decode_bounded_integer 3)
    ()
    (decode32_bounded_integer_3)

let synth_bounded_integer_4
  (x: U32.t)
: GTot (bounded_integer 4)
= x

let parse_bounded_integer_4_spec
  ()
: Lemma
  (forall (input: bytes) . parse (parse_bounded_integer 4) input == parse (parse_u32 `parse_synth` synth_bounded_integer_4) input)
= assert (forall (input: bytes { Seq.length input == 4 }) . (decode_u32 `compose` synth_bounded_integer_4) input == decode_bounded_integer 4 input);
  decode_u32_injective ();
  make_total_constant_size_parser_compose 4 U32.t (bounded_integer 4) (decode_u32) (synth_bounded_integer_4);
  assert_norm (forall (input: bytes) . parse (parse_bounded_integer 4) input == parse (make_total_constant_size_parser 4 (bounded_integer 4) (decode_u32 `compose` synth_bounded_integer_4)) input)

inline_for_extraction
let parse32_bounded_integer_4 : parser32 (parse_bounded_integer 4) =
  fun (input: bytes32) -> (
    let res = parse32_synth parse_u32 synth_bounded_integer_4 (fun (x: U32.t) -> (x <: (y: bounded_integer 4 { y == synth_bounded_integer_4 x } ))) parse32_u32 () input in
    parse_bounded_integer_4_spec ();
    (res <: (res: option (bounded_integer 4 * U32.t) { parser32_correct (parse_bounded_integer 4) input res} ))
  )

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
