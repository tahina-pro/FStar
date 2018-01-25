module LowParse.SLow.VLData
include LowParse.Spec.VLData
include LowParse.SLow.FLData
include LowParse.SLow.Int

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast
module B32 = FStar.Bytes

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 64 --max_ifuel 64 --max_fuel 64"

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
