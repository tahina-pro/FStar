module LowParse.SLow.Int.Proof

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module Cast = FStar.Int.Cast

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 128 --max_ifuel 32 --max_fuel 32"

let serialize32_u8_correct
  input
= b32_reveal_create 1ul input

let serialize_u16_spec
  (input: U16.t)
: Lemma
  (let ser = serialize_u16 input in
   Seq.length ser == 2 /\
   U8.v (Seq.index ser 1) == U16.v input % 256 /\
   U8.v (Seq.index ser 0) == (U16.v input / 256) % 256
  )
= E.index_n_to_be 2ul (U16.v input) 1;
  E.index_n_to_be 2ul (U16.v input) 0

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 128 --max_ifuel 32 --max_fuel 32"

let serialize32_u16_correct
  buf input
= let ser32 = serialize32_u16' buf input in
  let rser32 = B32.reveal ser32 in
  assert (pow2 8 == 256);
  assert (pow2 16 == 65536);
  let byte1 = Cast.uint16_to_uint8 input in
  assert (U8.v byte1 == U16.v input % 256);
  assert (Seq.index rser32 1 == byte1);
  let byte0v = U16.div input 256us in
  let byte0 = Cast.uint16_to_uint8 byte0v in
  assert (U8.v byte0 == (U16.v input / 256) % 256);
  assert (Seq.index rser32 0 == byte0);
  serialize_u16_spec input;
  let ser = serialize_u16 input in
  assert (Seq.length ser == 2);
  E.lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else if i = 1 then () else ());
  assert (serializer32_correct #_ #_ #parse_u16 serialize_u16 input ser32)

let serialize_u32_spec
  (input: U32.t)
: Lemma
  (let ser = serialize_u32 input in
   Seq.length ser == 4 /\
   U8.v (Seq.index ser 3) == U32.v input % 256 /\
   U8.v (Seq.index ser 2) == (U32.v input / 256) % 256 /\
   U8.v (Seq.index ser 1) == ((U32.v input / 256) / 256) % 256 /\
   U8.v (Seq.index ser 0) == (((U32.v input / 256) / 256) / 256) % 256
  )
= E.index_n_to_be 4ul (U32.v input) 3;
  E.index_n_to_be' 4 (U32.v input) 3;
  E.index_n_to_be 4ul (U32.v input) 2;
  E.index_n_to_be' 4 (U32.v input) 2;
  E.index_n_to_be 4ul (U32.v input) 1;
  E.index_n_to_be' 4 (U32.v input) 1;
  E.index_n_to_be 4ul (U32.v input) 0;
  E.index_n_to_be' 4 (U32.v input) 0

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 256 --max_ifuel 32 --max_fuel 32"

let serialize32_u32_correct
  buf input
= let ser32 = serialize32_u32' buf input in
  let rser32 = B32.reveal ser32 in
  assert (pow2 8 == 256);
  assert (pow2 16 == 65536);
  assert (pow2 32 == 4294967296);
  let byte3 = Cast.uint32_to_uint8 input in
  assert (U8.v byte3 == U32.v input % 256);
  assert (Seq.index rser32 3 == byte3);
  let byte2v = U32.div input 256ul in
  let byte2 = Cast.uint32_to_uint8 byte2v in
  assert (U8.v byte2 == (U32.v input / 256) % 256);
  assert (Seq.index rser32 2 == byte2);
  let byte1v = U32.div byte2v 256ul in
  let byte1 = Cast.uint32_to_uint8 byte1v in
  assert (U8.v byte1 == ((U32.v input / 256) / 256) % 256);
  assert (Seq.index rser32 1 == byte1);
  let byte0v = U32.div byte1v 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  assert (U8.v byte0 == (((U32.v input / 256) / 256) / 256) % 256);
  assert (Seq.index rser32 0 == byte0);
  serialize_u32_spec input;
  let ser = serialize_u32 input in
  assert (Seq.length ser == 4);
  E.lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else if i = 1 then () else if i = 2 then () else if i = 3 then () else ());
  assert (serializer32_correct #_ #_ #parse_u32 serialize_u32 input ser32)

let decode32_u16_correct
  b
=     let b1 = B32.get b 1ul in
      assert_norm (b1 == B32.index b 1);
      B32.index_reveal b 1;
      let b0 = B32.get b 0ul in
      assert_norm (b0 == B32.index b 0);
      B32.index_reveal b 0;
      assert_norm (pow2 8 == 256);
      let r =
	U16.add (Cast.uint8_to_uint16 b1) (U16.mul 256us (Cast.uint8_to_uint16 b0))
      in
      assert (
	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U16.v r == U8.v b1 + Prims.op_Multiply 256 (U8.v b0)
      );
      assert (
	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U16.v r == U8.v b1 + Prims.op_Multiply (pow2 8) (U8.v b0)
      );
      E.be_to_n_2_spec (B32.reveal b);
      assert (
	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U16.v r == E.be_to_n (B32.reveal b)
      );
      assert (
      	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U16.v r == U16.v (decode_u16 (B32.reveal b))
      );
      assert (
	U16.v_inj r (decode_u16 (B32.reveal b));
	(r == decode_u16 (B32.reveal b))
      );
      ()

#reset-options "--z3rlimit 128 --max_fuel 64 --max_ifuel 64"

let decode32_u32_correct
  b
=     let b3 = B32.get b 3ul in
      assert_norm (b3 == B32.index b 3);
      B32.index_reveal b 3;
      let b2 = B32.get b 2ul in
      assert_norm (b2 == B32.index b 2);
      B32.index_reveal b 2;
      let b1 = B32.get b 1ul in
      assert_norm (b1 == B32.index b 1);
      B32.index_reveal b 1;
      let b0 = B32.get b 0ul in
      assert_norm (b0 == B32.index b 0);
      B32.index_reveal b 0;
      assert_norm (pow2 8 == 256);
      let r =
        U32.add (Cast.uint8_to_uint32 b3) (U32.mul 256ul (
          U32.add (Cast.uint8_to_uint32 b2) (U32.mul 256ul (        
	  U32.add (Cast.uint8_to_uint32 b1) (U32.mul 256ul (
          Cast.uint8_to_uint32 b0
        ))))))
      in
      E.lemma_be_to_n_is_bounded (B32.reveal b);
      E.be_to_n_4_spec (B32.reveal b);
      assert (
	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U32.v r == E.be_to_n (B32.reveal b)
      );
      assert (
      	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U32.v r == U32.v (decode_u32 (B32.reveal b))
      );
      assert (
	U32.v_inj r (decode_u32 (B32.reveal b));
	(r == decode_u32 (B32.reveal b))
      );
      ()
