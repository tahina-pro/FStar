module LowParse.SLow.VLData.Proof

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

let serialize32_bounded_integer_1_correct
  buf input
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

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 128 --max_ifuel 64 --max_fuel 64"

let serialize32_bounded_integer_2_correct
  buf input
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

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 256 --max_ifuel 64 --max_fuel 64"

let serialize32_bounded_integer_3_correct
  buf input
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

let decode32_bounded_integer_1_correct b =
  let r = B32.get b 0ul in
  assert (r == B32.index b 0);
  B32.index_reveal b 0;
  E.be_to_n_1_spec (B32.reveal b);
  let res : U32.t = Cast.uint8_to_uint32 r in
  assert (res == (decode_bounded_integer 1 (B32.reveal b) <: U32.t));
  assert (U32.v res < pow2 (FStar.Mul.op_Star 8 1));
  let (res: bounded_integer 1) = res in
  (res <: (y: bounded_integer 1 { y == decode_bounded_integer 1 (B32.reveal b) }))

#reset-options "--z3rlimit 256 --max_fuel 64 --max_ifuel 64"

let parse_bounded_integer_2_spec
  ()
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

#reset-options "--z3rlimit 1024 --z3refresh  --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped --max_fuel 64 --max_ifuel 64"

let decode32_bounded_integer_3_correct
  b
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

let parse_bounded_integer_4_spec
  ()
= assert (forall (input: bytes { Seq.length input == 4 }) . (decode_u32 `compose` synth_bounded_integer_4) input == decode_bounded_integer 4 input);
  decode_u32_injective ();
  make_total_constant_size_parser_compose 4 U32.t (bounded_integer 4) (decode_u32) (synth_bounded_integer_4);
  assert_norm (forall (input: bytes) . parse (parse_bounded_integer 4) input == parse (make_total_constant_size_parser 4 (bounded_integer 4) (decode_u32 `compose` synth_bounded_integer_4)) input)


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
