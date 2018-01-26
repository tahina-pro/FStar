module LowParse.SLow.Int
include LowParse.Spec.Int
include LowParse.SLow.Combinators

module Seq = FStar.Seq
module E = FStar.Kremlin.Endianness
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes
module Cast = FStar.Int.Cast

inline_for_extraction
let serialize32_u8
: serializer32 serialize_u8
= fun (input: U8.t) -> (
    (
      b32_reveal_create 1ul input;
      B32.create 1ul input
    ) <: (
    res: B32.bytes { serializer32_correct serialize_u8 input res }
  ))

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 64 --max_ifuel 32 --max_fuel 32"

let length_set_byte
  (b: bytes32)
  (pos: U32.t {U32.v pos < B32.length b})
  (x: byte)
: Lemma
  (B32.length (B32.set_byte b pos x) == B32.length b)
  [SMTPat (B32.length (B32.set_byte b pos x))]
= B32.reveal_set_byte b pos x;
  B32.length_reveal b;
  B32.length_reveal (B32.set_byte b pos x)

let rec n_to_be'
  (len: nat)
  (n: nat)
: Tot (res: Seq.seq nat { Seq.length res == len } )
  (decreases len)
= if len = 0
  then Seq.createEmpty
  else begin
    let b' = n_to_be' (len - 1) (n / 256) in
    let b'' = Seq.create 1 (n % 256) in
    let res = Seq.append b' b'' in
    assert (Seq.length res == len);
    res
  end

let n_to_be'_spec
  (len: nat)
  (n: nat)
: Lemma
  (requires (len > 0))
  (ensures (
    Seq.slice (n_to_be' len n) 0 (len - 1) == n_to_be' (len - 1) (n / 256) /\
    Seq.index (n_to_be' len n) (len - 1) == n % 256
  ))
= Seq.lemma_eq_intro (n_to_be' (len - 1) (n / 256)) (Seq.slice (n_to_be' len n) 0 (len - 1))

let rec index_n_to_be
  (len: U32.t)
  (n: nat { n < pow2 (Prims.op_Multiply 8 (U32.v len)) } )
  (i: nat {i < U32.v len})
: Lemma
  (requires True)
  (ensures (U8.v (Seq.index (E.n_to_be len n) i) == Seq.index (n_to_be' (U32.v len) n) i))
  (decreases (U32.v len))
= E.n_to_be_spec len n;
  n_to_be'_spec (U32.v len) n;
  if i = U32.v len - 1
  then ()
  else begin
    let len' = U32.sub len 1ul in
    let n' = n / 256 in
    Seq.lemma_index_slice (E.n_to_be len n) 0 (U32.v len - 1) i;
    Seq.lemma_index_slice (n_to_be' (U32.v len) n) 0 (U32.v len - 1) i;
    index_n_to_be len' n' i
  end

let serialize_u16_spec
  (input: U16.t)
: Lemma
  (let ser = serialize_u16 input in
   Seq.length ser == 2 /\
   U8.v (Seq.index ser 1) == U16.v input % 256 /\
   U8.v (Seq.index ser 0) == (U16.v input / 256) % 256
  )
= index_n_to_be 2ul (U16.v input) 1;
  index_n_to_be 2ul (U16.v input) 0

inline_for_extraction
let serialize32_u16'
  (buf: B32.lbytes 2)
  (input: U16.t)
: Tot (B32.lbytes 2)
= let byte1 = Cast.uint16_to_uint8 input in
  let byte0v = U16.div input 256us in
  let byte0 = Cast.uint16_to_uint8 byte0v in
  let buf0 = B32.set_byte buf 0ul byte0 in
  let buf1 = B32.set_byte buf0 1ul byte1 in
  buf1

let lemma_u8_eq_intro
  (s1 s2: bytes)
  (u: unit { Seq.length s1 == Seq.length s2 } )
  (f: (
    (i: nat) ->
    Lemma
    (requires (i < Seq.length s1))
    (ensures (U8.v (Seq.index s1 i) == U8.v (Seq.index s2 i)))
  ))
: Lemma
  (ensures (s1 == s2))
= let g
    (i: nat { i < Seq.length s1 } )
  : Lemma
    (Seq.index s1 i == Seq.index s2 i)
  = f i;
    U8.v_inj (Seq.index s1 i) (Seq.index s2 i)
  in
  Classical.forall_intro g;
  Seq.lemma_eq_intro s1 s2

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 128 --max_ifuel 32 --max_fuel 32"

let serialize32_u16_correct
  (buf: B32.lbytes 2)
  (input: U16.t)
: Lemma
  (serializer32_correct #_ #_ #parse_u16 serialize_u16 input (serialize32_u16' buf input))
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
  lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else if i = 1 then () else ());
  assert (serializer32_correct #_ #_ #parse_u16 serialize_u16 input ser32)

inline_for_extraction
let serialize32_u16 : serializer32 #_ #_ #parse_u16 serialize_u16 =
  (fun (input: U16.t) -> ((
    let b = B32.create 2ul 42uy in
    serialize32_u16_correct b input;
    serialize32_u16' b input
  ) <: (res: B32.bytes { serializer32_correct #_ #_ #parse_u16 serialize_u16 input res } )))

let rec div_256
  (n: nat)
  (times: nat)
: Tot nat
  (decreases times)
= if times = 0
  then n % 256
  else div_256 (n / 256) (times - 1)

let rec index_n_to_be'
  (len: nat)
  (n: nat)
  (i: nat {i < len})
: Lemma
  (requires True)
  (ensures (Seq.index (n_to_be' len n) i == div_256 n (len - 1 - i)))
  (decreases len)
= n_to_be'_spec len n;
  if i = len - 1
  then ()
  else index_n_to_be' (len - 1) (n / 256) i

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
= index_n_to_be 4ul (U32.v input) 3;
  index_n_to_be' 4 (U32.v input) 3;
  index_n_to_be 4ul (U32.v input) 2;
  index_n_to_be' 4 (U32.v input) 2;
  index_n_to_be 4ul (U32.v input) 1;
  index_n_to_be' 4 (U32.v input) 1;
  index_n_to_be 4ul (U32.v input) 0;
  index_n_to_be' 4 (U32.v input) 0

inline_for_extraction
let serialize32_u32'
  (buf: B32.lbytes 4)
  (input: U32.t)
: Tot (B32.lbytes 4)
= let byte3 = Cast.uint32_to_uint8 input in
  let byte2v = U32.div input 256ul in
  let byte2 = Cast.uint32_to_uint8 byte2v in
  let byte1v = U32.div byte2v 256ul in
  let byte1 = Cast.uint32_to_uint8 byte1v in
  let byte0v = U32.div byte1v 256ul in
  let byte0 = Cast.uint32_to_uint8 byte0v in
  let buf0 = B32.set_byte buf 0ul byte0 in
  let buf1 = B32.set_byte buf0 1ul byte1 in
  let buf2 = B32.set_byte buf1 2ul byte2 in
  let buf3 = B32.set_byte buf2 3ul byte3 in
  buf3

#reset-options "--z3cliopt smt.arith.nl=false --z3rlimit 256 --max_ifuel 32 --max_fuel 32"

let serialize32_u32_correct
  (buf: B32.lbytes 4)
  (input: U32.t)
: Lemma
  (serializer32_correct #_ #_ #parse_u32 serialize_u32 input (serialize32_u32' buf input))
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
  lemma_u8_eq_intro rser32 ser ()
    (fun (i: nat) -> if i = 0 then () else if i = 1 then () else if i = 2 then () else if i = 3 then () else ());
  assert (serializer32_correct #_ #_ #parse_u32 serialize_u32 input ser32)

inline_for_extraction
let serialize32_u32 : serializer32 #_ #_ #parse_u32 serialize_u32 =
  (fun (input: U32.t) -> ((
    let b = B32.create 4ul 42uy in
    serialize32_u32_correct b input;
    serialize32_u32' b input
  ) <: (res: B32.bytes { serializer32_correct #_ #_ #parse_u32 serialize_u32 input res } )))

#reset-options "--z3rlimit 32"

inline_for_extraction
let parse32_u8 : parser32 parse_u8 =
  make_total_constant_size_parser32 1 1ul
    decode_u8
    (fun (b: B32.lbytes 1) ->
      let r = B32.get b 0ul in
      assert (r == B32.index b 0);
      B32.index_reveal b 0;
      (r <: (y: U8.t { y == decode_u8 (B32.reveal b) })))

(*
#reset-options "--z3rlimit 256 --max_fuel 64 --max_ifuel 64"

let decode32_u16
  (b: B32.lbytes 2)
: Tot (y: U16.t { y == decode_u16 (B32.reveal b) } )
=     let b1 = B32.get b 1ul in
      assert_norm (b1 == B32.index b 1);
      B32.index_reveal b 1;
      let b0 = B32.get b 0ul in
      assert_norm (b0 == B32.index b 0);
      B32.index_reveal b 0;
      assert_norm (pow2 8 == 256);
      let r =
	U16.add (Cast.uint8_to_uint16 b0) (U16.mul 256us (Cast.uint8_to_uint16 b1))
      in
      assert (
	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U16.v r == U8.v b0 + Prims.op_Multiply 256 (U8.v b1)
      );
      assert (
      	E.lemma_be_to_n_is_bounded (B32.reveal b);
	U16.v r == U16.v (decode_u16 (B32.reveal b))
      );
      assert (
	U16.v_inj r (decode_u16 (B32.reveal b));
	(r == decode_u16 (B32.reveal b))
      );
      (r <: (y: U16.t { y == decode_u16 (B32.reveal b) } ))


inline_for_extraction
let parse32_u16 =
  Classical.forall_intro_2 decode_u16_injective;
    make_total_constant_size_parser32 2 2ul
      #U16.t
      decode_u16
      decode32_u16

(*
    (fun (b: B32.lbytes 2) ->
    )
