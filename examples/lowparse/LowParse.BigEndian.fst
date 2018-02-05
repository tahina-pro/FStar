module LowParse.BigEndian
include FStar.Kremlin.Endianness
open FStar.Mul

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

let be_to_n_1_spec
  (s: Seq.seq U8.t { Seq.length s == 1 } )
: Lemma
  (be_to_n s == U8.v (Seq.index s 0))
= ()

let be_to_n_2_spec
  (s: Seq.seq U8.t { Seq.length s == 2 } )
: Lemma
  (be_to_n s == U8.v (Seq.index s 1) + pow2 8 * (U8.v (Seq.index s 0)))
= ()

let be_to_n_3_spec
  (s: Seq.seq U8.t { Seq.length s == 3 } )
: Lemma
  (be_to_n s ==
    U8.v (Seq.index s 2) + pow2 8 * (
    U8.v (Seq.index s 1) + pow2 8 * (
    U8.v (Seq.index s 0)
  )))
= ()

let be_to_n_4_spec
  (s: Seq.seq U8.t { Seq.length s == 4 } )
: Lemma
  (be_to_n s ==
    U8.v (Seq.index s 3) + pow2 8 * (
    U8.v (Seq.index s 2) + pow2 8 * (
    U8.v (Seq.index s 1) + pow2 8 * (
    U8.v (Seq.index s 0)
  ))))
= ()

let rec n_to_be'
  (len: nat)
  (n: nat)
: GTot (res: Seq.seq nat { Seq.length res == len } )
  (decreases len)
= if len = 0
  then
    Seq.createEmpty
  else begin
    let b' = n_to_be' (len - 1) (n / 256) in
    let b'' = Seq.create 1 (n % 256) in
    let res = Seq.append b' b'' in
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

let n_to_be_spec
  (len:U32.t)
  (n:nat{n < pow2 (Prims.op_Multiply 8 (U32.v len))} )
: Lemma
  (requires (U32.v len > 0))
  (ensures (
    let n' = n / 256 in
    let len' = U32.sub len 1ul in
    n' < pow2 (Prims.op_Multiply 8 (U32.v len')) /\
    Seq.slice (n_to_be len n) 0 (U32.v len - 1) == n_to_be len' n' /\
    U8.v (Seq.index (n_to_be len n) (U32.v len - 1)) == n % 256
  ))
= let n' = n / 256 in
  let len' = U32.sub len 1ul in
  FStar.Math.Lemmas.pow2_plus 8 (Prims.op_Multiply 8 (U32.v len'));
  assert(n' < pow2 (Prims.op_Multiply 8 (U32.v len')));
  Seq.lemma_eq_intro (n_to_be len' n') (Seq.slice (n_to_be len n) 0 (U32.v len'))

let rec index_n_to_be
  (len: U32.t)
  (n: nat { n < pow2 (Prims.op_Multiply 8 (U32.v len)) } )
  (i: nat {i < U32.v len})
: Lemma
  (requires True)
  (ensures (U8.v (Seq.index (n_to_be len n) i) == Seq.index (n_to_be' (U32.v len) n) i))
  (decreases (U32.v len))
= n_to_be_spec len n;
  n_to_be'_spec (U32.v len) n;
  if i = U32.v len - 1
  then ()
  else begin
    let len' = U32.sub len 1ul in
    let n' = n / 256 in
    Seq.lemma_index_slice (n_to_be len n) 0 (U32.v len - 1) i;
    Seq.lemma_index_slice (n_to_be' (U32.v len) n) 0 (U32.v len - 1) i;
    index_n_to_be len' n' i
  end

let rec div_256
  (n: nat)
  (times: nat)
: GTot nat
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
