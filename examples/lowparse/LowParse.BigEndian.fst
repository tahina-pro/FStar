module LowParse.BigEndian
include FStar.Kremlin.Endianness

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module CL = C.Loops
module B32 = FStar.Bytes
module Cast = FStar.Int.Cast

let be_to_n_inv
  (input: B32.bytes)
  (continue: bool)
  (accu: B32.bytes * U32.t)
: GTot Type0
= let (rem, sofar) = accu in
  B32.length rem <= B32.length input /\
  B32.length input <= 4 /\
  B32.reveal rem == Seq.slice (B32.reveal input) (B32.length input - B32.length rem) (B32.length input) /\
  U32.v sofar < pow2 (Prims.op_Multiply 8 (B32.length input - B32.length rem)) /\
  U32.v sofar == be_to_n (Seq.slice (B32.reveal input) 0 (B32.length input - B32.length rem)) /\
  (continue == false ==> B32.length rem == 0)

let be_to_n_measure
  (accu: B32.bytes * U32.t)
: GTot nat
= let (rem, _) = accu in
  B32.length rem

#reset-options "--z3rlimit 256 --max_fuel 64 --max_ifuel 64"

inline_for_extraction
let be_to_n_step
  (input: B32.bytes)
  (accu: B32.bytes * U32.t)
: Pure (bool * (B32.bytes * U32.t))
  (requires (be_to_n_inv input true accu))
  (ensures (fun (continue, accu') ->
    be_to_n_inv input continue accu' /\
    (continue == true ==> be_to_n_measure accu' < be_to_n_measure accu)
  ))
= let (rem, sofar) = accu in
  if B32.len rem = 0ul
  then (false, accu)
  else
    let rem' = B32.slice rem 1ul (B32.len rem) in
    let last = B32.get rem 0ul in
    let sofar' = U32.add (Cast.uint8_to_uint32 last) (U32.mul 256ul sofar) in
    assert (
      let s = Seq.slice (B32.reveal input) 0 (B32.length input - B32.length rem) in
      let s' = Seq.slice (B32.reveal input) 0 (B32.length input - B32.length rem') in
      B32.index_reveal rem 0;
      Seq.last s' == Seq.index (B32.reveal input) (B32.length input - B32.length rem) /\
      last == Seq.index (B32.reveal input) (B32.length input - B32.length rem) /\
      Seq.last s' == last /\
      Seq.slice s' 0 (Seq.length s' - 1) == s
    );
    (true, (rem', sofar'))



(*
  

open FStar.Mul

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
