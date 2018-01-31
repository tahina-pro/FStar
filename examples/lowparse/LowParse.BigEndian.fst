module LowParse.BigEndian
include FStar.Kremlin.Endianness
open FStar.Mul

module Seq = FStar.Seq
module U8 = FStar.UInt8

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
