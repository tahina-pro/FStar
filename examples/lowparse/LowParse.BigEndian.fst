module LowParse.BigEndian
include FStar.Kremlin.Endianness
open FStar.Mul

module Seq = FStar.Seq
module U8 = FStar.UInt8

let be_to_n_2_spec
  (s: Seq.seq U8.t { Seq.length s == 2 } )
: Lemma
  (be_to_n s == U8.v (Seq.index s 1) + pow2 8 * (U8.v (Seq.index s 0)))
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
