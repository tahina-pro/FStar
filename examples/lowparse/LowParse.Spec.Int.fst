module LowParse.Spec.Int
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module E = FStar.Kremlin.Endianness
module C = C
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

let parse_u8: total_constant_size_parser 1 U8.t =
  make_total_constant_size_parser 1 U8.t (fun b -> Seq.index b 0)

let decode_u16
  (b: bytes32 { Seq.length b == 2 } )
: Tot U16.t
= E.lemma_be_to_n_is_bounded b;
  U16.uint_to_t (E.be_to_n b)

(* TODO: move to FStar.Kremlin.Endianness *)

let rec be_to_n_inj
  (b1 b2: bytes)
: Lemma
  (requires (Seq.length b1 == Seq.length b2 /\ E.be_to_n b1 == E.be_to_n b2))
  (ensures (Seq.equal b1 b2))
  (decreases (Seq.length b1))
= if Seq.length b1 = 0
  then ()
  else begin
    be_to_n_inj (Seq.slice b1 0 (Seq.length b1 - 1)) (Seq.slice b2 0 (Seq.length b2 - 1));
    Seq.lemma_split b1 (Seq.length b1 - 1);
    Seq.lemma_split b2 (Seq.length b2 - 1)
  end

let decode_u16_injective
  (b1: bytes32 { Seq.length b1 == 2 } )
  (b2: bytes32 { Seq.length b2 == 2 } )
: Lemma
  (decode_u16 b1 == decode_u16 b2 ==> Seq.equal b1 b2)
= if decode_u16 b1 = decode_u16 b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U32.v (U32.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    be_to_n_inj b1 b2
  end else ()

let parse_u16: total_constant_size_parser 2 U16.t =
  Classical.forall_intro_2 decode_u16_injective;
  make_total_constant_size_parser 2 U16.t decode_u16

let decode_u32
  (b: bytes32 { Seq.length b == 4 } )
: Tot U32.t
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)

let decode_u32_injective
  (b1: bytes32 { Seq.length b1 == 4 } )
  (b2: bytes32 { Seq.length b2 == 4 } )
: Lemma
  (decode_u32 b1 == decode_u32 b2 ==> Seq.equal b1 b2)
= if decode_u32 b1 = decode_u32 b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U32.v (U32.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    be_to_n_inj b1 b2
  end else ()

let parse_u32: total_constant_size_parser 4 U32.t =
  Classical.forall_intro_2 decode_u32_injective;
  make_total_constant_size_parser 4 U32.t decode_u32
