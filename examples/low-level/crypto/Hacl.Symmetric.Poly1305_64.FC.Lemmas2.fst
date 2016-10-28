module Hacl.Symmetric.Poly1305_64.FC.Lemmas2

open FStar.Mul
open FStar.ST
open FStar.Buffer

open Hacl.Cast

open Hacl.Symmetric.Poly1305_64.Parameters
open Hacl.Symmetric.Poly1305_64.Bigint

open Hacl.Symmetric.Poly1305_64.FC.Spec
open Hacl.Symmetric.Poly1305_64.FC.Lemmas


module H8   = Hacl.UInt8
module H64  = Hacl.UInt64
module H128 = Hacl.UInt128
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

open FStar.SeqProperties

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"


let lemma_poly1305_encode_r_pre (h:HyperStack.mem) (k:uint8_p{length k = 16 /\ live h k})
  (r0:H64.t) (r1:H64.t) (r2:H64.t) : Type0 =
  let t0 = little_endian (Seq.slice (as_seq h k) 0 8) in
  let t1 = little_endian (Seq.slice (as_seq h k) 8 16) in
  lemma_little_endian_is_bounded (Seq.slice (as_seq h k) 0 8);
  lemma_little_endian_is_bounded (Seq.slice (as_seq h k) 8 16);
  (H64.v r0 = UInt.logand #64 t0 0xffc0fffffff
    /\ H64.v r1 = UInt.logand #64 (UInt.logor (t0 / pow2 44) ((t1 * pow2 20)% pow2 64))
                                  0xfffffc0ffff
    /\ H64.v r2 = UInt.logand #64 (t1 / pow2 24) 0x00ffffffc0f)


val lemma_poly1305_encode_r:
  h:HyperStack.mem ->
  k:uint8_p{length k = 16 /\ live h k} ->
  r0:H64.t -> r1:H64.t -> r2:H64.t ->
  Lemma (requires (lemma_poly1305_encode_r_pre h k r0 r1 r2))
        (ensures  (eval_3_limbs r0 r1 r2 = Hacl.Symmetric.Poly1305_64.FC.Spec.clamp (as_seq h k)))
let lemma_poly1305_encode_r h k r0 r1 r2 =
  admit()
