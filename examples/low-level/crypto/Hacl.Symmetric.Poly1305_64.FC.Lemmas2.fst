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

private let lemma_div_decr (x:nat) (y:pos) : Lemma
  (requires (True))
  (ensures  (x / y <= x))
  = admit() // TODO

val lemma_nth_pow2_gte: #n:pos -> x:UInt.uint_t n -> m:nat{m <= n} ->
  Lemma (requires (x % pow2 m = 0))
        (ensures  (forall (i:nat). (i < n /\ i >= n - m) ==> UInt.nth x i = false))
        [SMTPat (x % pow2 m); SMTPat (x < pow2 n)]
let lemma_nth_pow2_gte #n x m =
  Math.Lemmas.lemma_div_exact x (pow2 m);
  Math.Lemmas.lemma_div_mod x (pow2 m);
  let c = x / pow2 m in
  cut (x = c * pow2 m);
  Math.Lemmas.pow2_plus (n-m) m;
  Math.Lemmas.multiply_fractions x (pow2 m);
  lemma_div_decr x (pow2 m);
  UInt.shift_left_value_lemma #n c m;
  assert(UInt.shift_left #n c m = x);
  let vc = UInt.to_vec #n c in
  let vx = UInt.to_vec #n x in
  assert(vx == BitVector.shift_left_vec vc m);
  assert(forall (i:nat). (i < n /\ i >= n - m) ==> UInt.nth x i = false)


assume val lemma_nth_pow2_gte_inv: #n:pos -> x:UInt.uint_t n -> m:nat{m <= n} ->
  Lemma (requires (forall (i:nat). i < m ==> UInt.nth x (n-i-1) = false))
        (ensures  (x % pow2 m = 0))


assume val lemma_logand_pow2_gte: #n:pos -> x:UInt.uint_t n -> y:UInt.uint_t n -> m:nat ->
       Lemma (requires (x % pow2 m = 0))
             (ensures  (UInt.logand x y % pow2 m = 0))

assume val lemma_logand_pow2_lt: #n:pos -> x:UInt.uint_t n -> y:UInt.uint_t n -> m:nat ->
       Lemma (requires (x < pow2 m))
             (ensures  (UInt.logand x y < pow2 m))


assume val lemma_logand_mask: #n:pos -> x:UInt.uint_t n -> m:nat{m <= n} ->
       Lemma (requires (True))
             (ensures  (pow2 m < pow2 n /\ UInt.logand #n x (pow2 m - 1) = x % pow2 m))

val lemma_poly1305_encode_r_0_: t0:UInt.uint_t 64 -> t1:UInt.uint_t 64 -> Lemma
  (requires (True))
  (ensures  (
    let r0 = t0 % pow2 44 in
    let r1 = (t0 / pow2 44 + (t1 * pow2 20) % pow2 64) % pow2 44 in
    let r2 = t1 / pow2 24 in
    r0 + pow2 44 * r1 + pow2 88 * r2 = t0 + pow2 64 * t1))
let lemma_poly1305_encode_r_0_ t0 t1 =
  admit()


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 10"


val lemma_poly1305_encode_r_0: t0:H64.t -> t1:H64.t -> Lemma
  (requires (True))
  (ensures  (
    let open Hacl.UInt64 in
    let mask = Hacl.Cast.uint64_to_sint64 0xfffffffffffuL in
    let r0 = ( t0                           ) &^ mask in
    let r1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask in
    let r2 = ((t1 >>^ 24ul)                 )         in
    v t0 + pow2 64 * v t1 = eval_3_limbs r0 r1 r2))
let lemma_poly1305_encode_r_0 t0 t1 =
  cut (prime = pow2 130 - 5);
  let open Hacl.UInt64 in
  let mask_44 = Hacl.Cast.uint64_to_sint64 0xfffffffffffuL in
  assert_norm (H64.v mask_44 = pow2 44 - 1);
  let r0 = ( t0                           ) &^ mask_44 in
  let r1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_44 in
  let r2 = ((t1 >>^ 24ul)                 ) in
  assert_norm(pow2 0 = 1);
  lemma_logand_mask (v t0) 44;
  assume(v (t0 >>^ 44ul) < pow2 20);
  assume(v (t1 <<^ 20ul) % pow2 20 = 0);
  assume (v (t1 >>^ 24ul) < pow2 40);
  lemma_load64_le_ (t0 >>^ 44ul) (t1 <<^ 20ul) 0 20 64;
  lemma_logand_mask (v ((t0 >>^ 44ul) |^ (t1 <<^ 20ul))) 44;
  lemma_logand_mask (v (t1 >>^ 24ul)) 44;
  let vr = v r0 + pow2 44 * v r1 + pow2 88 * v r2 in
  Math.Lemmas.pow2_lt_compat 44 20;
  Math.Lemmas.pow2_lt_compat 44 40;
  Math.Lemmas.pow2_lt_compat 64 44;
  cut(v r0 = v t0 % pow2 44);
  cut(v r1 = (v t0 / pow2 44 + (v t1 * pow2 20) % pow2 64) % pow2 44);
  cut (v r2 = v t1 / pow2 24);
  lemma_poly1305_encode_r_0_ (v t0) (v t1);
  cut (vr = v t0 + pow2 64 * v t1);
  assume (vr < pow2 128);
  assert_norm (pow2 128 < pow2 130 - 5);
  cut (vr < prime);
  Math.Lemmas.modulo_lemma vr prime;
  cut (vr = eval_3_limbs r0 r1 r2)


let lemma_poly1305_encode_r_pre (h:HyperStack.mem) (k:uint8_p{length k = 16 /\ live h k})
  (r0:H64.t) (r1:H64.t) (r2:H64.t) : Type0 =
  let t0 = little_endian (Seq.slice (as_seq h k) 0 8) in
  let t1 = little_endian (Seq.slice (as_seq h k) 8 16) in
  lemma_little_endian_is_bounded (Seq.slice (as_seq h k) 0 8);
  lemma_little_endian_is_bounded (Seq.slice (as_seq h k) 8 16);
  assert_norm (0x0ffffffc0fffffff < pow2 64);
  assert_norm (0x0ffffffc0ffffffc < pow2 64);
  let t0' = UInt.logand #64 t0 0x0ffffffc0fffffff in
  let t1' = UInt.logand #64 t1 0x0ffffffc0ffffffc in
  (H64.v r0 = UInt.logand #64 t0' 0xfffffffffff
    /\ H64.v r1 = UInt.logand #64 (UInt.logor (t0' / pow2 44) ((t1' * pow2 20)% pow2 64))
                                  0xfffffffffff
    /\ H64.v r2 = (t1' / pow2 24) )


val lemma_poly1305_encode_r:
  h:HyperStack.mem ->
  k:uint8_p{length k = 16 /\ live h k} ->
  r0:H64.t -> r1:H64.t -> r2:H64.t ->
  Lemma (requires (lemma_poly1305_encode_r_pre h k r0 r1 r2))
        (ensures  (eval_3_limbs r0 r1 r2 = Hacl.Symmetric.Poly1305_64.FC.Spec.clamp (as_seq h k)))
let lemma_poly1305_encode_r h k r0 r1 r2 =
  admit()
