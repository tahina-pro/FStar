module Hacl.Symmetric.Poly1305_64.FC

open FStar.Mul
open FStar.ST
open FStar.Buffer

open Hacl.Cast

open Hacl.Symmetric.Poly1305_64.Parameters
open Hacl.Symmetric.Poly1305_64.Bigint

open Hacl.Symmetric.Poly1305_64.FC.Spec


module H8   = Hacl.UInt8
module H64  = Hacl.UInt64
module H128 = Hacl.UInt128
module U8   = FStar.UInt8
module U32  = FStar.UInt32
module U64  = FStar.UInt64

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

val pow2_8_lemma: n:nat ->
  Lemma
    (requires (n = 8))
    (ensures  (pow2 n = 256))
    [SMTPat (pow2 n)]
let pow2_8_lemma n = assert_norm(pow2 8 = 256)

val pow2_32_lemma: n:nat ->
  Lemma
    (requires (n = 32))
    (ensures  (pow2 n = 4294967296))
    [SMTPat (pow2 n)]
let pow2_32_lemma n = assert_norm(pow2 32 = 4294967296)

val pow2_64_lemma: n:nat ->
  Lemma
    (requires (n = 64))
    (ensures  (pow2 n = 18446744073709551616))
    [SMTPat (pow2 n)]
let pow2_64_lemma n = assert_norm(pow2 64 = 18446744073709551616)

let elemB : Type0 = b:bigint

let wordB = b:uint8_p{length b <= 16}
let wordB_16 = b:uint8_p{length b = 16}

noeq type poly1305_state = {
  r:bigint;
  h:bigint;
  }

val load64_le:
  b:uint8_p{length b >= 8} ->
  Stack h64
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> h0 == h1))
let load64_le b =
  let b0 = b.(0ul) in
  let b1 = b.(1ul) in
  let b2 = b.(2ul) in
  let b3 = b.(3ul) in
  let b4 = b.(4ul) in
  let b5 = b.(5ul) in
  let b6 = b.(6ul) in
  let b7 = b.(7ul) in
  H64 (
    sint8_to_sint64 b0
    |^ (sint8_to_sint64 b1 <<^ 8ul)
    |^ (sint8_to_sint64 b2 <<^ 16ul)
    |^ (sint8_to_sint64 b3 <<^ 24ul)
    |^ (sint8_to_sint64 b4 <<^ 32ul)
    |^ (sint8_to_sint64 b5 <<^ 40ul)
    |^ (sint8_to_sint64 b6 <<^ 48ul)
    |^ (sint8_to_sint64 b7 <<^ 56ul)
  )


val store64_le:
  b:uint8_p{length b >= 8} ->
  z:H64.t ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let store64_le b z =
  let open Hacl.UInt64 in
  b.(0ul) <- sint64_to_sint8 z;
  b.(1ul) <- sint64_to_sint8 (z >>^ 8ul);
  b.(2ul) <- sint64_to_sint8 (z >>^ 16ul);
  b.(3ul) <- sint64_to_sint8 (z >>^ 24ul);
  b.(4ul) <- sint64_to_sint8 (z >>^ 32ul);
  b.(5ul) <- sint64_to_sint8 (z >>^ 40ul);
  b.(6ul) <- sint64_to_sint8 (z >>^ 48ul);
  b.(7ul) <- sint64_to_sint8 (z >>^ 56ul)


let live_st h (st:poly1305_state) : Type0 =
  live h st.h /\ live h st.r /\ disjoint st.h st.r


val poly1305_init_:
  st:poly1305_state ->
  key:uint8_p{length key = 32} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h key))
    (ensures  (fun h0 _ h1 -> modifies_2 st.r st.h h0 h1 /\ live_st h1 st))
let poly1305_init_ st key =
  let t0 = load64_le(key) in
  let t1 = load64_le(offset key 8ul) in

  let open Hacl.UInt64 in
  st.r.(0ul) <- ( t0                           ) &^ uint64_to_sint64 0xffc0fffffffuL;
  st.r.(1ul) <- ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ uint64_to_sint64 0xfffffc0ffffuL;
  st.r.(2ul) <- ((t1 >>^ 24ul)                 ) &^ uint64_to_sint64 0x00ffffffc0fuL;

  let zero = uint64_to_sint64 0uL in
  st.h.(0ul) <- zero;
  st.h.(1ul) <- zero;
  st.h.(2ul) <- zero;
  Ghost.hide (Seq.createEmpty #elem)


let eval_3_limbs (h0:H64.t) (h1:H64.t) (h2:H64.t) : GTot nat =
  let open Hacl.UInt64 in
  Math.Lemmas.nat_times_nat_is_nat (pow2 44) (v h1);
  Math.Lemmas.nat_times_nat_is_nat (pow2 88) (v h2);
  (v h0 + pow2 44 * v h1 + pow2 88 * v h2) % prime


let limb_44 = x:h64{H64.v x < pow2 44}
let limb_45 = x:h64{H64.v x < pow2 45}
let limb_44_20 = x:h64{H64.v x < 20 * pow2 44}


val mk_mask: nbits:U32.t{U32.v nbits < 64} -> Tot (z:h64{H64.v z = pow2 (U32.v nbits) - 1})
let mk_mask nbits =
  admit();
  let one = uint64_to_sint64 1uL in
  H64 ((one <<^ nbits) -^ one)

open FStar.HyperStack

val sel_word:
  h:mem ->
  b:wordB{live h b} ->
  GTot (s:Seq.seq H8.t{Seq.length s = length b
    /\ (forall (i:nat). {:pattern (Seq.index s i)}
      i < Seq.length s ==> H8.v (Seq.index s i) == H8.v (get h b i))})
let sel_word h b = as_seq h b

(** From the current memory state, returns the field element corresponding to a elemB *)
val sel_elem: h:mem -> b:elemB{live h b} -> GTot elem
let sel_elem h b = eval h b norm_length % p_1305

(** From the current memory state, returns the integer corresponding to a elemB, (before
   computing the modulo) *)
val sel_int: h:mem -> b:elemB{live h b} -> GTot nat
let sel_int h b = eval h b norm_length

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"


open FStar.Ghost



val poly1305_update:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p{length m >= 16} ->
  r0:limb_44 ->
  r1:limb_44 ->
  r2:limb_44 ->
  s1:limb_44_20{H64 (v s1 = 20 * v r1)} ->
  s2:limb_44_20{H64 (v s2 = 20 * v r2)} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st
      /\ (reveal updated_log) ==
          SeqProperties.snoc (reveal current_log) (encode (sel_word h1 (Buffer.sub m 0ul 16ul)))
      /\ sel_elem h1 st.h == poly (reveal updated_log) (sel_elem h0 st.r)))
let poly1305_update log st m r0 r1 r2 s1 s2 =
  let m0 = ST.get() in
  let h_0 = st.h.(0ul) in
  let h_1 = st.h.(1ul) in
  let h_2 = st.h.(2ul) in
  let h0 = h_0 in
  let h1 = h_1 in
  let h2 = h_2 in
  let t0 = load64_le m in
  let t1 = load64_le (offset m 8ul) in

  let mask_2_44 = mk_mask 44ul in
  let mask_2_42 = mk_mask 42ul in

  let open Hacl.UInt64 in

  let t_0 = t0 &^ mask_2_44 in
  let t_1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44 in
  let t_2 = ((t1 >>^ 24ul) &^ mask_2_42) |^ (uint64_to_sint64 1uL <<^ 40ul) in

  assume (eval_3_limbs t_0 t_1 t_2 = pow2 128 + little_endian (sel_word m0 (Buffer.sub m 0ul 16ul)));

  assume (v h0 + v t_0 < pow2 64);
  let h0 = h0 +^ t_0 in
  assume (v h1 + v t_1 < pow2 64);
  let h1 = h1 +^ t_1 in
  assume (v h2 + v t_2 < pow2 64);
  let h2 = h2 +^ t_2 in

  assume (eval_3_limbs h0 h1 h2 =
    pow2 128 + little_endian (sel_word m0 (Buffer.sub m 0ul 16ul))
    + eval_3_limbs h_0 h_1 h_2);

  let open Hacl.UInt128 in
  let d0 = h0 *^ r0 in
  let d  = h1 *^ s2 in
  assume (v d0 + v d < pow2 128);
  let d0 = d0 +^ d  in
  let d  = h2 *^ s1 in
  assume (v d0 + v d < pow2 128);
  let d0 = d0 +^ d  in

  let d1 = h0 *^ r1 in
  let d  = h1 *^ r0 in
  assume (v d1 + v d < pow2 128);
  let d1 = d1 +^ d  in
  let d  = h2 *^ s2 in
  assume (v d1 + v d < pow2 128);
  let d1 = d1 +^ d  in

  let d2 = h0 *^ r2 in
  let d  = h1 *^ r1 in
  assume (v d2 + v d < pow2 128);
  let d2 = d2 +^ d  in
  let d  = h2 *^ r0 in
  assume (v d2 + v d < pow2 128);
  let d2 = d2 +^ d  in

  let c  = sint128_to_sint64 (d0 >>^ 44ul) in
  let h0 = H64 (sint128_to_sint64 d0 &^ mask_2_44) in
  let d1 = d1 +^ sint64_to_sint128 c in

  let c  = sint128_to_sint64 (d1 >>^ 44ul) in
  let h1 = H64 (sint128_to_sint64 d1 &^ mask_2_44) in
  assume (v d2 + H64.v c < pow2 128);
  let d2 = d2 +^ sint64_to_sint128 c in

  let c  = sint128_to_sint64 (d2 >>^ 42ul) in
  let h2 = H64 (sint128_to_sint64 d2 &^ mask_2_42) in

  let open Hacl.UInt64 in
  assume (v c * 5 < pow2 64 /\ v h0 + v c * 5 < pow2 64);
  let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  assume (v h0 + v c < pow2 64);
  let h1 = h1 +^ c in
  st.h.(0ul) <- h0;
  st.h.(1ul) <- h1;
  st.h.(2ul) <- h2;

  let new_log = elift1 (fun l -> SeqProperties.snoc l (eval_3_limbs h0 h1 h2)) log in
  new_log


val poly1305_blocks_loop:
  current_log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t{U64.v len <= length m} ->
  r0:limb_44 ->
  r1:limb_44 ->
  r2:limb_44 ->
  s1:limb_44_20{H64 (v s1 = 20 * v r1)} ->
  s2:limb_44_20{H64 (v s2 = 20 * v r2)} ->
  h0:limb_45 ->
  h1:limb_45 ->
  h2:limb_45 ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h m))
    (ensures  (fun h0 updated_log h1 -> modifies_1 st.h h0 h1 /\ live_st h1 st
      /\ (reveal updated_log) ==
          encode_pad (reveal current_log) (as_seq h0 (Buffer.sub m 0ul (U32 (16ul *^ (Int.Cast.uint64_to_uint32 len)))))
      /\ sel_elem h1 st.h == poly (reveal updated_log) (sel_elem h0 st.r)))
let rec poly1305_blocks_loop log st m len r0 r1 r2 s1 s2 h0 h1 h2 =
  let m0 = ST.get() in
  let h_0 = h0 in
  let h_1 = h1 in
  let h_2 = h2 in
  if U64 (len <^ 16uL) then (
    admit();
    st.h.(0ul) <- h0;
    st.h.(1ul) <- h1;
    st.h.(2ul) <- h2;
    log
  )
  else (
    let t0 = load64_le m in
    let t1 = load64_le (offset m 8ul) in

    let mask_2_44 = mk_mask 44ul in
    let mask_2_42 = mk_mask 42ul in

    let open Hacl.UInt64 in

    let t_0 = t0 &^ mask_2_44 in
    let t_1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44 in
    let t_2 = ((t1 >>^ 24ul) &^ mask_2_42) |^ (uint64_to_sint64 1uL <<^ 40ul) in

    assume (eval_3_limbs t_0 t_1 t_2 = pow2 128 + little_endian (sel_word m0 (Buffer.sub m 0ul 16ul)));

    assume (v h0 + v t_0 < pow2 64);
    let h0 = h0 +^ t_0 in
    assume (v h1 + v t_1 < pow2 64);
    let h1 = h1 +^ t_1 in
    assume (v h2 + v t_2 < pow2 64);
    let h2 = h2 +^ t_2 in

    assume (eval_3_limbs h0 h1 h2 =
      pow2 128 + little_endian (sel_word m0 (Buffer.sub m 0ul 16ul))
      + eval_3_limbs h_0 h_1 h_2);

    let open Hacl.UInt128 in
    let d0 = h0 *^ r0 in
    let d  = h1 *^ s2 in
    assume (v d0 + v d < pow2 128);
    let d0 = d0 +^ d  in
    let d  = h2 *^ s1 in
    assume (v d0 + v d < pow2 128);
    let d0 = d0 +^ d  in

    let d1 = h0 *^ r1 in
    let d  = h1 *^ r0 in
    assume (v d1 + v d < pow2 128);
    let d1 = d1 +^ d  in
    let d  = h2 *^ s2 in
    assume (v d1 + v d < pow2 128);
    let d1 = d1 +^ d  in

    let d2 = h0 *^ r2 in
    let d  = h1 *^ r1 in
    assume (v d2 + v d < pow2 128);
    let d2 = d2 +^ d  in
    let d  = h2 *^ r0 in
    assume (v d2 + v d < pow2 128);
    let d2 = d2 +^ d  in

    let c  = sint128_to_sint64 (d0 >>^ 44ul) in
    let h0 = H64 (sint128_to_sint64 d0 &^ mask_2_44) in
    let d1 = d1 +^ sint64_to_sint128 c in

    let c  = sint128_to_sint64 (d1 >>^ 44ul) in
    let h1 = H64 (sint128_to_sint64 d1 &^ mask_2_44) in
    assume (v d2 + H64.v c < pow2 128);
    let d2 = d2 +^ sint64_to_sint128 c in

    let c  = sint128_to_sint64 (d2 >>^ 42ul) in
    let h2 = H64 (sint128_to_sint64 d2 &^ mask_2_42) in

    let open Hacl.UInt64 in
    assume (v c * 5 < pow2 64 /\ v h0 + v c * 5 < pow2 64);
    let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
    let c  = h0 >>^ 44ul in
    let h0 = h0 &^ mask_2_44 in
    assume (v h0 + v c < pow2 64);
    let h1 = h1 +^ c in

    let len = U64 (len -^ 16uL) in
    let m   = offset m 16ul in
    let new_log = elift1 (fun l -> SeqProperties.snoc l (eval_3_limbs h0 h1 h2)) log in
    poly1305_blocks_loop new_log st m len r0 r1 r2 s1 s2 h0 h1 h2
  )


val poly1305_blocks:
  log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:FStar.UInt64.t ->
  Stack log_t
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))
let poly1305_blocks log st m len =
  let r0 = st.r.(0ul) in
  let r1 = st.r.(1ul) in
  let r2 = st.r.(2ul) in
  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in

  let five = uint64_to_sint64 5uL in
  let s1 = H64 (r1 *^ (five <<^ 2ul)) in
  let s2 = H64 (r2 *^ (five <<^ 2ul)) in

  poly1305_blocks_loop log st m len r0 r1 r2 s1 s2 h0 h1 h2


val poly1305_finish_:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p ->
  m:uint8_p ->
  len:U64.t ->
  key_s:uint8_p{length key_s = 16} ->
  Stack log_t
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let poly1305_finish_ log st mac m len key_s =
  push_frame();

  let mask_2_44 = uint64_to_sint64 0xfffffffffffuL in
  let mask_2_42 = uint64_to_sint64 0x3ffffffffffuL in

  let rem = U64 (len &^ 0xfuL) in

  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in
  let r0 = st.r.(0ul) in
  let r1 = st.r.(1ul) in
  let r2 = st.r.(2ul) in
  let five = uint64_to_sint64 5uL in
  let s1 = H64 (r1 *^ (five <<^ 2ul)) in
  let s2 = H64 (r2 *^ (five <<^ 2ul)) in

    if U64 (rem =^ 0uL) then ()
    else (
      let zero = uint8_to_sint8 0uy in
      let block = create zero 16ul in
      let i = FStar.Int.Cast.uint64_to_uint32 rem in
      blit m (FStar.Int.Cast.uint64_to_uint32 (U64 (len -^ rem))) block 0ul i;
      block.(i) <- uint8_to_sint8 1uy;

      let t0 = load64_le block in
      let t1 = load64_le (offset block 8ul) in

      let open Hacl.UInt64 in

      let h0 = h0 +^ (t0 &^ mask_2_44) in
      let h1 = h1 +^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) in
      let h2 = h2 +^ ((t1 >>^ 24ul) &^ mask_2_42) in

      let open Hacl.UInt128 in

      let d0 = h0 *^ r0 in
      let d  = h1 *^ s2 in
      let d0 = d0 +^ d  in
      let d  = h2 *^ s1 in
      let d0 = d0 +^ d  in

      let d1 = h0 *^ r1 in
      let d  = h1 *^ r0 in
      let d1 = d1 +^ d  in
      let d  = h2 *^ s2 in
      let d1 = d1 +^ d  in

      let d2 = h0 *^ r2 in
      let d  = h1 *^ r1 in
      let d2 = d2 +^ d  in
      let d  = h2 *^ r0 in
      let d2 = d2 +^ d  in

      let c  = sint128_to_sint64 (d0 >>^ 44ul) in
      let h0 = H64 (sint128_to_sint64 d0 &^ mask_2_44) in
      let d1 = d1 +^ sint64_to_sint128 c in

      let c  = sint128_to_sint64 (d1 >>^ 44ul) in
      let h1 = H64 (sint128_to_sint64 d1 &^ mask_2_44) in
      let d2 = d2 +^ sint64_to_sint128 c in

      let c  = sint128_to_sint64 (d2 >>^ 42ul) in
      let h2 = H64 (sint128_to_sint64 d2 &^ mask_2_42) in

      let open Hacl.UInt64 in
      let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
      let c  = h0 >>^ 44ul in
      let h0 = h0 &^ mask_2_44 in
      let h1 = h1 +^ c in
      st.h.(0ul) <- h0;
      st.h.(1ul) <- h1;
      st.h.(2ul) <- h2
    );

  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in

  let open Hacl.UInt64 in

  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ c in
  let c  = h2 >>^ 42ul in
  let h2 = h2 &^ mask_2_42 in
  let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ c in
  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ c in
  let c  = h2 >>^ 42ul in
  let h2 = h2 &^ mask_2_42 in
  let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ c in

  let mask = (eq_mask h0 mask_2_44)
             &^ (eq_mask h1 mask_2_44)
             &^ (gte_mask h2 (uint64_to_sint64 0x3fffffffffbuL)) in
  let h0 = h0 &^ lognot mask in
  let h1 = h1 &^ lognot mask in
  let h2 = h2 -^ ((uint64_to_sint64 0x3fffffffffbuL) &^ mask) in

  let t0 = load64_le (offset key_s 0ul) in
  let t1 = load64_le (offset key_s 8ul) in

  let h0 = h0 +^ (t0 &^ mask_2_44) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) +^ c in
  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ ((t1 >>^ 24ul) &^ mask_2_42) +^ c in
  let h2 = h2 &^ mask_2_42 in

  let h0 = h0 |^ (h1 <<^ 44ul) in
  let h1 = (h1 >>^ 20ul) |^ (h2 <<^ 24ul) in

  store64_le mac h0;
  store64_le (offset mac 8ul) h1;
  pop_frame();
  log // TODO


val poly1305_last:
  log:log_t ->
  st:poly1305_state ->
  m:uint8_p ->
  len:U64.t ->
  Stack log_t
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let poly1305_last log st m len =
  push_frame();

  let mask_2_44 = uint64_to_sint64 0xfffffffffffuL in
  let mask_2_42 = uint64_to_sint64 0x3ffffffffffuL in

  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in
  let r0 = st.r.(0ul) in
  let r1 = st.r.(1ul) in
  let r2 = st.r.(2ul) in
  let five = uint64_to_sint64 5uL in
  let s1 = H64 (r1 *^ (five <<^ 2ul)) in
  let s2 = H64 (r2 *^ (five <<^ 2ul)) in

    if U64 (len =^ 0uL) then ()
    else (
      let zero = uint8_to_sint8 0uy in
      let block = create zero 16ul in
      let i = FStar.Int.Cast.uint64_to_uint32 len in
      blit m 0ul block 0ul i;
      block.(i) <- uint8_to_sint8 1uy;

      let t0 = load64_le block in
      let t1 = load64_le (offset block 8ul) in

      let open Hacl.UInt64 in

      let h0 = h0 +^ (t0 &^ mask_2_44) in
      let h1 = h1 +^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) in
      let h2 = h2 +^ ((t1 >>^ 24ul) &^ mask_2_42) in

      let open Hacl.UInt128 in

      let d0 = h0 *^ r0 in
      let d  = h1 *^ s2 in
      let d0 = d0 +^ d  in
      let d  = h2 *^ s1 in
      let d0 = d0 +^ d  in

      let d1 = h0 *^ r1 in
      let d  = h1 *^ r0 in
      let d1 = d1 +^ d  in
      let d  = h2 *^ s2 in
      let d1 = d1 +^ d  in

      let d2 = h0 *^ r2 in
      let d  = h1 *^ r1 in
      let d2 = d2 +^ d  in
      let d  = h2 *^ r0 in
      let d2 = d2 +^ d  in

      let c  = sint128_to_sint64 (d0 >>^ 44ul) in
      let h0 = H64 (sint128_to_sint64 d0 &^ mask_2_44) in
      let d1 = d1 +^ sint64_to_sint128 c in

      let c  = sint128_to_sint64 (d1 >>^ 44ul) in
      let h1 = H64 (sint128_to_sint64 d1 &^ mask_2_44) in
      let d2 = d2 +^ sint64_to_sint128 c in

      let c  = sint128_to_sint64 (d2 >>^ 42ul) in
      let h2 = H64 (sint128_to_sint64 d2 &^ mask_2_42) in

      let open Hacl.UInt64 in
      let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
      let c  = h0 >>^ 44ul in
      let h0 = h0 &^ mask_2_44 in
      let h1 = h1 +^ c in
      st.h.(0ul) <- h0;
      st.h.(1ul) <- h1;
      st.h.(2ul) <- h2
    );

  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in

  let open Hacl.UInt64 in

  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ c in
  let c  = h2 >>^ 42ul in
  let h2 = h2 &^ mask_2_42 in
  let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ c in
  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ c in
  let c  = h2 >>^ 42ul in
  let h2 = h2 &^ mask_2_42 in
  let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ c in

  let mask = (eq_mask h0 mask_2_44)
             &^ (eq_mask h1 mask_2_44)
             &^ (gte_mask h2 (uint64_to_sint64 0x3fffffffffbuL)) in
  let h0 = h0 &^ lognot mask in
  let h1 = h1 &^ lognot mask in
  let h2 = h2 -^ ((uint64_to_sint64 0x3fffffffffbuL) &^ mask) in

  st.h.(0ul) <- h0;
  st.h.(1ul) <- h1;
  st.h.(2ul) <- h2;

  pop_frame();
  log // TODO


val poly1305_last_sum:
  log:log_t ->
  st:poly1305_state ->
  mac:uint8_p ->
  key_s:uint8_p{length key_s = 16} ->
  Stack log_t
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let poly1305_last_sum log st mac key_s =
  let t0 = load64_le (offset key_s 0ul) in
  let t1 = load64_le (offset key_s 8ul) in

  let mask_2_44 = uint64_to_sint64 0xfffffffffffuL in
  let mask_2_42 = uint64_to_sint64 0x3ffffffffffuL in

  let h0 = st.h.(0ul) in
  let h1 = st.h.(1ul) in
  let h2 = st.h.(2ul) in

  let open Hacl.UInt64 in
  let h0 = h0 +^ (t0 &^ mask_2_44) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) +^ c in
  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ ((t1 >>^ 24ul) &^ mask_2_42) +^ c in
  let h2 = h2 &^ mask_2_42 in

  let h0 = h0 |^ (h1 <<^ 44ul) in
  let h1 = (h1 >>^ 20ul) |^ (h2 <<^ 24ul) in

  store64_le mac h0;
  store64_le (offset mac 8ul) h1;
  log


val crypto_onetimeauth:
  output:uint8_p ->
  input:uint8_p ->
  len:U64.t ->
  k:uint8_p ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let crypto_onetimeauth output input len k =
  push_frame();
  let zero = uint64_to_sint64 0uL in
  let r = create zero 3ul in
  let h = create zero 3ul in
  let st = {r = r; h = h} in
  let key_r = Buffer.sub k 0ul 16ul in
  let key_s = Buffer.sub k 16ul 16ul in
  let init_log = poly1305_init_ st key_r in
  let partial_log = poly1305_blocks init_log st input len in
  let final_log = poly1305_finish_ partial_log st output input len key_s in
  pop_frame()

(* ############################################################################# *)
(*                              API FOR THE RECORD LAYER                         *)
(* ############################################################################# *)


val poly1305_encode_r:
  r:bigint ->
  key:uint8_p{length key = 16} ->
  Stack unit
    (requires (fun h -> live h r /\ live h key /\ disjoint key r))
    (ensures  (fun h0 _ h1 -> modifies_1 r h0 h1 /\ live h1 r
      // TODO: function correctness
      ))
let poly1305_encode_r r key =
  let t0 = load64_le(key) in
  let t1 = load64_le(offset key 8ul) in
  let open Hacl.UInt64 in
  r.(0ul) <- ( t0                           ) &^ uint64_to_sint64 0xffc0fffffffuL;
  r.(1ul) <- ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ uint64_to_sint64 0xfffffc0ffffuL;
  r.(2ul) <- ((t1 >>^ 24ul)                 ) &^ uint64_to_sint64 0x00ffffffc0fuL


val toField_plus_2_128:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let toField_plus_2_128 b m =
  (* Load block values *)
  let t0 = load64_le m in
  let t1 = load64_le (offset m 8ul) in
  (* Useful masks *)
  let mask_2_44 = mk_mask 44ul in
  let mask_2_42 = mk_mask 42ul in
  let open Hacl.UInt64 in
  let t_0 = t0 &^ mask_2_44 in
  let t_1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44 in
  let t_2 = ((t1 >>^ 24ul) &^ mask_2_42) |^ (uint64_to_sint64 1uL <<^ 40ul) in
  b.(0ul) <- t_0;
  b.(1ul) <- t_1;
  b.(2ul) <- t_2


val toField_plus:
  len:U32.t ->
  b:bigint ->
  m:wordB ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let toField_plus len b m' =
  (* Load block values *)
  let m = create (uint8_to_sint8 0uy) 16ul in
  blit m' 0ul m 0ul len;
  let t0 = load64_le m in
  let t1 = load64_le (offset m 8ul) in
  (* Useful masks *)
  let mask_2_44 = mk_mask 44ul in
  let mask_2_42 = mk_mask 42ul in
  let open Hacl.UInt64 in
  let t_0 = t0 &^ mask_2_44 in
  let t_1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44 in
  let t_2 = ((t1 >>^ 24ul) &^ mask_2_42) |^ (uint64_to_sint64 1uL <<^ (U32 (24ul+^ len))) in
  b.(0ul) <- t_0;
  b.(1ul) <- t_1;
  b.(2ul) <- t_2


val toField:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let toField b m =
  (* Load block values *)
  let t0 = load64_le m in
  let t1 = load64_le (offset m 8ul) in
  (* Useful masks *)
  let mask_2_44 = mk_mask 44ul in
  let mask_2_42 = mk_mask 42ul in
  let open Hacl.UInt64 in
  let t_0 = t0 &^ mask_2_44 in
  let t_1 = ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44 in
  let t_2 = ((t1 >>^ 24ul) &^ mask_2_42) in
  b.(0ul) <- t_0;
  b.(1ul) <- t_1;
  b.(2ul) <- t_2


val add_and_multiply:
  acc:bigint ->
  block:bigint ->
  r:bigint ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let add_and_multiply acc block r =
  let mask_2_44 = mk_mask 44ul in
  let mask_2_42 = mk_mask 42ul in
  let five = uint64_to_sint64 5uL in
  let r0 = r.(0ul) in
  let r1 = r.(1ul) in
  let r2 = r.(2ul) in
  let s1 = H64 (r1 *^ (five <<^ 2ul)) in
  let s2 = H64 (r2 *^ (five <<^ 2ul)) in
  let h0 = acc.(0ul) in
  let h1 = acc.(1ul) in
  let h2 = acc.(2ul) in
  let t_0 = block.(0ul) in
  let t_1 = block.(1ul) in
  let t_2 = block.(2ul) in
  let open Hacl.UInt64 in
  let h0 = h0 +^ t_0 in
  assume (v h1 + v t_1 < pow2 64);
  let h1 = h1 +^ t_1 in
  assume (v h2 + v t_2 < pow2 64);
  let h2 = h2 +^ t_2 in
  let open Hacl.UInt128 in
  let d0 = h0 *^ r0 in
  let d  = h1 *^ s2 in
  assume (v d0 + v d < pow2 128);
  let d0 = d0 +^ d  in
  let d  = h2 *^ s1 in
  assume (v d0 + v d < pow2 128);
  let d0 = d0 +^ d  in
  let d1 = h0 *^ r1 in
  let d  = h1 *^ r0 in
  assume (v d1 + v d < pow2 128);
  let d1 = d1 +^ d  in
  let d  = h2 *^ s2 in
  assume (v d1 + v d < pow2 128);
  let d1 = d1 +^ d  in
  let d2 = h0 *^ r2 in
  let d  = h1 *^ r1 in
  assume (v d2 + v d < pow2 128);
  let d2 = d2 +^ d  in
  let d  = h2 *^ r0 in
  assume (v d2 + v d < pow2 128);
  let d2 = d2 +^ d  in
  let c  = sint128_to_sint64 (d0 >>^ 44ul) in
  let h0 = H64 (sint128_to_sint64 d0 &^ mask_2_44) in
  let d1 = d1 +^ sint64_to_sint128 c in
  let c  = sint128_to_sint64 (d1 >>^ 44ul) in
  let h1 = H64 (sint128_to_sint64 d1 &^ mask_2_44) in
  assume (v d2 + H64.v c < pow2 128);
  let d2 = d2 +^ sint64_to_sint128 c in
  let c  = sint128_to_sint64 (d2 >>^ 42ul) in
  let h2 = H64 (sint128_to_sint64 d2 &^ mask_2_42) in
  let open Hacl.UInt64 in
  assume (v c * 5 < pow2 64 /\ v h0 + v c * 5 < pow2 64);
  let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  assume (v h0 + v c < pow2 64);
  let h1 = h1 +^ c in
  acc.(0ul) <- h0;
  acc.(1ul) <- h1;
  acc.(2ul) <- h2


val poly1305_finish:
  mac:uint8_p ->
  acc:bigint ->
  key_s:uint8_p{length key_s = 16} ->
  Stack unit
    (requires (fun _ -> True))
    (ensures  (fun _ _ _ -> True))
let poly1305_finish mac acc key_s =
  push_frame();
  let mask_2_44 = uint64_to_sint64 0xfffffffffffuL in
  let mask_2_42 = uint64_to_sint64 0x3ffffffffffuL in
  let h0 = acc.(0ul) in
  let h1 = acc.(1ul) in
  let h2 = acc.(2ul) in
  let open Hacl.UInt64 in
  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ c in
  let c  = h2 >>^ 42ul in
  let h2 = h2 &^ mask_2_42 in
  let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ c in
  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ c in
  let c  = h2 >>^ 42ul in
  let h2 = h2 &^ mask_2_42 in
  let h0 = h0 +^ (c *^ uint64_to_sint64 5uL) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ c in
  let mask = (eq_mask h0 mask_2_44)
             &^ (eq_mask h1 mask_2_44)
             &^ (gte_mask h2 (uint64_to_sint64 0x3fffffffffbuL)) in
  let h0 = h0 &^ lognot mask in
  let h1 = h1 &^ lognot mask in
  let h2 = h2 -^ ((uint64_to_sint64 0x3fffffffffbuL) &^ mask) in
  let t0 = load64_le (offset key_s 0ul) in
  let t1 = load64_le (offset key_s 8ul) in
  let h0 = h0 +^ (t0 &^ mask_2_44) in
  let c  = h0 >>^ 44ul in
  let h0 = h0 &^ mask_2_44 in
  let h1 = h1 +^ (((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ mask_2_44) +^ c in
  let c  = h1 >>^ 44ul in
  let h1 = h1 &^ mask_2_44 in
  let h2 = h2 +^ ((t1 >>^ 24ul) &^ mask_2_42) +^ c in
  let h2 = h2 &^ mask_2_42 in
  let h0 = h0 |^ (h1 <<^ 44ul) in
  let h1 = (h1 >>^ 20ul) |^ (h2 <<^ 24ul) in
  store64_le mac h0;
  store64_le (offset mac 8ul) h1;
  pop_frame()


val poly1305_start:
  a:elemB ->
  Stack unit
    (requires (fun h -> live h a))
    (ensures  (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1 /\ sel_elem h1 a = 0))
let poly1305_start a =
  let zero_64 = uint64_to_sint64 0uL in
  a.(0ul) <- zero_64;
  a.(1ul) <- zero_64;
  a.(2ul) <- zero_64


val poly1305_init:
  r:elemB ->
  s:wordB_16 ->
  key:uint8_p{length key = 32} ->
  Stack unit
    (requires (fun h -> live h r /\ live h s /\ live h key))
    (ensures  (fun h0 _ h1 -> modifies_2 r s h0 h1 /\ live h1 r /\ live h1 s))
let poly1305_init r s key =
  let t0 = load64_le(key) in
  let t1 = load64_le(offset key 8ul) in
  let open Hacl.UInt64 in
  r.(0ul) <- ( t0                           ) &^ uint64_to_sint64 0xffc0fffffffuL;
  r.(1ul) <- ((t0 >>^ 44ul) |^ (t1 <<^ 20ul)) &^ uint64_to_sint64 0xfffffc0ffffuL;
  r.(2ul) <- ((t1 >>^ 24ul)                 ) &^ uint64_to_sint64 0x00ffffffc0fuL;
  blit key 16ul s 0ul 16ul

