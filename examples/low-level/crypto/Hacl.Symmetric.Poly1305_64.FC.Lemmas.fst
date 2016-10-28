module Hacl.Symmetric.Poly1305_64.FC.Lemmas

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

open FStar.SeqProperties


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

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

let lemma_div_mod (a:nat) (b:pos) : Lemma ( (b * a) % b = 0) = Math.Lemmas.lemma_mod_plus 0 a b

let lemma_mul_lt_lt (a:nat) (b:nat) (c:pos) (d:pos) :
  Lemma (requires (a < c /\ b < d))
        (ensures  (a * b < c * d))
  = ()

let lemma_mul_lt (a:nat) (b:pos) (c:pos) :
  Lemma (requires (a < b))
        (ensures  (a * c < b * c))
  = ()

let lemma_mul_le (a:nat) (b:pos) (c:pos) :
  Lemma (requires (a <= b))
        (ensures  (a * c <= b * c))
  = ()

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_add_disjoint: #z:pos -> a:UInt.uint_t z -> b:UInt.uint_t z -> n:nat -> m:nat{m < z} -> Lemma
  (requires (a % pow2 m = 0 /\ b < pow2 m /\ a < pow2 n /\ n >= m))
  (ensures  (a + b < pow2 n))
let lemma_add_disjoint #z a b n m =
  UInt.lemma_logor_dijoint a b m;
  let c = a / pow2 m in
  Math.Lemmas.lemma_div_exact a (pow2 m);
  cut(a + b < c * pow2 m + pow2 m);
  Math.Lemmas.pow2_plus (n-m) m;
  cut(c < pow2 (n-m));
  Math.Lemmas.distributivity_add_right (pow2 m) c 1;
  cut(a + b < pow2 m * (c + 1));
  lemma_mul_le (c+1) (pow2 (n-m)) (pow2 m)

#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val lemma_shift_h8_h64: b:H8.t -> n:U32.t{U32.v n <= 56} ->
  Lemma (requires (True))
        (ensures  (H64( v (sint8_to_sint64 b <<^ n) % pow2 (U32.v n) = 0
            /\ v (sint8_to_sint64 b <<^ n) < pow2 (U32.v n+8)
            /\ v (sint8_to_sint64 b <<^ n) = pow2 (U32.v n) * H8.v b)))
let lemma_shift_h8_h64 b n =
  let x = H64 (sint8_to_sint64 b <<^ n) in
  let vx = H64.v x in
  let vb = H8.v b in
  let vn = U32.v n in
  Math.Lemmas.pow2_plus 8 vn;
  Math.Lemmas.pow2_le_compat 64 (8+vn);
  lemma_mul_lt vb (pow2 8) (pow2 vn);
  Math.Lemmas.modulo_lemma (pow2 vn * vb) (pow2 64);
  lemma_div_mod (H8.v b) (pow2 vn)

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val lemma_mod_pow2: a:nat -> b:nat -> c:nat{c <= b} ->
  Lemma (requires (a % pow2 b = 0))
        (ensures  (a % pow2 c = 0))
let lemma_mod_pow2 a b c =
  Math.Lemmas.pow2_plus (b-c) c;
  cut (pow2 b = pow2 (b-c) * pow2 c);
  Math.Lemmas.lemma_div_exact a (pow2 b);
  let q = a / pow2 b in
  cut (a = q * pow2 b);
  cut (a = q * pow2 (b - c) * pow2 c);
  Math.Lemmas.lemma_mod_plus 0 (q * pow2 (b - c)) (pow2 c)


val lemma_load64_le_:
  b0:H64.t -> b1:H64.t -> l:nat -> m:nat{m >= l} -> n:nat{n > m /\ n <= 64} ->
  Lemma (requires (H64 (v b0 < pow2 m /\ v b1 % pow2 m = 0 /\ v b1 < pow2 n /\ v b0 % pow2 l = 0)))
        (ensures  (H64 (v (b0 |^ b1) = v b0 + v b1 /\ v b0 + v b1 < pow2 n /\ (v b0 + v b1) % pow2 l = 0)))
let lemma_load64_le_ b0 b1 l m n =
  let open Hacl.UInt64 in
  UInt.lemma_logor_dijoint (v b1) (v b0) m;
  lemma_add_disjoint (v b1) (v b0) n m;
  UInt.logor_commutative (v b0) (v b1);
  lemma_mod_pow2 (v b1) m l;
  Math.Lemmas.lemma_mod_plus_distr_l (v b0) (v b1) (pow2 l);
  Math.Lemmas.lemma_mod_plus_distr_l (v b1) ((v b0) % pow2 l) (pow2 l)


#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"


val lemma_load64_le_1:
  b0:H8.t -> b1:H8.t -> b2:H8.t -> b3:H8.t ->
  Lemma (  H64 (v (sint8_to_sint64 b0 |^ (sint8_to_sint64 b1 <<^ 8ul)
                 |^ (sint8_to_sint64 b2 <<^ 16ul) |^ (sint8_to_sint64 b3 <<^ 24ul))) =
           H8 (v b0 + pow2 8 * v b1 + pow2 16 * v b2 + pow2 24 * v b3)
           /\ H8 (v b0 + pow2 8 * v b1 + pow2 16 * v b2 + pow2 24 * v b3) < pow2 32)
let lemma_load64_le_1 b0 b1 b2 b3 =
  let open Hacl.UInt64 in
  assert_norm (pow2 0 = 1);
  lemma_shift_h8_h64 b1 8ul;
  lemma_shift_h8_h64 b2 16ul;
  lemma_shift_h8_h64 b3 24ul;
  let bs0 = (sint8_to_sint64 b0) in
  let bs1 = (sint8_to_sint64 b1 <<^ 8ul) in
  let bs2 = (sint8_to_sint64 b2 <<^ 16ul) in
  let bs3 = (sint8_to_sint64 b3 <<^ 24ul) in
  lemma_load64_le_ bs0 bs1 0 8 16;
  lemma_load64_le_ (bs0|^bs1) bs2 0 16 24;
  lemma_load64_le_ (bs0|^bs1|^bs2) bs3 0 24 32

#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0"

val lemma_load64_le:
  b0:H8.t -> b1:H8.t -> b2:H8.t -> b3:H8.t -> b4:H8.t -> b5:H8.t -> b6:H8.t -> b7:H8.t ->
  Lemma (  H64 (v (sint8_to_sint64 b0 |^ (sint8_to_sint64 b1 <<^ 8ul)
                 |^ (sint8_to_sint64 b2 <<^ 16ul) |^ (sint8_to_sint64 b3 <<^ 24ul)
                 |^ (sint8_to_sint64 b4 <<^ 32ul) |^ (sint8_to_sint64 b5 <<^ 40ul)
                 |^ (sint8_to_sint64 b6 <<^ 48ul) |^ (sint8_to_sint64 b7 <<^ 56ul))) =
           H8 (v b0 + pow2 8 * v b1 + pow2 16 * v b2 + pow2 24 * v b3
              + pow2 32 * v b4 + pow2 40 * v b5 + pow2 48 * v b6 + pow2 56 * v b7) )
let lemma_load64_le b0 b1 b2 b3 b4 b5 b6 b7 =
  let open Hacl.UInt64 in
  assert_norm (pow2 0 = 1);
  lemma_shift_h8_h64 b4 32ul;
  lemma_shift_h8_h64 b5 40ul;
  lemma_shift_h8_h64 b6 48ul;
  lemma_shift_h8_h64 b7 56ul;
  let bs0 = (sint8_to_sint64 b0) in
  let bs1 = (sint8_to_sint64 b1 <<^ 8ul) in
  let bs2 = (sint8_to_sint64 b2 <<^ 16ul) in
  let bs3 = (sint8_to_sint64 b3 <<^ 24ul) in
  let bs4 = (sint8_to_sint64 b4 <<^ 32ul) in
  let bs5 = (sint8_to_sint64 b5 <<^ 40ul) in
  let bs6 = (sint8_to_sint64 b6 <<^ 48ul) in
  let bs7 = (sint8_to_sint64 b7 <<^ 56ul) in
  lemma_load64_le_1 b0 b1 b2 b3;
  lemma_load64_le_ (bs0|^bs1|^bs2|^bs3) bs4 0 32 40;
  lemma_load64_le_ (bs0|^bs1|^bs2|^bs3|^bs4) bs5 0 40 48;
  lemma_load64_le_ (bs0|^bs1|^bs2|^bs3|^bs4|^bs5) bs6 0 48 56;
  lemma_load64_le_ (bs0|^bs1|^bs2|^bs3|^bs4|^bs5|^bs6) bs7 0 56 64

#reset-options "--z3timeout 5 --initial_fuel 1 --max_fuel 1"

let rec little_endian_from_top (s:Seq.seq H8.t) (len:nat{len <= Seq.length s}) : GTot nat
  = if len = 0 then 0
    else pow2 (8 * (len - 1)) * H8.v (Seq.index s (len-1)) + little_endian_from_top s (len-1)

#reset-options "--z3timeout 20 --initial_fuel 1 --max_fuel 1"

val lemma_little_endian_from_top_:
  s:Seq.seq H8.t{Seq.length s > 0} -> len:nat{len <= Seq.length s} ->
  Lemma (requires (True))
        (ensures  (little_endian (Seq.slice s 0 len) = little_endian_from_top s len))
let rec lemma_little_endian_from_top_ s len =
  if len = 0 then ()
  else (
    lemma_little_endian_from_top_ s (len-1);
    let s' = Seq.slice s 0 (len-1) in
    let s'' = Seq.slice s (len-1) len in
    Seq.lemma_eq_intro (Seq.slice s 0 len) (Seq.append s' s'');
    Seq.lemma_eq_intro s'' (Seq.create 1 (Seq.index s (len-1)));
    little_endian_append s' s'';
    little_endian_singleton (Seq.index s (len-1))
  )


#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"


val lemma_little_endian_from_top:
  s:Seq.seq H8.t{Seq.length s > 0} ->
  Lemma (requires (True))
        (ensures  (little_endian s = little_endian_from_top s (Seq.length s)))
let lemma_little_endian_from_top s =
  Seq.lemma_eq_intro s (Seq.slice s 0 (Seq.length s)); lemma_little_endian_from_top_ s (Seq.length s)

#reset-options "--z3timeout 5 --initial_fuel 1 --max_fuel 1"

val lemma_little_endian_from_top_def: s:Seq.seq H8.t -> len:nat{Seq.length s >= len} ->
  Lemma (requires (True))
        (ensures  ((len = 0 ==> little_endian_from_top s len = 0)
          /\ (len > 0 ==> little_endian_from_top s len = pow2 (8*(len-1)) * H8.v (Seq.index s (len-1)) + little_endian_from_top s (len-1))))
let lemma_little_endian_from_top_def s len = ()

#reset-options "--z3timeout 5 --initial_fuel 0 --max_fuel 0"


val lemma_little_endian_8_:
  s:Seq.seq H8.t{Seq.length s = 8} ->
  Lemma (little_endian s =
              H8 (v (Seq.index s 0) + pow2 8 * v (Seq.index s 1) + pow2 16 * v (Seq.index s 2)
              + pow2 24 * v (Seq.index s 3) + pow2 32 * v (Seq.index s 4) + pow2 40 * v (Seq.index s 5)
              + pow2 48 * v (Seq.index s 6) + pow2 56 * v (Seq.index s 7)))
let lemma_little_endian_8_ s =
  let open Hacl.UInt8 in
  let open FStar.Seq in
  assert_norm (pow2 0 = 1);
  lemma_little_endian_from_top s;
  lemma_little_endian_from_top_def s 8;
  lemma_little_endian_from_top_def s 7;
  lemma_little_endian_from_top_def s 6;
  lemma_little_endian_from_top_def s 5;
  lemma_little_endian_from_top_def s 4;
  lemma_little_endian_from_top_def s 3;
  lemma_little_endian_from_top_def s 2;
  lemma_little_endian_from_top_def s 1;
  lemma_little_endian_from_top_def s 0


val lemma_little_endian_8:
  h:HyperStack.mem ->
  b:uint8_p{length b = 8} ->
  Lemma (requires (live h b))
        (ensures  (live h b
          /\ little_endian (as_seq h b) =
              H8 (v (get h b 0) + pow2 8 * v (get h b 1) + pow2 16 * v (get h b 2)
              + pow2 24 * v (get h b 3) + pow2 32 * v (get h b 4) + pow2 40 * v (get h b 5)
              + pow2 48 * v (get h b 6) + pow2 56 * v (get h b 7))))
let lemma_little_endian_8 h b =
  let s = as_seq h b in
  cut(forall (i:nat). {:pattern (Seq.index s i)} i < 8 ==> Seq.index s i == get h b i);
  lemma_little_endian_8_ s


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 10"

val lemma_div_pow2_lt: a:nat -> m:nat -> n:nat ->
  Lemma (requires (a < pow2 m /\ n <= m))
        (ensures  (n <= m /\ a / pow2 n < pow2 (m-n)))
let lemma_div_pow2_lt a m n =
  Math.Lemmas.pow2_plus (m-n) n

val lemma_div_pow2_mod: a:nat -> m:nat -> n:nat ->
  Lemma (requires (a < pow2 m /\ n <= m))
        (ensures  (n <= m /\ (a / pow2 n) % pow2 (m-n) = a/pow2 n))
let lemma_div_pow2_mod a m n =
  lemma_div_pow2_lt a m n; Math.Lemmas.modulo_lemma (a/pow2 n) (pow2 (m-n))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

val lemma_store64_le_: z:H64.t ->
  Lemma (let open Hacl.UInt64 in
    let b0 = sint64_to_sint8 z in
    let b1 = sint64_to_sint8 (z >>^ 8ul) in
    let b2 = sint64_to_sint8 (z >>^ 16ul) in
    let b3 = sint64_to_sint8 (z >>^ 24ul) in
    let b4 = sint64_to_sint8 (z >>^ 32ul) in
    let b5 = sint64_to_sint8 (z >>^ 40ul) in
    let b6 = sint64_to_sint8 (z >>^ 48ul) in
    let b7 = sint64_to_sint8 (z >>^ 56ul) in
    H8 (v (b0) + pow2 8 * v (b1) + pow2 16 * v (b2)
              + pow2 24 * v (b3) + pow2 32 * v (b4) + pow2 40 * v (b5)
              + pow2 48 * v (b6) + pow2 56 * v (b7)) = H64.v z)
let lemma_store64_le_ z =
  let open Hacl.UInt64 in
  let b0 = sint64_to_sint8 z in
  let b1 = sint64_to_sint8 (z >>^ 8ul) in
  let b2 = sint64_to_sint8 (z >>^ 16ul) in
  let b3 = sint64_to_sint8 (z >>^ 24ul) in
  let b4 = sint64_to_sint8 (z >>^ 32ul) in
  let b5 = sint64_to_sint8 (z >>^ 40ul) in
  let b6 = sint64_to_sint8 (z >>^ 48ul) in
  let b7 = sint64_to_sint8 (z >>^ 56ul) in
  let open Hacl.UInt8 in
  let vz = H64.v z in
  let vz56 = vz % pow2 56 in
  let vz48 = vz % pow2 48 in
  let vz40 = vz % pow2 40 in
  let vz32 = vz % pow2 32 in
  let vz24 = vz % pow2 24 in
  let vz16 = vz % pow2 16 in
  let vz8  = vz % pow2  8 in
  let p8 = pow2 8 in
  let p16 = pow2 16 in
  let p24 = pow2 24 in
  let p32 = pow2 32 in
  let p40 = pow2 40 in
  let p48 = pow2 48 in
  let p56 = pow2 56 in
  Math.Lemmas.lemma_div_mod vz (p56);
  lemma_div_pow2_mod vz 64 56;
  cut (vz = p56 * (v b7) + (vz56));
  Math.Lemmas.lemma_div_mod (vz56) (p48);
  lemma_div_pow2_mod (vz56) 56 48;
  Math.Lemmas.pow2_modulo_division_lemma_1 vz 48 56;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 vz 48 56;
  cut (vz56 = p48 * v b6 + vz48);
  Math.Lemmas.lemma_div_mod (vz48) (p40);
  lemma_div_pow2_mod (vz48) 48 40;
  Math.Lemmas.pow2_modulo_division_lemma_1 vz 40 48;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 vz 40 48;
  cut (vz48 = p40 * v b5 + vz40);
  Math.Lemmas.lemma_div_mod (vz40) (p32);
  lemma_div_pow2_mod (vz40) 40 32;
  Math.Lemmas.pow2_modulo_division_lemma_1 vz 32 40;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 vz 32 40;
  cut (vz40 = p32 * v b4 + vz32);
  Math.Lemmas.lemma_div_mod (vz32) (p24);
  lemma_div_pow2_mod (vz32) 32 24;
  Math.Lemmas.pow2_modulo_division_lemma_1 vz 24 32;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 vz 24 32;
  cut (vz32 = p24 * v b3 + vz24);
  Math.Lemmas.lemma_div_mod (vz24) (p16);
  lemma_div_pow2_mod (vz24) 24 16;
  Math.Lemmas.pow2_modulo_division_lemma_1 vz 16 24;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 vz 16 24;
  cut (vz24 = p16 * v b2 + vz16);
  Math.Lemmas.lemma_div_mod (vz16) (p8);
  lemma_div_pow2_mod (vz16) 16 8;
  Math.Lemmas.pow2_modulo_division_lemma_1 vz 8 16;
  Math.Lemmas.pow2_modulo_modulo_lemma_1 vz 8 16;
  cut (vz16 = p8 * v b1 + v b0)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"


open FStar.HyperStack


val sel_word:
  h:mem ->
  b:uint8_p{live h b} ->
  GTot (s:Seq.seq H8.t{Seq.length s = length b
    /\ (forall (i:nat). {:pattern (Seq.index s i)}
      i < Seq.length s ==> H8.v (Seq.index s i) == H8.v (get h b i))})
let sel_word h b = as_seq h b


(** From the current memory state, returns the field element corresponding to a elemB *)
val sel_elem: h:mem -> b:bigint{live h b} -> GTot elem
let sel_elem h b = eval h b norm_length % p_1305


(** From the current memory state, returns the integer corresponding to a elemB, (before
   computing the modulo) *)
val sel_int: h:mem -> b:bigint{live h b} -> GTot nat
let sel_int h b = eval h b norm_length


let eval_3_limbs (h0:H64.t) (h1:H64.t) (h2:H64.t) : GTot nat =
  let open Hacl.UInt64 in
  Math.Lemmas.nat_times_nat_is_nat (pow2 44) (v h1);
  Math.Lemmas.nat_times_nat_is_nat (pow2 88) (v h2);
  (v h0 + pow2 44 * v h1 + pow2 88 * v h2) % prime


let limb_44 = x:h64{H64.v x < pow2 44}
let limb_45 = x:h64{H64.v x < pow2 45}
let limb_44_20 = x:h64{H64.v x < 20 * pow2 44}

#reset-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

val mk_mask: nbits:U32.t{U32.v nbits < 64} -> Tot (z:h64{H64.v z = pow2 (U32.v nbits) - 1})
let mk_mask nbits =
  Math.Lemmas.pow2_lt_compat 64 (U32.v nbits);
  cut( (1*pow2 (U32.v nbits)) % pow2 64 = pow2 (U32.v nbits));
  let one = uint64_to_sint64 1uL in
  H64 ((one <<^ nbits) -^ one)
