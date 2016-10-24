module Hacl.Symmetric.Poly1305_64.FC.Spec

open FStar.Mul
open FStar.ST

open Hacl.Cast

open Hacl.Symmetric.Poly1305_64.Parameters
open Hacl.Symmetric.Poly1305_64.Bigint


module H8   = Hacl.UInt8
module H64  = Hacl.UInt64
module H128 = Hacl.UInt128
module U8   = FStar.UInt8
module U64  = FStar.UInt64
module U128 = FStar.UInt64

open FStar.Ghost

let p_1305: p:nat{pow2 128 < p} =
  assert_norm (pow2 128 < pow2 130 - 5);
  pow2 130 - 5

type elem = n:nat{n < p_1305}
type word = b:Seq.seq H8.byte{Seq.length b <= 16}
type word_16 = b:Seq.seq H8.byte{Seq.length b = 16}
type text = Seq.seq elem
type tag  = word_16

val field_add: elem -> elem -> Tot elem
let field_add a b = (a + b) % p_1305
val field_mul: elem -> elem -> Tot elem
let field_mul a b = (a * b) % p_1305

(* Infix field operators for readability *)
let op_Plus_At = field_add
let op_Star_At = field_mul


(* * *********************************************)
(* *            Encoding                         *)
(* * *********************************************)

open FStar.Math.Lemmas
open FStar.SeqProperties

let bytes = Seq.seq H8.t

(* Little endian integer value of a sequence of bytes *)
let rec little_endian (b:Seq.seq H8.t) : GTot (n:nat) (decreases (Seq.length b)) =
  if Seq.length b = 0 then 0
  else
    H8.v (head b) + pow2 8 * little_endian (tail b)


#reset-options "--initial_fuel 1 --max_fuel 1 --z3timeout 20"

let zerob = uint8_to_sint8 0uy

val little_endian_null: len:nat{len < 16} -> Lemma
  (little_endian (Seq.create len (uint8_to_sint8 0uy)) == 0)
let rec little_endian_null len =
  if len = 0 then ()
  else
    begin
    Seq.lemma_eq_intro (Seq.slice (Seq.create len zerob) 1 len)
		       (Seq.create (len - 1) zerob);
    assert (little_endian (Seq.create len zerob) ==
      0 + pow2 8 * little_endian (Seq.slice (Seq.create len zerob) 1 len));
    little_endian_null (len - 1)
    end

val little_endian_singleton: n:H8.t -> Lemma
  (little_endian (Seq.create 1 n) == H8.v n)
let little_endian_singleton n =
  assert (little_endian (Seq.create 1 n) ==
    H8.v (Seq.index (Seq.create 1 n) 0) + pow2 8 *
    little_endian (Seq.slice (Seq.create 1 n) 1 1))


val little_endian_append: w1:bytes -> w2:bytes -> Lemma
  (requires True)
  (ensures
    little_endian (Seq.append w1 w2) ==
    little_endian w1 + pow2 (8 * Seq.length w1) * little_endian w2)
  (decreases (Seq.length w1))
let rec little_endian_append w1 w2 =
  let open FStar.Seq in
  if length w1 = 0 then
    begin
    assert_norm (pow2 (8 * 0) == 1);
    Seq.lemma_eq_intro (append w1 w2) w2
    end
  else
    begin
    let w1' = slice w1 1 (length w1) in
    assert (length w1' == length w1 - 1);
    little_endian_append w1' w2;
    assert (index (append w1 w2) 0 == index w1 0);
    Seq.lemma_eq_intro
      (append w1' w2)
      (Seq.slice (append w1 w2) 1 (length (append w1 w2)));
    assert (little_endian (append w1 w2) ==
      H8.v (index w1 0) + pow2 8 * little_endian (append w1' w2));
    assert (little_endian (append w1' w2) ==
      little_endian w1' + pow2 (8 * length w1') * little_endian w2);
    assert (H8.v (index w1 0) + pow2 8 * little_endian (append w1' w2) ==
      H8.v (index w1 0) +
      pow2 8 * (little_endian w1' + pow2 (8 * length w1') * little_endian w2));
    Math.Lemmas.pow2_plus 8 (8 * (length w1 - 1));
    assert (pow2 8 * pow2 (8 * length w1') == pow2 (8 * length w1));
    assert (H8.v (index w1 0) + pow2 8 * little_endian (append w1' w2) ==
      H8.v (index w1 0) +
      pow2 8 * little_endian w1' + pow2 (8 * length w1) * little_endian w2);
    assert (H8.v (index w1 0) + pow2 8 * little_endian w1' == little_endian w1)
    end

private val lemma_factorise: a:nat -> b:nat -> Lemma (a + a * b == a * (b + 1))
let lemma_factorise a b = ()

val lemma_euclidean_division: r:nat -> b:nat -> q:pos -> Lemma
  (requires (r < q))
  (ensures  (r + q * b < q * (b+1)))
let lemma_euclidean_division r b q = ()

val lemma_little_endian_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (little_endian b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))
let rec lemma_little_endian_is_bounded b =
  if Seq.length b = 0 then ()
  else
    begin
    let s = Seq.slice b 1 (Seq.length b) in
    assert(Seq.length s = Seq.length b - 1);
    lemma_little_endian_is_bounded s;
    assert(H8.v (Seq.index b 0) < pow2 8);
    assert(little_endian s < pow2 (8 * Seq.length s));
    assert(little_endian b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
    lemma_euclidean_division (H8.v (Seq.index b 0)) (little_endian s) (pow2 8);
    assert(little_endian b <= pow2 8 * (little_endian s + 1));
    assert(little_endian b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (Seq.length b - 1));
    lemma_factorise 8 (Seq.length b - 1)
    end

#reset-options "--initial_fuel 0 --max_fuel 0"

val lemma_little_endian_lt_2_128: b:bytes {Seq.length b <= 16} -> Lemma
  (requires True)
  (ensures  (little_endian b < pow2 128))
  [SMTPat (little_endian b)]
let lemma_little_endian_lt_2_128 b =
  lemma_little_endian_is_bounded b;
  if Seq.length b = 16 then ()
  else Math.Lemmas.pow2_lt_compat 128 (8 * Seq.length b)


let encode (w:word) : GTot elem =
  let l = Seq.length w in
  pow2_le_compat 128 (8 * l);
  pow2 (8 * l) +@ little_endian w


val encode_pad: prefix:Seq.seq elem -> txt:Seq.seq H8.t -> GTot (Seq.seq elem) 
  (decreases (Seq.length txt))
let rec encode_pad prefix txt =
  let l = Seq.length txt in
  if l = 0 then prefix
  else if l < 16 then
    let w = txt in
    SeqProperties.snoc prefix (encode w)
  else
    begin
    let w, txt = SeqProperties.split txt 16 in
    let prefix = SeqProperties.snoc prefix (encode w) in
    encode_pad prefix txt
    end


let trunc_1305 (e:elem) : Tot elem = e % pow2 128

(* * *********************************************)
(* *          Encoding-related lemmas            *)
(* * *********************************************)

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"


#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

open FStar.Math.Lib
open FStar.Math.Lemmas

val lemma_little_endian_is_injective_0: b:word{Seq.length b > 0} -> Lemma
  (little_endian b =
   H8.v (Seq.index b 0) + pow2 8 * little_endian (Seq.slice b 1 (Seq.length b)))
let lemma_little_endian_is_injective_0 b = ()

val lemma_little_endian_is_injective_1: b:pos -> q:nat -> r:nat -> q':nat -> r':nat -> Lemma
  (requires (r < b /\ r' < b /\ r + b * q = r' + b * q'))
  (ensures  (r = r' /\ q = q'))
let lemma_little_endian_is_injective_1 b q r q' r' =
  lemma_mod_plus r q b;
  lemma_mod_plus r' q' b;
  lemma_mod_injective b r r'

val lemma_little_endian_is_injective_2: b:word -> len:pos{len <= Seq.length b} -> Lemma
  (let s = Seq.slice b (Seq.length b - len) (Seq.length b) in
   let s' = Seq.slice s 1 (Seq.length s) in
   let s'' = Seq.slice b (Seq.length b - (len - 1)) (Seq.length b) in
   s'' == s')
let lemma_little_endian_is_injective_2 b len =
  let s = Seq.slice b (Seq.length b - len) (Seq.length b) in
  let s' = Seq.slice s 1 (Seq.length s) in
  let s'' = Seq.slice b (Seq.length b - (len - 1)) (Seq.length b) in
  Seq.lemma_eq_intro s' s''

val lemma_little_endian_is_injective_3: b:word -> b':word -> len:pos{len <= Seq.length b /\ len <= Seq.length b'} -> Lemma
  (requires (Seq.slice b (Seq.length b - (len - 1)) (Seq.length b) ==
             Seq.slice b' (Seq.length b' - (len-1)) (Seq.length b')
           /\ Seq.index b (Seq.length b - len) = Seq.index b' (Seq.length b' - len)))
  (ensures  (Seq.slice b (Seq.length b - len) (Seq.length b) ==
             Seq.slice b' (Seq.length b' - len) (Seq.length b')))
let lemma_little_endian_is_injective_3 b b' len =
  Seq.lemma_eq_intro (Seq.slice b' (Seq.length b' - len) (Seq.length b'))
                     (Seq.append (Seq.create 1 (Seq.index b' (Seq.length b' - len))) (Seq.slice b' (Seq.length b' - (len-1)) (Seq.length b')));
  Seq.lemma_eq_intro (Seq.slice b (Seq.length b - len) (Seq.length b))
                     (Seq.append (Seq.create 1 (Seq.index b (Seq.length b - len))) (Seq.slice b (Seq.length b - (len-1)) (Seq.length b)))

val lemma_little_endian_is_injective: b:word -> b':word ->
  len:nat{Seq.length b >= len /\ Seq.length b' >= len} -> Lemma
  (requires (little_endian (Seq.slice b (Seq.length b - len) (Seq.length b)) =
             little_endian (Seq.slice b' (Seq.length b' - len) (Seq.length b')) ))
  (ensures  (Seq.slice b (Seq.length b - len) (Seq.length b) ==
             Seq.slice b' (Seq.length b' - len) (Seq.length b')))
let rec lemma_little_endian_is_injective b b' len =
  if len = 0 then
    Seq.lemma_eq_intro (Seq.slice b (Seq.length b - len) (Seq.length b))
                       (Seq.slice b' (Seq.length b' - len) (Seq.length b'))
  else
    begin
    let s = Seq.slice b (Seq.length b - len) (Seq.length b) in
    let s' = Seq.slice b' (Seq.length b' - len) (Seq.length b') in
    assert(Seq.length s = len /\ Seq.length s' = len);
    lemma_little_endian_is_injective_0 s; lemma_little_endian_is_injective_0 s';
    lemma_little_endian_is_injective_1 (pow2 8)
                                      (little_endian (Seq.slice s 1 (Seq.length s)))
                                      (H8.v (Seq.index s 0))
                                      (little_endian (Seq.slice s' 1 (Seq.length s')))
                                      (H8.v (Seq.index s' 0));
    lemma_little_endian_is_injective_2 b len;
    lemma_little_endian_is_injective_2 b' len;
    lemma_little_endian_is_injective b b' (len - 1);
    lemma_little_endian_is_injective_3 b b' len
    end

val lemma_encode_injective: w0:word -> w1:word -> Lemma
  (requires (Seq.length w0 == Seq.length w1 /\ encode w0 == encode w1))
  (ensures  (w0 == w1))
let lemma_encode_injective w0 w1 =
  let l = Seq.length w0 in
  lemma_little_endian_is_bounded w0;
  lemma_little_endian_is_bounded w1;
  pow2_le_compat 128 (8 * l);
  lemma_mod_plus_injective p_1305 (pow2 (8 * l))
    (little_endian w0) (little_endian w1);
  assert (little_endian w0 == little_endian w1);
  Seq.lemma_eq_intro (Seq.slice w0 0 l) w0;
  Seq.lemma_eq_intro (Seq.slice w1 0 l) w1;
  lemma_little_endian_is_injective w0 w1 l

val lemma_encode_pad_injective: p0:Seq.seq elem -> t0:Seq.seq H8.t -> p1:Seq.seq elem -> t1:Seq.seq H8.t -> Lemma
  (requires Seq.length t0 == Seq.length t1 /\ encode_pad p0 t0 == encode_pad p1 t1)
  (ensures  p0 == p1 /\ t0 == t1)
  (decreases (Seq.length t0))
let rec lemma_encode_pad_injective p0 t0 p1 t1 =
  let l = Seq.length t0 in
  if l = 0 then Seq.lemma_eq_intro t0 t1
  else if l < 16 then
    begin
    SeqProperties.lemma_append_inj
      p0 (Seq.create 1 (encode t0))
      p1 (Seq.create 1 (encode t1));
    Seq.lemma_index_create 1 (encode t0) 0;
    Seq.lemma_index_create 1 (encode t1) 0;
    lemma_encode_injective t0 t1
    end
  else
    begin
    let w0, t0' = SeqProperties.split_eq t0 16 in
    let w1, t1' = SeqProperties.split_eq t1 16 in
    let p0' = SeqProperties.snoc p0 (encode w0) in
    let p1' = SeqProperties.snoc p1 (encode w1) in
    assert (encode_pad p0' t0' == encode_pad p1' t1');
    lemma_encode_pad_injective p0' t0' p1' t1';
    SeqProperties.lemma_append_inj
      p0 (Seq.create 1 (encode w0))
      p1 (Seq.create 1 (encode w1));
    Seq.lemma_index_create 1 (encode w0) 0;
    Seq.lemma_index_create 1 (encode w1) 0;
    lemma_encode_injective w0 w1
    end

val encode_pad_empty: prefix:Seq.seq elem -> txt:Seq.seq H8.t -> Lemma
  (requires Seq.length txt == 0)
  (ensures  encode_pad prefix txt == prefix)
let encode_pad_empty prefix txt = ()

val encode_pad_snoc: prefix:Seq.seq elem -> txt:Seq.seq H8.t -> w:word_16 -> Lemma
  (encode_pad (SeqProperties.snoc prefix (encode w)) txt ==
   encode_pad prefix (Seq.append w txt))
let encode_pad_snoc prefix txt w =
  Seq.lemma_len_append w txt;
  assert (16 <= Seq.length (Seq.append w txt));
  let w', txt' = SeqProperties.split (Seq.append w txt) 16 in
  let prefix' = SeqProperties.snoc prefix (encode w') in
  Seq.lemma_eq_intro w w';
  Seq.lemma_eq_intro txt txt'

(* * *********************************************)
(* *        Poly1305 functional invariant        *)
(* * *********************************************)

let seq_head (vs:Seq.seq 'a {Seq.length vs > 0}) = Seq.slice vs 0 (Seq.length vs - 1)

val poly: vs:Seq.seq elem -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly vs r =
  if Seq.length vs = 0 then 0
  else (poly (seq_head vs) r +@ Seq.index vs (Seq.length vs - 1)) *@ r

let log_t : Type0 = erased (Seq.seq elem)

(* the definition above captures what POLY1305 does, 
   not the usual polynomial computation; 
   it may be more natural to flip the sequence, 
   so that the coefficients are aligned. 
   (i.e. a_0::a_1::a_2 stands for a_0 + a_1 X + a_2 X^2 , is implicitly extended with 0s.) *)

val poly': vs:Seq.seq elem -> r:elem -> Tot (a:elem) (decreases (Seq.length vs))
let rec poly' vs r =
  if Seq.length vs = 0 then 0
  else (SeqProperties.head vs +@ poly' (SeqProperties.tail vs) r ) *@ r

val eq_poly0: p:Seq.seq elem -> Tot bool (decreases (Seq.length p)) 
let rec eq_poly0 p = 
  Seq.length p = 0 || 
  (SeqProperties.head p = 0 && eq_poly0 (SeqProperties.tail p))
  
val eq_poly: p0:Seq.seq elem -> p1:Seq.seq elem -> Tot bool (decreases (Seq.length p0))
let rec eq_poly p0 p1 = 
  if Seq.length p0 = 0 then eq_poly0 p1 
  else if Seq.length p1 = 0 then eq_poly0 p0
  else SeqProperties.head p0 = SeqProperties.head p1 && eq_poly (SeqProperties.tail p0) (SeqProperties.tail p1)

private let fix (r:word_16) (i:nat {i < 16}) m : Tot word_16 =
  Seq.upd r i (H8 (Seq.index r i &^ m))

// an abstract spec of clamping for our state invariant
// for our polynomial-sampling assumption,
// we rely solely on the number of fixed bits (22, right?)
val clamp: word_16 -> GTot elem
let clamp r =
  assert_norm(pow2 8 > 15);
  assert_norm(pow2 8 > 252);
  let fifteen = uint8_to_sint8 15uy in
  let thft = uint8_to_sint8 252uy in
  let r = fix r  3  fifteen in // 0000****
  let r = fix r  7  fifteen in
  let r = fix r 11  fifteen in
  let r = fix r 15  fifteen in
  let r = fix r  4 thft in // ******00
  let r = fix r  8 thft in
  let r = fix r 12 thft in
  little_endian r

(** REMARK: this is equivalent to (poly vs r + little_endian s) % pow2 128 *)
val mac_1305: vs:Seq.seq elem -> r:elem -> s:Seq.seq H8.t -> GTot int
let mac_1305 vs r s = (trunc_1305 (poly vs r) + little_endian s) % pow2 128

