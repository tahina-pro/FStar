module LowParse.Spec.VLData
include LowParse.Spec.FLData
include LowParse.Spec.Int

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast

let integer_size : Type0 = (sz: nat { 1 <= sz /\ sz <= 4 } )

inline_for_extraction
let bounded_integer
  (i: integer_size)
: Tot Type0
= (u: U32.t { U32.v u < pow2 (FStar.Mul.op_Star 8 i) } )

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --z3refresh"

let decode_bounded_integer
  (i: integer_size)
  (b: bytes { Seq.length b == i } )
: Tot (bounded_integer i)
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)

let decode_bounded_integer_injective'
  (i: integer_size)
  (b1: bytes { Seq.length b1 == i } )
  (b2: bytes { Seq.length b2 == i } )
: Lemma
  (decode_bounded_integer i b1 == decode_bounded_integer i b2 ==> Seq.equal b1 b2)
= if decode_bounded_integer i b1 = decode_bounded_integer i b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U32.v (U32.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    be_to_n_inj b1 b2
  end else ()

#reset-options

let decode_bounded_integer_injective
  (i: integer_size)
: Lemma
  (forall
    (b1: bytes { Seq.length b1 == i } )
    (b2: bytes { Seq.length b2 == i } )
  . decode_bounded_integer i b1 == decode_bounded_integer i b2 ==> Seq.equal b1 b2
  )
= Classical.forall_intro_2 (decode_bounded_integer_injective' i)

// unfold
let parse_bounded_integer_kind
  (i: integer_size)
: Tot parser_kind
= {
    parser_kind_low = i;
    parser_kind_high = Some i;
    parser_kind_total = true;
    parser_kind_subkind = Some ParserStrong;
  }

inline_for_extraction
let parse_bounded_integer
  (i: integer_size)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i))
= decode_bounded_integer_injective i;
  make_total_constant_size_parser i (bounded_integer i) (decode_bounded_integer i)

// unfold
let parse_vldata_payload_kind
: parser_kind
= {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_total = false;
    parser_kind_subkind = Some ParserStrong;
  }

inline_for_extraction
let parse_vldata_payload
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (i: bounded_integer sz { f i == true } )
: Tot (parser parse_vldata_payload_kind t)
= weaken parse_vldata_payload_kind (parse_fldata p (U32.v i))

#set-options "--z3rlimit 16"

let parse_fldata_and_then_cases_injective
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Lemma
  (and_then_cases_injective (parse_vldata_payload sz f p))
= let g
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1 b2: bytes)
  : Lemma
    (requires (and_then_cases_injective_precond (parse_vldata_payload sz f p) len1 len2 b1 b2))
    (ensures (len1 == len2))
  = assert (injective_precond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (injective_postcond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (len1 == len2)
  in
  let g'
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1: bytes)
  : Lemma
    (forall (b2: bytes) . and_then_cases_injective_precond (parse_vldata_payload sz f p) len1 len2 b1 b2 ==> len1 == len2)
  = Classical.forall_intro (Classical.move_requires (g len1 len2 b1))
  in
  Classical.forall_intro_3 g'

#reset-options

// unfold
let parse_vldata_gen_kind
  (sz: integer_size)
: parser_kind
= {
    parser_kind_low = sz;
    parser_kind_high = None;
    parser_kind_total = false;
    parser_kind_subkind = Some ParserStrong;
  }

let parse_vldata_gen_kind_correct
  (sz: integer_size)
: Lemma
  ( (parse_vldata_gen_kind sz) == (and_then_kind (parse_filter_kind (parse_bounded_integer_kind sz)) parse_vldata_payload_kind))
= let kl = parse_vldata_gen_kind sz in
  let kr = and_then_kind (parse_filter_kind (parse_bounded_integer_kind sz)) parse_vldata_payload_kind in
  assert_norm (kl == kr)

inline_for_extraction
let parse_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser (parse_vldata_gen_kind sz) t)
= parse_fldata_and_then_cases_injective sz f p;
  parse_vldata_gen_kind_correct sz;
  (parse_filter (parse_bounded_integer sz) f)
  `and_then`
  parse_vldata_payload sz f p

inline_for_extraction
let unconstrained_bounded_integer
  (sz: integer_size)
  (i: bounded_integer sz)
: Tot bool
= true

inline_for_extraction
let parse_vldata
  (sz: integer_size)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser _ t)
= parse_vldata_gen sz (unconstrained_bounded_integer sz) p


(** Explicit bounds on size *)

inline_for_extraction
val log256'
  (n: nat)
: Pure nat
  (requires (n > 0 /\ n < 4294967296))
  (ensures (fun l ->
    1 <= l /\
    l <= 4 /\
    pow2 (FStar.Mul.op_Star 8 (l - 1)) <= n /\
    n < pow2 (FStar.Mul.op_Star 8 l)
  ))

#set-options "--z3rlimit 16"

let log256' n =
  assert (n < pow2 32);
  let z0 = 1 in
  let z1 = Prims.op_Multiply 256 z0 in
  let l = 1 in
  assert_norm (pow2 (Prims.op_Multiply 8 l) == z1);
  assert_norm (pow2 (Prims.op_Multiply 8 (l - 1)) == z0);
  if n < z1
  then begin
    assert (normalize_term (pow2 (Prims.op_Multiply 8 (l - 1))) <= n);
    assert (n < normalize_term (pow2 (Prims.op_Multiply 8 l)));
    l
  end else begin
    let z2 = Prims.op_Multiply 256 z1 in
    let l = l + 1 in
    assert_norm (pow2 (Prims.op_Multiply 8 l) == z2);
    if n < z2
    then begin
      assert (normalize_term (pow2 (Prims.op_Multiply 8 (l - 1))) <= n);
      assert (n < normalize_term (pow2 (Prims.op_Multiply 8 l)));
      l
    end else begin
      let z3 = Prims.op_Multiply 256 z2 in
      let l = l + 1 in
      assert_norm (pow2 (Prims.op_Multiply 8 l) == z3);
      if n < z3
      then begin
	assert (normalize_term (pow2 (Prims.op_Multiply 8 (l - 1))) <= n);
	assert (n < normalize_term (pow2 (Prims.op_Multiply 8 l)));
        l    
      end else begin
        let l = l + 1 in
        assert_norm (pow2 (Prims.op_Multiply 8 l) == Prims.op_Multiply 256 z3);
	assert (normalize_term (pow2 (Prims.op_Multiply 8 (l - 1))) <= n);
	assert (n < normalize_term (pow2 (Prims.op_Multiply 8 l)));
        l
      end
    end
  end

#reset-options

(*
inline_for_extraction
val log256
  (n: U32.t)
: Pure nat
  (requires (U32.v n > 0))
  (ensures (fun l ->
    1 <= l /\
    l <= 4 /\
    pow2 (FStar.Mul.op_Star 8 (l - 1)) <= U32.v n /\
    U32.v n < pow2 (FStar.Mul.op_Star 8 l)
  ))

let log256 n =
  log256' (U32.v n)
*)

inline_for_extraction
let in_bounds
  (min: nat)
  (max: nat)
  (x: U32.t)
: Tot bool
= not (U32.v x < min || max < U32.v x)

// unfold
let parse_bounded_vldata_kind
  (min: nat)
  (max: nat)
: Pure parser_kind
  (requires (min <= max /\ max > 0 /\ max < 4294967296 ))
  (ensures (fun _ -> True))
= {
    parser_kind_low = log256' max + min;
    parser_kind_high = Some (log256' max + max);
    parser_kind_total = false;
    parser_kind_subkind = Some ParserStrong;
  }

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --z3refresh"

let parse_bounded_vldata_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Lemma
  (parser_kind_prop (parse_bounded_vldata_kind min max) (parse_vldata_gen (log256' max) (in_bounds min max) p))
= let sz : integer_size = log256' max in
  let p' = parse_vldata_gen sz (in_bounds min max) p in
  let prf
    (input: bytes)
  : Lemma
    (requires (Some? (parse p' input)))
    (ensures (
      let pi = parse p' input in
      Some? pi /\ (
      let (Some (_, consumed)) = pi in
      sz + min <= (consumed <: nat) /\
      (consumed <: nat) <= sz + max
    )))
  = let klen = parse_filter_kind (parse_bounded_integer_kind sz) in
    let plen : parser klen _ = parse_filter (parse_bounded_integer sz) (in_bounds min max) in
    let plen_res = parse plen input in
    assert (Some? plen_res);
    let (Some (len, clen)) = plen_res in
    let f1 () : Lemma ((clen <: nat) == (sz <: nat)) =
      parser_kind_prop_intro klen plen;
      assert_norm (klen.parser_kind_low == (sz <: nat));
      assert_norm (klen.parser_kind_high == Some (sz <: nat));
      is_constant_size_parser_equiv sz plen;
      assert ((clen <: nat) == (sz <: nat))
    in
    let f2 () : Lemma (in_bounds min max len) = () in
    let input' = Seq.slice input clen (Seq.length input) in
    let kp = parse_fldata_kind (U32.v len) in
    let pp : parser kp _ = parse_fldata p (U32.v len) in
    let pp_res = parse pp input' in
    assert (Some? pp_res);
    let (Some (_, cp)) = pp_res in
    let f3 () : Lemma ((cp <: nat) == U32.v len) =
      parser_kind_prop_intro kp pp;
      assert_norm (kp.parser_kind_low == U32.v len);
      assert_norm (kp.parser_kind_high == Some (U32.v len));
      is_constant_size_parser_equiv (U32.v len) pp;
      assert ((cp <: nat) == U32.v len)
    in
    let (Some (_, consumed)) = parse p' input in
    let f () : Lemma
      (sz + min <= (consumed <: nat) /\
       ((consumed <: nat) <= sz + max))
    = assert ((consumed <: nat) == (clen <: nat) + (cp <: nat));
      f1 ();
      f2 ();
      f3 ()
    in
    f ()
  in
  Classical.forall_intro (Classical.move_requires prf)

#reset-options

inline_for_extraction
let parse_bounded_vldata
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser (parse_bounded_vldata_kind min max) t)
= parse_bounded_vldata_correct min max p;
  strengthen (parse_bounded_vldata_kind min max) (parse_vldata_gen (log256' max) (in_bounds min max) p)
