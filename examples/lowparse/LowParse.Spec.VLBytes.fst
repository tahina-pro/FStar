module LowParse.Spec.VLBytes
include LowParse.Spec.FLBytes
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

let decode_bounded_integer
  (i: integer_size)
  (b: bytes { Seq.length b == i } )
: Tot (bounded_integer i)
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)

#set-options "--z3rlimit 32"

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

inline_for_extraction
let parse_bounded_integer
  (i: integer_size)
: Tot (parser _ (bounded_integer i))
= decode_bounded_integer_injective i;
  make_total_constant_size_parser i (bounded_integer i) (decode_bounded_integer i)

inline_for_extraction
let parse_vlbytes_payload
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (i: bounded_integer sz { f i == true } )
: Tot (parser (ParserStrong (StrongParserKind StrongUnknown false ())) t)
= weaken (ParserStrong (StrongParserKind StrongUnknown false ())) (parse_flbytes p (U32.v i))

#set-options "--z3rlimit 16"

let parse_flbytes_and_then_cases_injective
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Lemma
  (and_then_cases_injective (parse_vlbytes_payload sz f p))
= let g
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1 b2: bytes)
  : Lemma
    (requires (and_then_cases_injective_precond (parse_vlbytes_payload sz f p) len1 len2 b1 b2))
    (ensures (len1 == len2))
  = assert (injective_precond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (injective_postcond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (len1 == len2)
  in
  let g'
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1: bytes)
  : Lemma
    (forall (b2: bytes) . and_then_cases_injective_precond (parse_vlbytes_payload sz f p) len1 len2 b1 b2 ==> len1 == len2)
  = Classical.forall_intro (Classical.move_requires (g len1 len2 b1))
  in
  Classical.forall_intro_3 g'

#reset-options

inline_for_extraction
let parse_vlbytes_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser (ParserStrong (StrongParserKind StrongUnknown true ())) t)
= parse_flbytes_and_then_cases_injective sz f p;
  (parse_filter (parse_bounded_integer sz) f)
  `and_then`
  parse_vlbytes_payload sz f p

inline_for_extraction
let unconstrained_bounded_integer
  (sz: integer_size)
  (i: bounded_integer sz)
: Tot bool
= true

inline_for_extraction
let parse_vlbytes
  (sz: integer_size)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser _ t)
= parse_vlbytes_gen sz (unconstrained_bounded_integer sz) p


(** Explicit bounds on size *)

inline_for_extraction
val log256'
  (n: nat)
: Pure nat
  (requires (n > 0 /\ n < pow2 32))
  (ensures (fun l ->
    1 <= l /\
    l <= 4 /\
    pow2 (FStar.Mul.op_Star 8 (l - 1)) <= n /\
    n < pow2 (FStar.Mul.op_Star 8 l)
  ))

let log256' n =
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

inline_for_extraction
let in_bounds
  (min: U32.t)
  (max: U32.t)
  (x: U32.t)
: Tot bool
= not (U32.lt x min || U32.lt max x)

inline_for_extraction
let parse_bounded_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser _ t)
= let sz : integer_size = log256 max in
  parse_vlbytes_gen sz (in_bounds min max) p
