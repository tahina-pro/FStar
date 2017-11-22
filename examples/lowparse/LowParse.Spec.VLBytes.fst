module LowParse.Spec.VLBytes
include LowParse.Spec.Combinators
include LowParse.Spec.Int

module Seq = FStar.Seq
module S = LowParse.Slice
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast

noextract
val parse_sized'
  (#t: Type0)
  (p: bare_parser t)
  (sz: nat)
: Tot (bare_parser t)

let parse_sized' #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes32) ->
  if Seq.length s < sz
  then None
  else
    match p (Seq.slice s 0 sz) with
    | Some (v, consumed) ->
      if (consumed <: nat) = (sz <: nat)
      then Some (v, (sz <: consumed_length s))
      else None
    | _ -> None

let parse_sized_injective
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sz: nat)
: Lemma
  (ensures (injective (parse_sized' p sz)))
= let f
    (b1 b2: bytes32)
  : Lemma
    (requires (injective_precond (parse_sized' p sz) b1 b2))
    (ensures (injective_postcond (parse_sized' p sz) b1 b2))
  = assert (injective_precond p (Seq.slice b1 0 sz) (Seq.slice b2 0 sz))
  in
  Classical.forall_intro_2 (fun b -> Classical.move_requires (f b))

noextract
val parse_sized
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sz: nat)
: Tot (constant_size_parser false sz t)

let parse_sized #b #t p sz =
  parse_sized_injective p sz;
  parse_sized' p sz  

let integer_size : Type0 = (sz: nat { 1 <= sz /\ sz <= 4 } )

inline_for_extraction
let bounded_integer
  (i: integer_size)
: Tot Type0
= (u: U32.t { U32.v u < pow2 (FStar.Mul.op_Star 8 i) } )

let decode_bounded_integer
  (i: integer_size)
  (b: bytes32 { Seq.length b == i } )
: Tot (bounded_integer i)
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)

#set-options "--z3rlimit 32"

let decode_bounded_integer_injective
  (i: integer_size)
  (b1: bytes32 { Seq.length b1 == i } )
  (b2: bytes32 { Seq.length b2 == i } )
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

noextract
val parse_bounded_integer
  (i: integer_size)
: Tot (total_constant_size_parser i (bounded_integer i))

let parse_bounded_integer i =
  Classical.forall_intro_2 (decode_bounded_integer_injective i);
  make_total_constant_size_parser i (bounded_integer i) (decode_bounded_integer i)

noextract
let parse_vlbytes_payload
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (i: bounded_integer sz { f i == true } )
: Tot (weak_parser t)
= parse_sized p (U32.v i)

let parse_sized_and_then_cases_injective
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Lemma
  (and_then_cases_injective (parse_vlbytes_payload sz f p))
= let g
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1 b2: bytes32)
  : Lemma
    (requires (and_then_cases_injective_precond (parse_vlbytes_payload sz f p) len1 len2 b1 b2))
    (ensures (len1 == len2))
  = assert (injective_precond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (injective_postcond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (len1 == len2)
  in
  let g'
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1: bytes32)
  : Lemma
    (forall (b2: bytes32) . and_then_cases_injective_precond (parse_vlbytes_payload sz f p) len1 len2 b1 b2 ==> len1 == len2)
  = Classical.forall_intro (Classical.move_requires (g len1 len2 b1))
  in
  Classical.forall_intro_3 g'

noextract
let parse_vlbytes_gen'
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Tot (weak_parser t)
= parse_sized_and_then_cases_injective sz f p;
  (weaken (parse_filter (parse_bounded_integer sz) f))
  `and_then`
  parse_vlbytes_payload sz f p

#set-options "--z3rlimit 64"

let parse_vlbytes_gen_no_lookahead_on
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (x x' : bytes32)
: Lemma
  (requires (
    no_lookahead_on_precond t (parse_vlbytes_gen' sz f p) x x'
  ))
  (ensures (
    no_lookahead_on_postcond t (parse_vlbytes_gen' sz f p) x x'
  ))
= assert (Some? (parse (parse_vlbytes_gen' sz f p) x));
  let (Some v) = parse (parse_vlbytes_gen' sz f p) x in
  let (y, off) = v in
  assert (off <= Seq.length x');
  assert (Seq.slice x' 0 off == Seq.slice x 0 off);
  assert (Some? (parse (parse_filter (parse_bounded_integer sz) f) x));
  let (Some v1) = parse (parse_filter (parse_bounded_integer sz) f) x in
  let (len1, off1) = v1 in
  assert (off1 <= off);
  assert (Seq.slice x' 0 off1 == Seq.slice (Seq.slice x' 0 off) 0 off1);
  assert (Seq.slice x 0 off1 == Seq.slice (Seq.slice x 0 off) 0 off1);
  assert (Seq.slice x' 0 off1 == Seq.slice x 0 off1);
  assert (no_lookahead_on_precond _ (parse_filter (parse_bounded_integer sz) f) x x');
  assert (no_lookahead_on_postcond _ (parse_filter (parse_bounded_integer sz) f) x x');
  let (Some v2) = parse (parse_filter (parse_bounded_integer sz) f) x in
  let (len2, off2) = v2 in
  assert (len1 == len2);
  assert ((off1 <: nat) == (off2 <: nat));
  assert (off == off1 + U32.v len1);
  assert (Seq.slice x off1 off == Seq.slice (Seq.slice x 0 off) off1 off);
  assert (Seq.slice x' off2 off == Seq.slice (Seq.slice x' 0 off) off2 off);
  assert (Seq.slice x' off2 off == Seq.slice x off1 off);
  assert (Some? (parse (parse_vlbytes_gen' sz f p) x'));
  let (Some v') = parse (parse_vlbytes_gen' sz f p) x' in
  let (y', _) = v' in
  assert (y' == y)

#reset-options

noextract
let parse_vlbytes_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Tot (parser t)
= Classical.forall_intro_2 (fun (x: bytes32) -> Classical.move_requires (parse_vlbytes_gen_no_lookahead_on sz f p x));
  strengthen (parse_vlbytes_gen' sz f p)

inline_for_extraction
let unconstrained_bounded_integer
  (sz: integer_size)
  (i: bounded_integer sz)
: Tot bool
= true

noextract
let parse_vlbytes
  (sz: integer_size)
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Tot (parser t)
= parse_vlbytes_gen sz (unconstrained_bounded_integer sz) p


(** Explicit bounds on size *)

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
  let z0 = 1ul in
  let z1 = U32.mul 256ul z0 in
  let l = 1 in
  assert_norm (pow2 (FStar.Mul.op_Star 8 l) == U32.v z1);
  assert_norm (pow2 (FStar.Mul.op_Star 8 (l - 1)) == U32.v z0);
  if U32.lt n z1
  then
    l
  else begin
    let z2 = U32.mul 256ul z1 in
    let l = l + 1 in
    assert_norm (pow2 (FStar.Mul.op_Star 8 l) == U32.v z2);
    if U32.lt n z2
    then
      l
    else begin
      let z3 = U32.mul 256ul z2 in
      let l = l + 1 in
      assert_norm (pow2 (FStar.Mul.op_Star 8 l) == U32.v z3);
      if U32.lt n z3
      then
        l    
      else begin
        let l = l + 1 in
        assert_norm (pow2 (FStar.Mul.op_Star 8 l) == FStar.Mul.op_Star 256 (U32.v z3));
        l
      end
    end
  end

inline_for_extraction
let in_bounds
  (min: U32.t)
  (max: U32.t)
  (x: U32.t)
: Tot bool
= not (U32.lt x min || U32.lt max x)

noextract
let parse_bounded_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Tot (parser t)
= let sz : integer_size = log256 max in
  parse_vlbytes_gen sz (in_bounds min max) p

#set-options "--z3rlimit 64"

let parse_bounded_vlbytes_parse_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#b: bool)
  (#t: Type0)
  (h: HS.mem)
  (p: parser' b t)
  (b: S.bslice)
  (pred: ((t * consumed_slice_length b) -> GTot Type0))
: Lemma
  (requires (parses h (parse_bounded_vlbytes min max p) b pred))
  (ensures (parses h (parse_vlbytes (log256 max) p) b pred))
= ()

#reset-options
