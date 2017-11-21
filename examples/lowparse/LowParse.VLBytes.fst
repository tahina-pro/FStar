module LowParse.VLBytes
include LowParse.Base

module Seq = FStar.Seq
module S = LowParse.Slice
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module E = FStar.Kremlin.Endianness
module IP = LowParse.Int
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

inline_for_extraction
let validate_sized
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (ps: stateful_validator p)
  (len': U32.t)
: Tot (stateful_validator (parse_sized p (U32.v len')))
= fun (input: S.bslice) ->
  let blen = S.length input in
  if U32.lt blen len'
  then begin
    None
  end else begin
    let input'  = S.truncate_slice input len'  in
    match ps input' with
    | Some consumed ->
      if consumed = len'
      then Some ((consumed <: U32.t) <: consumed_slice_length input)
      else None
    | _ -> None
  end

inline_for_extraction
let validate_sized_nochk
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (len: U32.t)
: Tot (stateful_validator_nochk (parse_sized p (U32.v len)))
= validate_constant_size_nochk len (parse_sized p (U32.v len))

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
    IP.be_to_n_inj b1 b2
  end else ()

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

#set-options "--z3rlimit 16"

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

#set-options "--z3rlimit 16"

inline_for_extraction
let parse_bounded_integer_1_synth
  (x: U8.t)
: Tot (bounded_integer 1)
= Cast.uint8_to_uint32 x

noextract
let parse_bounded_integer_1
: parser (bounded_integer 1)
= parse_synth IP.parse_u8 parse_bounded_integer_1_synth

inline_for_extraction
let parse_bounded_integer_2_synth
  (x: U16.t)
: Tot (bounded_integer 2)
= Cast.uint16_to_uint32 x

noextract
let parse_bounded_integer_2
: parser (bounded_integer 2)
= parse_synth IP.parse_u16 parse_bounded_integer_2_synth

inline_for_extraction
let parse_bounded_integer_3_synth
  (hilo: U16.t * U8.t)
: Tot (bounded_integer 3)
= let (hi, lo) = hilo in
  U32.add (Cast.uint8_to_uint32 lo) (U32.mul 256ul (Cast.uint16_to_uint32 hi))

noextract
let parse_bounded_integer_3
: parser (bounded_integer 3)
= (IP.parse_u16 `nondep_then` IP.parse_u8) `parse_synth` parse_bounded_integer_3_synth

noextract
val parse_bounded_integer'
  (i: integer_size)
: parser (bounded_integer i)

let parse_bounded_integer' = function
  | 1 -> parse_bounded_integer_1
  | 2 -> parse_bounded_integer_2
  | 3 -> parse_bounded_integer_3
  | 4 -> IP.parse_u32

#set-options "--z3rlimit 64"

let parse_bounded_integer'_correct
  (i: integer_size)
  (b: bytes32)
: Lemma
  (parse (parse_bounded_integer' i) b == parse (parse_bounded_integer i) b)
= ()

#set-options "--z3rlimit 32"

inline_for_extraction
let parse_bounded_integer_st_nochk_1
: parser_st_nochk parse_bounded_integer_1
= parse_synth_st_nochk IP.parse_u8_st_nochk parse_bounded_integer_1_synth

inline_for_extraction
let parse_bounded_integer_st_nochk_2
: parser_st_nochk parse_bounded_integer_2
= parse_synth_st_nochk IP.parse_u16_st_nochk parse_bounded_integer_2_synth

inline_for_extraction
let parse_bounded_integer_st_nochk_3
: parser_st_nochk parse_bounded_integer_3
= parse_synth_st_nochk
    (parse_nondep_then_nochk IP.parse_u16_st_nochk IP.parse_u8_st_nochk)
    parse_bounded_integer_3_synth

inline_for_extraction
val parse_bounded_integer_st_nochk'
  (i: integer_size)
: Tot (parser_st_nochk (parse_bounded_integer' i))

let parse_bounded_integer_st_nochk' i = match i with
  | 1 -> parse_bounded_integer_st_nochk_1
  | 2 -> parse_bounded_integer_st_nochk_2
  | 3 -> parse_bounded_integer_st_nochk_3
  | 4 -> IP.parse_u32_st_nochk

inline_for_extraction
let parse_bounded_integer_st_nochk
  (i: integer_size)
: Tot (parser_st_nochk (parse_bounded_integer i))
= fun (b: S.bslice) ->
    Classical.forall_intro (parse_bounded_integer'_correct i);
    parse_bounded_integer_st_nochk' i b

inline_for_extraction
let parse_bounded_integer_st
  (i: integer_size)
: Tot (parser_st (parse_bounded_integer i))
= parse_total_constant_size (U32.uint_to_t i) (parse_bounded_integer_st_nochk i)

inline_for_extraction
let validate_vlbytes_payload
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (pv: stateful_validator p)
  (i: bounded_integer sz { f i == true } )
: Tot (stateful_validator (parse_vlbytes_payload sz f p i))
= validate_sized pv i

inline_for_extraction
let validate_vlbytes_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (pv: stateful_validator p)
: Tot (stateful_validator (parse_vlbytes_gen sz f p))
= parse_sized_and_then_cases_injective sz f p;
  parse_then_check
    #false
    #_
    #(weaken (parse_filter (parse_bounded_integer sz) f))
    (parse_filter_st (parse_bounded_integer_st sz) f)
    #_
    #(parse_vlbytes_payload sz f p)
    (validate_vlbytes_payload sz f pv)

inline_for_extraction
val validate_vlbytes
  (sz: integer_size)
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (pv: stateful_validator p)
: Tot (stateful_validator (parse_vlbytes sz p))

let validate_vlbytes sz #b #t #p pv =
  validate_vlbytes_gen sz (unconstrained_bounded_integer sz) #b #t #p pv

inline_for_extraction
let validate_vlbytes_payload_nochk
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (len: bounded_integer sz { f len == true } )
: Tot (stateful_validator_nochk (parse_vlbytes_payload sz f p len))
= validate_sized_nochk p len

inline_for_extraction
let validate_vlbytes_gen_nochk
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Tot (stateful_validator_nochk (parse_vlbytes_gen sz f p))
= parse_sized_and_then_cases_injective sz f p;
  parse_nochk_then_nochk
    #false
    #_
    #(weaken (parse_filter (parse_bounded_integer sz) f))
    (parse_filter_st_nochk (parse_bounded_integer_st_nochk sz) f)
    #_
    #(parse_vlbytes_payload sz f p)
    (validate_vlbytes_payload_nochk sz f p)

inline_for_extraction
val validate_vlbytes_nochk
  (sz: integer_size)
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Tot (stateful_validator_nochk (parse_vlbytes sz p))

let validate_vlbytes_nochk sz #b #t p =
  validate_vlbytes_gen_nochk sz (unconstrained_bounded_integer sz) p

inline_for_extraction
val point_to_vlbytes_contents
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    parses h (parse_vlbytes_gen sz f p) b (fun _ -> True)
  ))
  (ensures (fun h0 b' h1 ->
    S.modifies_none h0 h1 /\
    sz <= U32.v (S.length b) /\ (
    let sz' = U32.uint_to_t sz in
    let b1 = S.truncated_slice b sz' in
    S.is_prefix_gen [b1; b'] b /\
    parses h0 (parse_vlbytes_gen sz f p) b (fun (v, len) ->
    exactly_parses h0 p b' (fun v' ->
    U32.v sz' <= U32.v len /\
    S.length b' == U32.sub len sz' /\
    v == v'
  )))))

#set-options "--z3rlimit 64"

let point_to_vlbytes_contents sz f #b #t p b =
  let (len, _) = parse_bounded_integer_st_nochk sz b in
  let b1 = S.advance_slice b (U32.uint_to_t sz) in
  S.truncate_slice b1 len

#set-options "--z3rlimit 32"

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

inline_for_extraction
let validate_bounded_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (pv: stateful_validator p)
: Tot (stateful_validator (parse_bounded_vlbytes min max p))
= let sz : integer_size = log256 max in
  validate_vlbytes_gen sz (in_bounds min max) #b #t #p pv

inline_for_extraction
let validate_bounded_vlbytes_nochk
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Tot (stateful_validator_nochk (parse_bounded_vlbytes min max p))
= let sz = log256 max in
  validate_vlbytes_gen_nochk sz (in_bounds min max) #b #t p
