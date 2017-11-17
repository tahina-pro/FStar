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
val parse_sized
  (#t: Type0)
  (p: parser t)
  (sz: nat)
: Tot (constant_size_parser sz t)

let parse_sized #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes32) ->
  if Seq.length s < sz
  then None
  else
    let (sz: consumed_length s) = sz in
    match p (Seq.slice s 0 sz) with
    | Some (v, consumed) ->
      if (consumed <: nat) = (sz <: nat)
      then Some (v, sz)
      else None
    | _ -> None

let parse_sized_injective
  (#t: Type0)
  (p: parser t)
  (sz: nat)
: Lemma
  (requires (injective p))
  (ensures (injective (parse_sized p sz)))
= let f
    (b1 b2: bytes32)
  : Lemma
    (requires (injective_precond (parse_sized p sz) b1 b2))
    (ensures (injective_postcond (parse_sized p sz) b1 b2))
  = assert (injective_precond p (Seq.slice b1 0 sz) (Seq.slice b2 0 sz))
  in
  Classical.forall_intro_2 (fun b -> Classical.move_requires (f b))

inline_for_extraction
let validate_sized
  (#t: Type0)
  (#p: parser t)
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
  (#t: Type0)
  (p: parser t)
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

noextract
val parse_bounded_integer
  (i: integer_size)
: Tot (total_constant_size_parser i (bounded_integer i))

let parse_bounded_integer i =
  make_total_constant_size_parser i (bounded_integer i) (decode_bounded_integer i)

let decode_bounded_integer_injective
  (i: integer_size)
  (b1: bytes32 { Seq.length b1 == i } )
  (b2: bytes32 { Seq.length b2 == i } )
: Lemma
  (decode_bounded_integer i b1 == decode_bounded_integer i b2 ==> b1 == b2)
= if decode_bounded_integer i b1 = decode_bounded_integer i b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U32.v (U32.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    IP.be_to_n_inj b1 b2
  end else ()

let parse_bounded_integer_injective
  (i: integer_size)
: Lemma
  (injective (parse_bounded_integer i))
= Classical.forall_intro_2 (decode_bounded_integer_injective i);
  make_total_constant_size_parser_injective i (bounded_integer i) (decode_bounded_integer i)

noextract
let parse_vlbytes
  (sz: integer_size)
  (#t: Type0)
  (p: parser t)
: Tot (parser t)
= let parse_payload (len: bounded_integer sz) : Tot (parser t) =
    parse_sized p (U32.v len)
  in
  (parse_bounded_integer sz)
  `and_then`
  parse_payload

#set-options "--z3rlimit 16"

let parse_vlbytes_injective
  (sz: integer_size)
  (#t: Type0)
  (p: parser t)
: Lemma
  (requires (injective p))
  (ensures (injective (parse_vlbytes sz p)))
= let parse_payload (len: bounded_integer sz) : Tot (parser t) =
    parse_sized p (U32.v len)
  in
  let f
    (len: bounded_integer sz)
  : Lemma
    (injective (parse_payload len))
  = parse_sized_injective p (U32.v len)
  in
  let g
    (len1 len2: bounded_integer sz)
    (b1 b2: bytes32)
  : Lemma
    (requires (and_then_cases_injective_precond parse_payload len1 len2 b1 b2))
    (ensures (len1 == len2))
  = assert (injective_precond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (injective_postcond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (len1 == len2)
  in
  let g' () : Lemma
    (and_then_cases_injective parse_payload)
  = Classical.forall_intro_3 (fun (len1 len2: bounded_integer sz) (b1: bytes32) -> Classical.forall_intro (Classical.move_requires (g len1 len2 b1)))
  in
  g' ();
  Classical.forall_intro (Classical.move_requires f);
  parse_bounded_integer_injective sz;
  let f' () :
    Lemma (injective (parse_vlbytes sz p))
  = and_then_injective (parse_bounded_integer sz) parse_payload
  in
  f' ()

noextract
val parse_bounded_integer'
  (i: integer_size)
: parser (bounded_integer i)

let parse_bounded_integer' = function
  | 1 -> parse_synth IP.parse_u8 (fun x -> Cast.uint8_to_uint32 x <: bounded_integer 1)
  | 2 -> parse_synth IP.parse_u16 (fun x -> Cast.uint16_to_uint32 x <: bounded_integer 2)
  | 3 -> (IP.parse_u16 `nondep_then` IP.parse_u8)
	`parse_synth` (fun (hilo : U16.t * U8.t) ->
	  let (hi, lo) = hilo in
	  U32.add (Cast.uint8_to_uint32 lo) (U32.mul 256ul (Cast.uint16_to_uint32 hi)) <: bounded_integer 3
	)
  | 4 -> IP.parse_u32

#set-options "--z3rlimit 64"

let parse_bounded_integer'_correct
  (i: integer_size)
  (b: bytes32)
: Lemma
  (parse (parse_bounded_integer' i) b == parse (parse_bounded_integer i) b)
= ()

#set-options "--z3rlimit 16"

inline_for_extraction
val parse_bounded_integer_st_nochk'
  (i: integer_size)
: Tot (parser_st_nochk (parse_bounded_integer' i))

let parse_bounded_integer_st_nochk' = function
  | 1 -> parse_synth_st_nochk IP.parse_u8_st_nochk (fun x -> Cast.uint8_to_uint32 x <: bounded_integer 1)
  | 2 -> parse_synth_st_nochk IP.parse_u16_st_nochk (fun x -> Cast.uint16_to_uint32 x <: bounded_integer 2)
  | 3 -> parse_synth_st_nochk
	  (parse_nondep_then_nochk IP.parse_u16_st_nochk IP.parse_u8_st_nochk)
	  (fun (hilo : U16.t * U8.t) ->
	    let (hi, lo) = hilo in
	    U32.add (Cast.uint8_to_uint32 lo) (U32.mul 256ul (Cast.uint16_to_uint32 hi)) <: bounded_integer 3
	  )
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
let validate_vlbytes
  (sz: integer_size)
  (#t: Type0)
  (#p: parser t)
  (pv: stateful_validator p)
: Tot (stateful_validator (parse_vlbytes sz p))
= parse_then_check
    #_
    #(parse_bounded_integer sz)
    (parse_bounded_integer_st sz)
    #_
    #(fun (len: bounded_integer sz) -> parse_sized p (U32.v len))
    (fun (len: bounded_integer sz) -> validate_sized pv len)

inline_for_extraction
let validate_vlbytes_nochk
  (sz: integer_size)
  (#t: Type0)
  (p: parser t)
: Tot (stateful_validator_nochk (parse_vlbytes sz p))
= parse_nochk_then_nochk
    #_
    #(parse_bounded_integer sz)
    (parse_bounded_integer_st_nochk sz)
    #_
    #(fun (len: bounded_integer sz) -> parse_sized p (U32.v len))
    (fun (len: bounded_integer sz) -> validate_sized_nochk p len)

inline_for_extraction
val point_to_vlbytes_contents
  (#t: Type0)
  (p: parser t)
  (sz: integer_size)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    parses h (parse_vlbytes sz p) b (fun _ -> True)
  ))
  (ensures (fun h0 b' h1 ->
    S.modifies_none h0 h1 /\
    sz <= U32.v (S.length b) /\ (
    let sz' = U32.uint_to_t sz in
    let b1 = S.truncated_slice b sz' in
    S.is_prefix_gen [b1; b'] b /\
    parses h0 (parse_vlbytes sz p) b (fun (v, len) ->
    exactly_parses h0 p b' (fun v' ->
    U32.v sz' <= U32.v len /\
    S.length b' == U32.sub len sz' /\
    v == v'
  )))))

#set-options "--z3rlimit 32"

let point_to_vlbytes_contents #t p sz b =
  let (len, _) = parse_bounded_integer_st_nochk sz b in
  let b1 = S.advance_slice b (U32.uint_to_t sz) in
  S.truncate_slice b1 len

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
let parse_bounded_vlbytes'
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (p: parser t)
  (sz: integer_size { sz == log256 max } )
: Tot (parser t)
= parse_filter
    (parse_bounded_integer sz)
    (in_bounds min max)
  `and_then`
  (fun len ->
    parse_sized p (U32.v len)
  )

noextract
let parse_bounded_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (p: parser t)
: Tot (parser t)
= let sz : integer_size = log256 max in
  parse_bounded_vlbytes' min max p sz

let parse_bounded_vlbytes_parse_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (h: HS.mem)
  (p: parser t)
  (b: S.bslice)
  (pred: ((t * consumed_slice_length b) -> GTot Type0))
: Lemma
  (requires (parses h (parse_bounded_vlbytes min max p) b pred))
  (ensures (parses h (parse_vlbytes (log256 max) p) b pred))
= ()

inline_for_extraction
let validate_bounded_vlbytes'
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (#p: parser t)
  (pv: stateful_validator p)
  (sz: integer_size { sz == log256 max } )
: Tot (stateful_validator (parse_bounded_vlbytes' min max p sz))
= parse_then_check
    #_
    #(parse_filter (parse_bounded_integer sz) (in_bounds min max))
    (parse_filter_st (parse_bounded_integer_st sz) (in_bounds min max))
    #_
    #(fun len -> parse_sized p (U32.v len))
    (fun len -> validate_sized pv len)

inline_for_extraction
let validate_bounded_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (#p: parser t)
  (pv: stateful_validator p)
: Tot (stateful_validator (parse_bounded_vlbytes min max p))
= let sz = log256 max in
  validate_bounded_vlbytes' min max pv sz

inline_for_extraction
let validate_bounded_vlbytes_nochk'
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (p: parser t)
  (sz: integer_size { sz == log256 max } )
: Tot (stateful_validator_nochk (parse_bounded_vlbytes' min max p sz))
= parse_nochk_then_nochk
    #_
    #(parse_filter (parse_bounded_integer sz) (in_bounds min max))
    (parse_filter_st_nochk (parse_bounded_integer_st_nochk sz) (in_bounds min max))
    #_
    #(fun len -> parse_sized p (U32.v len))
    (fun len -> validate_sized_nochk p len)

inline_for_extraction
let validate_bounded_vlbytes_nochk
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (p: parser t)
: Tot (stateful_validator_nochk (parse_bounded_vlbytes min max p))
= let sz = log256 max in
  validate_bounded_vlbytes_nochk' min max p sz
