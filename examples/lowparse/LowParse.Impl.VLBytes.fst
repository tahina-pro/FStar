module LowParse.Impl.VLBytes
include LowParse.Impl.Combinators
include LowParse.Impl.Int
include LowParse.Spec.VLBytes

module Seq = FStar.Seq
module S = LowParse.Slice
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast

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

inline_for_extraction
let parse_bounded_integer_1_synth
  (x: U8.t)
: Tot (bounded_integer 1)
= Cast.uint8_to_uint32 x

noextract
let parse_bounded_integer_1
: parser (bounded_integer 1)
= parse_synth parse_u8 parse_bounded_integer_1_synth

inline_for_extraction
let parse_bounded_integer_2_synth
  (x: U16.t)
: Tot (bounded_integer 2)
= Cast.uint16_to_uint32 x

noextract
let parse_bounded_integer_2
: parser (bounded_integer 2)
= parse_synth parse_u16 parse_bounded_integer_2_synth

#set-options "--z3rlimit 32"

inline_for_extraction
let parse_bounded_integer_3_synth
  (hilo: U16.t * U8.t)
: Tot (bounded_integer 3)
= let (hi, lo) = hilo in
  U32.add (Cast.uint8_to_uint32 lo) (U32.mul 256ul (Cast.uint16_to_uint32 hi))

#reset-options

noextract
let parse_bounded_integer_3
: parser (bounded_integer 3)
= (parse_u16 `nondep_then` parse_u8) `parse_synth` parse_bounded_integer_3_synth

noextract
val parse_bounded_integer'
  (i: integer_size)
: parser (bounded_integer i)

let parse_bounded_integer' = function
  | 1 -> parse_bounded_integer_1
  | 2 -> parse_bounded_integer_2
  | 3 -> parse_bounded_integer_3
  | 4 -> parse_u32

#set-options "--z3rlimit 256"

let parse_bounded_integer'_correct
  (i: integer_size)
  (b: bytes32)
: Lemma
  (parse (parse_bounded_integer' i) b == parse (parse_bounded_integer i) b)
= ()

#reset-options

inline_for_extraction
let parse_bounded_integer_st_nochk_1
: parser_st_nochk parse_bounded_integer_1
= parse_synth_st_nochk parse_u8_st_nochk parse_bounded_integer_1_synth

inline_for_extraction
let parse_bounded_integer_st_nochk_2
: parser_st_nochk parse_bounded_integer_2
= parse_synth_st_nochk parse_u16_st_nochk parse_bounded_integer_2_synth

inline_for_extraction
let parse_bounded_integer_st_nochk_3
: parser_st_nochk parse_bounded_integer_3
= parse_synth_st_nochk
    (parse_nondep_then_nochk parse_u16_st_nochk parse_u8_st_nochk)
    parse_bounded_integer_3_synth

inline_for_extraction
val parse_bounded_integer_st_nochk'
  (i: integer_size)
: Tot (parser_st_nochk (parse_bounded_integer' i))

let parse_bounded_integer_st_nochk' i = match i with
  | 1 -> parse_bounded_integer_st_nochk_1
  | 2 -> parse_bounded_integer_st_nochk_2
  | 3 -> parse_bounded_integer_st_nochk_3
  | 4 -> parse_u32_st_nochk

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
