module LowParse.VLBytes
include LowParse.Base

module Seq = FStar.Seq
module S = LowParse.Slice
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

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

assume
val parse_bounded_integer
  (i: integer_size)
: Tot (total_constant_size_parser i (bounded_integer i))

let parse_vlbytes
  (sz: integer_size)
  (#t: Type0)
  (p: parser t)
: Tot (parser t)
= (parse_bounded_integer sz)
  `and_then`
  (fun len ->
    parse_sized p (U32.v len)
  )

assume
val parse_bounded_integer_st_nochk
  (i: integer_size)
: Tot (parser_st_nochk (parse_bounded_integer i))

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
    #(fun len -> parse_sized p (U32.v len))
    (fun len -> validate_sized pv len)

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
    #(fun len -> parse_sized p (U32.v len))
    (fun len -> validate_sized_nochk p len)

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

#set-options "--z3rlimit 16"

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
