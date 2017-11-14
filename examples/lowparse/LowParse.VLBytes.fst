module LowParse.VLBytes
include LowParse.Base

module Seq = FStar.Seq
module S = LowParse.Slice
module U32 = FStar.UInt32

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

let parse_vlbytes'
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

let parse_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (p: parser t)
: Tot (parser t)
= let sz : integer_size = log256 max in
  parse_vlbytes' min max p sz

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
let validate_vlbytes'
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (#p: parser t)
  (pv: stateful_validator p)
  (sz: integer_size { sz == log256 max } )
: Tot (stateful_validator (parse_vlbytes' min max p sz))
= parse_then_check
    #_
    #(parse_filter (parse_bounded_integer sz) (in_bounds min max))
    (parse_filter_st (parse_bounded_integer_st sz) (in_bounds min max))
    #_
    #(fun len -> parse_sized p (U32.v len))
    (fun len -> validate_sized pv len)

inline_for_extraction
let validate_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (#p: parser t)
  (pv: stateful_validator p)
: Tot (stateful_validator (parse_vlbytes min max p))
= let sz = log256 max in
  validate_vlbytes' min max pv sz

inline_for_extraction
let validate_vlbytes_nochk'
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (p: parser t)
  (sz: integer_size { sz == log256 max } )
: Tot (stateful_validator_nochk (parse_vlbytes' min max p sz))
= parse_nochk_then_nochk
    #_
    #(parse_filter (parse_bounded_integer sz) (in_bounds min max))
    (parse_filter_st_nochk (parse_bounded_integer_st_nochk sz) (in_bounds min max))
    #_
    #(fun len -> parse_sized p (U32.v len))
    (fun len -> validate_sized_nochk p len)

inline_for_extraction
let validate_vlbytes_nochk
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#t: Type0)
  (p: parser t)
: Tot (stateful_validator_nochk (parse_vlbytes min max p))
= let sz = log256 max in
  validate_vlbytes_nochk' min max p sz

(*

val point_to_vlbytes1_contents
  (#t: Type0)
  (#p: parser t)
  (ps: stateful_validator p)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    S.live h b /\ (
    let s = S.as_seq h b in (
    Some? (parse_vlbytes1 p s)
  ))))
  (ensures (fun h0 b' h1 ->
    B.modifies_none h0 h1 /\
    S.live h0 b /\
    S.live h0 b' /\ (
    let s = S.as_seq h0 b in
    let v = parse_vlbytes1 p s in (
    Some? v /\ (
    let (Some (v', consumed)) = v in (
    B.includes (S.truncated_slice b (U32.uint_to_t consumed)).S.p b'.S.p /\
    (
    let s' = S.as_seq h1 b' in
    let v'' = p s' in (
    Some? v'' /\ (
    let (Some (v'', len')) = v'' in (
    v'' == v' /\
    len' == U32.v (S.BSlice?.len b')
  ))))))))))

#set-options "--z3rlimit 16"

let point_to_vlbytes1_contents #t #p ps b =
  let h0 = HST.get () in
  let v = parse_u8_st b in
  assert (Some? v);
  let (Some (len, off1)) = v in
  let b1 = S.advance_slice b off1 in
  assert (b1.S.p == B.sub b.S.p off1 (U32.sub b.S.len off1));
  let len' = FStar.Int.Cast.uint8_to_uint32 len in
  assert (U32.v len' <= U32.v (S.BSlice?.len b1));
  let b' = S.truncate_slice b1 len' in
  assert (b1.S.p == B.sub b.S.p off1 (U32.sub b.S.len off1));
  assert (b'.S.p == B.sub b1.S.p 0ul len');
  let f () : Lemma
  (
    let s = S.as_seq h0 b in
    let (Some (_, consumed)) = parse_vlbytes1 p s in
    b'.S.p == B.sub (B.sub b.S.p 0ul (U32.uint_to_t consumed)) off1 len'
  )
  = let s = S.as_seq h0 b in
    let (Some (_, consumed)) = parse_vlbytes1 p s in
    B.sub_sub b.S.p 0ul (U32.uint_to_t consumed) off1 len';
    B.sub_sub b.S.p off1 (U32.sub b.S.len off1) 0ul len'
  in
  f ();
  b'
*)
