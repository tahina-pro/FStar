module LowParse.Impl.VLBytes.Part5
include LowParse.Impl.VLBytes.Part3
include LowParse.Impl.VLBytes.Part4

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
    point_to_vlbytes_contents_postcond sz f p b h0 b'
  ))

#set-options "--z3rlimit 16"

let point_to_vlbytes_contents sz f #b #t p b =
  let h = HST.get () in
  let (len, _) = parse_bounded_integer_st_nochk sz b in
  let b1 = S.advance_slice b (U32.uint_to_t sz) in
  let b' = S.truncate_slice b1 len in
  assert (point_to_vlbytes_contents_correct_precond sz f p b h len b1 b');
  point_to_vlbytes_contents_correct sz f p b h len b1 b';
  b'

#reset-options

#set-options "--z3rlimit 256"

let serialize_vlbytes_gen_correct
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b b1 b2: S.bslice)
  (h: HS.mem)
: Lemma
  (requires (
    S.is_concat b b1 b2 /\ (
    let len = S.length b2 in
    U32.v len < pow2 (FStar.Mul.op_Star 8 sz) /\
    f (len <: bounded_integer sz) == true /\
    exactly_parses h (parse_bounded_integer sz) b1 (fun v -> (v <: U32.t) == len) /\
    exactly_parses h p b2 (fun _ -> True)
  )))
  (ensures (
    exactly_parses h (parse_vlbytes_gen sz f p) b (fun v ->
    exactly_parses h p b2 (fun v' ->
    v == v'
  ))))
= assert (no_lookahead_on _ (parse_bounded_integer sz) (S.as_seq h b1) (S.as_seq h b));
  assert (injective_postcond (parse_bounded_integer sz) (S.as_seq h b1) (S.as_seq h b))

#reset-options

module B = FStar.Buffer

inline_for_extraction
val serialize_bounded_integer_3
  (i: bounded_integer 3)
  (dest: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.live h dest /\
    U32.v (S.length dest) >= 3
  ))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    U32.v (S.length destl) == 3 /\
    S.live h' destr /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    exactly_parses h' parse_bounded_integer_3 destl (fun i' ->
    i' == i
  )))

#set-options "--z3rlimit 128 --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"

let serialize_bounded_integer_3 i dest =
  let h = HST.get () in
  let lo = Cast.uint32_to_uint8 (U32.rem i 256ul) in
  let i' = U32.div i 256ul in
  assert (U32.v i' < pow2 16);
  assert (U32.v i' % pow2 16 == U32.v i');
  let hi = Cast.uint32_to_uint16 i' in
  assert (i == U32.add (Cast.uint8_to_uint32 lo) (U32.mul 256ul (Cast.uint16_to_uint32 hi)));
  let (dhi, d1) = serialize_u16 hi dest in
  let h1 = HST.get () in
  let (dlo, destr) = serialize_u8 lo d1 in
  let destl = S.truncate_slice dest 3ul in
  let f1 () : Lemma (S.is_concat destl dhi dlo) =
    assert (dhi == S.truncated_slice destl 2ul);
    assert (dlo == S.advanced_slice destl 2ul);
    S.is_concat_intro destl 2ul
  in
  f1 ();
  let f2 () : Lemma (S.is_concat dest destl destr) =
    assert (destl == S.truncated_slice dest 3ul);
    assert (destr == S.advanced_slice dest 3ul);
    S.is_concat_intro dest 3ul
  in
  f2 ();
  let h' = HST.get () in
  assert (S.as_seq h' dhi == S.as_seq h1 dhi);
  serialize_nondep_then_correct parse_u16 parse_u8 destl dhi dlo h';
  assert (B.modifies_1 (S.as_buffer destl) h h');
  (destl, destr)

#reset-options

inline_for_extraction
val serialize_bounded_integer
  (sz: integer_size)
  (i: bounded_integer sz)
  (dest: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.live h dest /\
    U32.v (S.length dest) >= sz
  ))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    U32.v (S.length destl) == sz /\
    S.live h' destr /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    exactly_parses h' (parse_bounded_integer sz) destl (fun i' ->
    i' == i
  )))

#set-options "--z3rlimit 16"

let serialize_bounded_integer sz i dest =
  Classical.forall_intro (parse_bounded_integer'_correct sz);
  match sz with
  | 1 -> 
    assert (U32.v i < pow2 8);
    assert (U32.v i % pow2 8 == U32.v i);
    assert (Cast.uint8_to_uint32 (Cast.uint32_to_uint8 i) == i);
    let (destl, destr) = serialize_u8 (Cast.uint32_to_uint8 i) dest in
    (destl, destr)
  | 2 ->
    assert (U32.v i < pow2 16);
    assert (U32.v i % pow2 16 == U32.v i);
    assert (Cast.uint16_to_uint32 (Cast.uint32_to_uint16 i) == i);
    let (destl, destr) = serialize_u16 (Cast.uint32_to_uint16 i) dest in
    (destl, destr)
  | 4 ->
    let (destl, destr) = serialize_u32 i dest in
    (destl, destr)
  | 3 ->
    let (destl, destr) = serialize_bounded_integer_3 i dest in
    (destl, destr)

#reset-options
