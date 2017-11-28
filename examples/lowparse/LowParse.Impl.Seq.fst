module LowParse.Impl.Seq
include LowParse.Impl.Combinators
include LowParse.Spec.Seq

module Seq = FStar.Seq
module L = FStar.List.Tot
module S = LowParse.Slice
module PL = LowParse.Impl.List
module B = FStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module Classical = FStar.Classical
module G = FStar.Ghost

let parse_seq_exactly_parses
  (h: HS.mem)
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (s: S.bslice)
  (pred: ((Seq.seq t * consumed_slice_length s) -> GTot Type0))
: Lemma
  (requires (parses h (parse_seq p) s pred))
  (ensures (exactly_parses h (parse_seq p) s (fun v -> pred (v, S.length s))))
= parse_seq_correct p (S.as_seq h s);
  let pred' (input: list t * consumed_slice_length s) : GTot Type0 =
    let (l, len) = input in
    pred (Seq.seq_of_list l, len)
  in
  PL.parse_list_exactly_parses h p s pred'

val seq_length
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
: HST.Stack U32.t
  (requires (fun h ->
    parses h (parse_seq p) b (fun _ -> True)
  ))
  (ensures (fun h i h' ->
    S.modifies_none h h' /\
    parses h (parse_seq p) b (fun (l, _) ->
    Seq.length l == U32.v i
  )))

let seq_length #b #t #p sv b =
  let h = HST.get () in
  parse_seq_correct p (S.as_seq h b);
  PL.list_length sv b

inline_for_extraction
val seq_length_constant_size_parser
  (#n: U32.t)
  (#b: bool)
  (#t: Type0)
  (p: constant_size_parser b (U32.v n) t)
  (b: S.bslice)
: HST.Stack U32.t
  (requires (fun h ->
    U32.v n <> 0 /\
    parses h (parse_seq p) b (fun _ -> True)
  ))
  (ensures (fun h i h' ->
    S.modifies_none h h' /\
    parses h (parse_seq p) b (fun (l, _) ->
    Seq.length l == U32.v i
  )))

let seq_length_constant_size_parser #n #b #t p b =
  let h = HST.get () in
  parse_seq_correct p (S.as_seq h b);
  PL.list_length_constant_size_parser p b

(* TODO: move to FStar.Seq.Properties *)

val index_seq_of_list
  (#a: Type)
  (l: list a)
  (i: nat)
: Lemma
  (requires (i < L.length l))
  (ensures (
    i < L.length l /\
    i < Seq.length (Seq.seq_of_list l) /\
    Seq.index (Seq.seq_of_list l) i == L.index l i
  ))
  (decreases i)
  [SMTPat (Seq.index (Seq.seq_of_list l) i)]

let rec index_seq_of_list #a l i =
  if i = 0
  then ()
  else
    let (_ :: l') = l in
    index_seq_of_list l' (i - 1)

val seq_index_spec
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: S.bslice)
  (i: U32.t)
  (h: HS.mem)
: Ghost(* Do not remove this comment or add any whitespace before it,
    this is to guard against gtot_to_tot.sh *)
    S.bslice
  (requires (
    parses h (parse_seq p) b (fun (l, _) ->
    U32.v i < Seq.length l
  )))
  (ensures (fun b' ->
    S.includes b b' /\
    parses h (parse_seq p) b (fun (l, _) ->
    exactly_parses h p b' (fun (x) ->
    U32.v i < Seq.length l /\
    x == Seq.index l (U32.v i)
  ))))

let seq_index_spec #b #t p b i h =
  parse_seq_correct p (S.as_seq h b);
  PL.list_nth_spec p b i h

val seq_index_spec_ext
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: S.bslice)
  (i: U32.t)
  (h h': HS.mem)
: Lemma
  (requires (
    parses h (parse_seq p) b (fun (l, _) -> U32.v i < Seq.length l) /\
    S.live h' b /\
    S.as_seq h' b == S.as_seq h b
  ))
  (ensures (
    parses h (parse_seq p) b (fun (l, _) -> U32.v i < Seq.length l) /\
    parses h' (parse_seq p) b (fun (l, _) -> U32.v i < Seq.length l) /\
    seq_index_spec p b i h' == seq_index_spec p b i h
  ))

let seq_index_spec_ext #b #t p b i h h' =
  parse_seq_correct p (S.as_seq h b);
  PL.list_nth_spec_ext p b i h h'

val seq_index_spec_disjoint
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: S.bslice)
  (i j: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    U32.v i <> U32.v j /\
    parses h (parse_seq p) b (fun (l, _) ->
    U32.v i < Seq.length l /\
    U32.v j < Seq.length l
  )))
  (ensures (
    U32.v i <> U32.v j /\
    parses h (parse_seq p) b (fun (l, _) ->
    U32.v i < Seq.length l /\
    U32.v j < Seq.length l /\
    S.disjoint (seq_index_spec p b i h) (seq_index_spec p b j h)
  )))

let seq_index_spec_disjoint #b #t p b i j h =
  parse_seq_correct p (S.as_seq h b);
  PL.list_nth_spec_disjoint p b i j h

inline_for_extraction
val seq_index
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
: HST.Stack S.bslice
  (requires (fun h ->
    parses h (parse_seq p) b (fun (l, _) ->
    U32.v i < Seq.length l
  )))
  (ensures (fun h b' h' ->
    S.modifies_none h h' /\
    S.includes b b' /\
    parses h (parse_seq p) b (fun (l, _) ->
      U32.v i < Seq.length l
    ) /\
    b' == seq_index_spec p b i h
  ))

let seq_index #b #t p sv b i =
  let h = HST.get () in
  parse_seq_correct p (S.as_seq h b);
  PL.list_nth p sv b i

inline_for_extraction
val seq_index_constant_size_parser
  (#n: U32.t)
  (#b: bool)
  (#t: Type0)
  (p: constant_size_parser b (U32.v n) t)
  (b: S.bslice)
  (i: U32.t)
: HST.Stack S.bslice
  (requires (fun h ->
    parses h (parse_seq p) b (fun (l, _) ->
    U32.v i < Seq.length l
  )))
  (ensures (fun h b' h' ->
    S.modifies_none h h' /\
    S.includes b b' /\
    parses h (parse_seq p) b (fun (l, _) ->
      U32.v i < Seq.length l
    ) /\
    b' == seq_index_spec p b i h
  ))

let seq_index_constant_size_parser #n #b #t p b i =
  let h = HST.get () in
  parse_seq_correct p (S.as_seq h b);
  PL.list_nth_constant_size_parser p b i

inline_for_extraction
val validate_seq
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (sv: stateful_validator p)
: Tot (stateful_validator (parse_seq p))

let validate_seq #b #t #p sv =
  fun (input: S.bslice) ->
    let h = HST.get () in
    parse_seq_correct p (S.as_seq h input);
    seq_of_list_inj t;
    validate_synth (PL.validate_list sv) (Seq.seq_of_list) input

let seq_prefix_length_spec_nat_postcond
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (input: bytes32)
  (i: nat)
  (result: nat)
: GTot Type0
=   result <= Seq.length input /\ (
    let v = parse (parse_seq p) input in
    let inputl : bytes32 = Seq.slice input 0 result in
    let vl = parse (parse_seq p) inputl in
    let inputr : bytes32 = Seq.slice input result (Seq.length input) in
    let vr = parse (parse_seq p) inputr in
    Some? v /\
    Some? vl /\
    Some? vr /\ (
    let (Some (s, _)) = v in
    let (Some (sl, _)) = vl in
    let (Some (sr, _)) = vr in
    i <= Seq.length s /\
    sl == Seq.slice s 0 i /\
    sr == Seq.slice s i (Seq.length s)
  ))

(* TODO: move to FStar.Seq *)

let slice_cons_r
  (#t: Type0)
  (hd: t)
  (tl: Seq.seq t)
  (lo hi: nat)
: Lemma
  (requires (
    1 <= lo /\  lo <= hi /\ hi <= Seq.length tl + 1
  ))
  (ensures (
    1 <= lo /\  lo <= hi /\ hi <= Seq.length tl + 1 /\
    Seq.slice (Seq.cons hd tl) lo hi == Seq.slice tl (lo - 1) (hi - 1)
  ))
//  [SMTPat (Seq.slice (Seq.cons hd tl) lo hi)]
= assert (Seq.equal (Seq.slice (Seq.cons hd tl) lo hi) (Seq.slice tl (lo - 1) (hi - 1)))

let slice_cons_l
  (#t: Type0)
  (hd: t)
  (tl: Seq.seq t)
  (hi: nat)
: Lemma
  (requires (
    1 <= hi /\ hi <= Seq.length tl + 1
  ))
  (ensures (
    1 <= hi /\ hi <= Seq.length tl + 1 /\
    Seq.slice (Seq.cons hd tl) 0 hi == Seq.cons hd (Seq.slice tl 0 (hi - 1))
  ))
//  [SMTPat (Seq.slice (Seq.cons hd tl) 0 hi)]
= assert (Seq.equal (Seq.slice (Seq.cons hd tl) 0 hi) (Seq.cons hd (Seq.slice tl 0 (hi - 1))))

val seq_prefix_length_spec_nat
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (input: bytes32)
  (i: nat)
: Ghost nat
  (requires (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i <= Seq.length s
  )))
  (ensures (fun _ -> True))
  (decreases i)

let rec seq_prefix_length_spec_nat #b #t p input i =
  if i = 0
  then 0
  else
    let (Some (_, len)) = parse p input in
    let intl : bytes32 = Seq.slice input len (Seq.length input) in
    let len' = seq_prefix_length_spec_nat p intl (i - 1) in
    len + len'

val seq_prefix_length_spec_nat_correct
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (input: bytes32)
  (i: nat)
: Lemma
  (requires (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i <= Seq.length s
  )))
  (ensures (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i <= Seq.length s /\
    seq_prefix_length_spec_nat_postcond p input i (seq_prefix_length_spec_nat p input i)
  )))
  (decreases i)
  [SMTPat (seq_prefix_length_spec_nat p input i)]

#set-options "--z3rlimit 128  --smtencoding.l_arith_repr native"

let rec seq_prefix_length_spec_nat_correct #b #t p input i =
  if i = 0
  then ()
  else begin
    let (Some (hd, len)) = parse p input in
    let inhd : bytes32 = Seq.slice input 0 len in
    let intl : bytes32 = Seq.slice input len (Seq.length input) in
    let result' = seq_prefix_length_spec_nat p intl (i - 1) in
    seq_prefix_length_spec_nat_correct p intl (i - 1);
    let inputl' : bytes32 = Seq.slice intl 0 result' in
    let inputr' : bytes32 = Seq.slice intl result' (Seq.length intl) in
    let result = len + result' in
    assert (result <= Seq.length input);
    let inputl : bytes32 = Seq.slice input 0 result in
    let inputr : bytes32 = Seq.slice input result (Seq.length input) in
    assert (no_lookahead_weak_on _ p input inputl);
    let (Some (hd', len')) = parse p inputl in
    assert (hd == hd');
    assert ((len <: nat) == (len' <: nat));
    assert (inputl' == Seq.slice inputl len (Seq.length inputl));
    let vl = parse (parse_seq p) inputl in
    assert (Some? vl);
    assert (inputr' == inputr);
    let vr = parse (parse_seq p) inputr in
    assert (Some? vr);
    let (Some (sl, _)) = vl in
    let (Some (sr, _)) = vr in
    let (Some (sl', _)) = parse (parse_seq p) inputl' in
    let (Some (s, _)) = parse (parse_seq p) input in
    let (Some (s', _)) = parse (parse_seq p) intl in
    assert (s == Seq.cons hd s');
    assert (i - 1 <= Seq.length s');
    // works here, but I prefer to speed up the proof somewhat
    assert (sl == Seq.cons hd sl');
    slice_cons_r hd s' i (Seq.length s);
    assert (sr == Seq.slice s i (Seq.length s));
    slice_cons_l hd s' i;
    assert (sl == Seq.slice s 0 i);
    assert (seq_prefix_length_spec_nat_postcond p input i result);
    ()
  end

#reset-options

val seq_prefix_length_spec
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (input: S.bslice)
  (h: HS.mem)
  (i: U32.t)
: Ghost U32.t
  (requires (
    parses h (parse_seq p) input (fun (s, _) ->
    U32.v i <= Seq.length s
  )))
  (ensures (fun result ->
    U32.v result <= U32.v (S.length input) /\ (
    let sleft = S.truncated_slice input result in
    let sright = S.advanced_slice input result in
    parses h (parse_seq p) input (fun (s, _) ->
    parses h (parse_seq p) sleft (fun (sl, _) ->
    parses h (parse_seq p) sright (fun (sr, _) ->
    U32.v i <= Seq.length s /\
    sl == Seq.slice s 0 (U32.v i) /\
    sr == Seq.slice s (U32.v i) (Seq.length s)
  ))))))

let seq_prefix_length_spec #b #t p input h i =
  U32.uint_to_t (seq_prefix_length_spec_nat p (S.as_seq h input) (U32.v i))

val seq_prefix_length_spec_nat_add
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (input: bytes32)
  (i1 i2: nat)
: Lemma
  (requires (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i1 <= Seq.length s /\
    i2 <= Seq.length s - i1
  )))
  (ensures (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i1 <= Seq.length s /\
    i2 <= Seq.length s - i1 /\ (
    let len1 = seq_prefix_length_spec_nat p input i1 in
    let input2 : bytes32 = Seq.slice input len1 (Seq.length input) in
    let len2 = seq_prefix_length_spec_nat p input2 i2 in
    seq_prefix_length_spec_nat p input (i1 + i2) == len1 + len2
  ))))
  (decreases i1)

#set-options "--z3rlimit 64 --smtencoding.l_arith_repr native"

let rec seq_prefix_length_spec_nat_add #b #t p input i1 i2 =
  if i1 = 0
  then ()
  else begin
    let (Some (_, len)) = parse p input in
    let input' : bytes32 = Seq.slice input len (Seq.length input) in
    let res = seq_prefix_length_spec_nat p input (i1 + i2) in
    let (Some _) = parse (parse_seq p) input in
    let (Some _) = parse (parse_seq p) input' in
    let res' = seq_prefix_length_spec_nat p input' (i1 - 1 + i2) in
    assert (res == len + res');
    seq_prefix_length_spec_nat_add p input' (i1 - 1) i2;
    let len1' = seq_prefix_length_spec_nat p input' (i1 - 1) in
    let input2' : bytes32 = Seq.slice input' len1' (Seq.length input') in
    let len2' = seq_prefix_length_spec_nat p input2' i2 in
    assert (res' == len1' + len2');
    let len1 = seq_prefix_length_spec_nat p input i1 in
    assert (len1 == len + len1');
    let input2 : bytes32 = Seq.slice input len1 (Seq.length input) in
    let f () : Lemma (input2 == input2') =
      Seq.slice_slice input len (Seq.length input) len1' (Seq.length input')
    in
    f ();
    let len2 = seq_prefix_length_spec_nat p input2 i2 in
    assert (res == len1 + len2)
  end

#reset-options

let seq_offset_at_inv
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
  (h0: G.erased HS.mem)
  (sl: B.buffer U32.t)
  (h: HS.mem)
  (j: nat)
: GTot Type0
= B.disjoint (S.as_buffer b) sl /\
  B.length sl == 1 /\
  B.modifies_1 sl (G.reveal h0) h /\
  parses (G.reveal h0) (parse_seq p) b (fun (s, _) ->
    U32.v i <= Seq.length s
  ) /\
  j <= U32.v i /\
  B.live h sl /\ (
    let i' = Seq.index (B.as_seq h sl) 0 in
    i' == seq_prefix_length_spec p b (G.reveal h0) (U32.uint_to_t j)
  )

inline_for_extraction
val seq_offset_at_advance
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
  (h0: G.erased HS.mem)
  (sl: B.buffer U32.t)
  (j: U32.t)
: HST.Stack unit
  (requires (fun h ->
    seq_offset_at_inv p sv b i h0 sl h (U32.v j) /\
    U32.v j < U32.v i
  ))
  (ensures (fun h1 _ h2 ->
    seq_offset_at_inv p sv b i h0 sl h1 (U32.v j) /\
    U32.v j < U32.v i /\
    seq_offset_at_inv p sv b i h0 sl h2 (U32.v j + 1)
  ))

#set-options "--z3rlimit 16"

let seq_offset_at_advance #b #t p sv b i h0 sl j =
  let h1 = HST.get () in
  let i1 = B.index sl 0ul in
  let b' = S.advance_slice b i1 in
  let len = sv b' in
  let i2 = U32.add i1 len in
  let h2 = HST.get () in
  assert (B.modifies_none h1 h2);
  B.upd sl 0ul i2;
  seq_prefix_length_spec_nat_add p (S.as_seq (G.reveal h0) b) (U32.v j) (U32.v i - U32.v j);
  seq_prefix_length_spec_nat_add p (S.as_seq (G.reveal h0) b) (U32.v j) 1;
  seq_prefix_length_spec_nat_add p (S.as_seq (G.reveal h0) b) (U32.v j + 1) (U32.v i - (U32.v j + 1));
  let h3 = HST.get () in
  B.lemma_modifies_none_1_trans sl h1 h2 h3

#reset-options

inline_for_extraction
val seq_offset_at
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    parses h (parse_seq p) b (fun (s, _) ->
    U32.v i <= Seq.length s
  )))
  (ensures (fun h1 res h2 ->
    S.modifies_none h1 h2 /\
    parses h1 (parse_seq p) b (fun (s, _) ->
      U32.v i <= Seq.length s
    ) /\
    res == seq_prefix_length_spec p b h1 i
  ))

let seq_offset_at #b #t p sv b i =
  let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let sl : B.buffer U32.t = B.create 0ul 1ul in
  let h2 = HST.get () in
  C.Loops.for
    0ul
    i
    (fun h j -> seq_offset_at_inv p sv b i (G.hide h2) sl h j)
    (fun j -> seq_offset_at_advance p sv b i (G.hide h2) sl j)
  ;
  let res = B.index sl 0ul in  
  let h3 = HST.get () in
  B.lemma_modifies_0_1' sl h1 h2 h3;
  HST.pop_frame ();
  let h4 = HST.get () in
  B.lemma_modifies_0_push_pop h0 h1 h3 h4;
  res
