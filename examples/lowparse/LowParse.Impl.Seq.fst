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

