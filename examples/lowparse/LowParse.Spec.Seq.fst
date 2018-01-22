module LowParse.Spec.Seq
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module L = FStar.List.Tot
module PL = LowParse.Spec.List
module U32 = FStar.UInt32
module Classical = FStar.Classical

(* Parse a list, until there is nothing left to read. This parser will mostly fail EXCEPT if the whole size is known and the slice has been suitably truncated beforehand, or if the elements of the list all have a known constant size. *)

val parse_seq_aux
  (#t: Type0)
  (p: bare_parser t)
  (b: bytes)
: Tot (option (Seq.seq t * (consumed_length b)))
  (decreases (Seq.length b))

let rec parse_seq_aux #t p b =
  if Seq.length b = 0
  then 
    Some (Seq.createEmpty, (0 <: consumed_length b))
  else
    match p b with
    | None -> None
    | Some (v, n) ->
      if n = 0
      then None (* elements cannot be empty *)
      else
        match parse_seq_aux p (Seq.slice b n (Seq.length b)) with
	| Some (l, n') -> Some (Seq.cons v l, (n + n' <: consumed_length b))
	| _ -> None

let seq_of_list_inj
  (t: Type0)
: Lemma
  (forall (l1 l2 : list t) . Seq.seq_of_list l1 == Seq.seq_of_list l2 ==> l1 == l2)
= Classical.forall_intro (Seq.lemma_list_seq_bij #t)

let parse_seq'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser ParserConsumesAll (Seq.seq t))
= seq_of_list_inj t;
  parse_synth (PL.parse_list p) (Seq.seq_of_list)

val parse_seq_aux_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: Lemma
  (ensures (
    parse (parse_seq_aux p) b == parse (parse_seq' p) b
  ))
  (decreases (Seq.length b))

#set-options "--z3rlimit 32"

let rec parse_seq_aux_correct #k #t p b =
  if Seq.length b = 0
  then ()
  else
    match parse p b with
    | Some (v, n) ->
      if n = 0
      then ()
      else
	let b' = Seq.slice b n (Seq.length b) in
	parse_seq_aux_correct p b'
    | _ -> ()

#reset-options

let parse_seq
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (parser ParserConsumesAll (Seq.seq t))
= Classical.forall_intro (parse_seq_aux_correct p);
  no_lookahead_weak_ext (parse_seq' p) (parse_seq_aux p);
  injective_ext (parse_seq' p) (parse_seq_aux p);
  no_lookahead_ext (parse_seq' p) (parse_seq_aux p);
  parse_seq_aux p

let parse_seq_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: Lemma
  (parse (parse_seq p) b == parse (parse_seq' p) b)
= parse_seq_aux_correct p b

val seq_length_constant_size_parser_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (b: bytes)
: Lemma
  (requires (
    Some? (parse (parse_seq p) b)
  ))
  (ensures (
    let pb = parse (parse_seq p) b in
    Some? pb /\ (
    let (Some (l, _)) = pb in
    FStar.Mul.op_Star (Seq.length l) (get_constant_size_parser_size p) == Seq.length b
  )))

let seq_length_constant_size_parser_correct #k #t p b =
  parse_seq_correct p b;
  PL.list_length_constant_size_parser_correct p b
