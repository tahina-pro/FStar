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
  (b: bytes32)
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
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Tot (weak_parser (Seq.seq t))
= seq_of_list_inj t;
  parse_synth (PL.parse_list p) (Seq.seq_of_list)

val parse_seq_aux_correct
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: bytes32)
: Lemma
  (ensures (
    parse (parse_seq_aux p) b == parse (parse_seq' p) b
  ))
  (decreases (Seq.length b))

let rec parse_seq_aux_correct #b #t p b =
  if Seq.length b = 0
  then ()
  else
    match p b with
    | Some (v, n) ->
      if n = 0
      then ()
      else
	let b' = Seq.slice b n (Seq.length b) in
	parse_seq_aux_correct p b'
    | _ -> ()

let parse_seq
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Tot (weak_parser (Seq.seq t))
= Classical.forall_intro (parse_seq_aux_correct p);
  no_lookahead_weak_ext (parse_seq' p) (parse_seq_aux p);
  injective_ext (parse_seq' p) (parse_seq_aux p);
  no_lookahead_ext (parse_seq' p) (parse_seq_aux p);
  parse_seq_aux p

let parse_seq_correct
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: bytes32)
: Lemma
  (parse (parse_seq p) b == parse (parse_seq' p) b)
= parse_seq_aux_correct p b
