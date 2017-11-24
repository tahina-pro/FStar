module LowParse.Spec.List
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module L = FStar.List.Tot
module S = LowParse.Slice
module B = FStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module Classical = FStar.Classical

(* Parse a list, until there is nothing left to read. This parser will mostly fail EXCEPT if the whole size is known and the slice has been suitably truncated beforehand, or if the elements of the list all have a known constant size. *)

noextract
val parse_list_aux
  (#t: Type0)
  (p: bare_parser t)
  (b: bytes32)
: GTot (option (list t * (consumed_length b)))
  (decreases (Seq.length b))

let rec parse_list_aux #t p b =
  if Seq.length b = 0
  then 
    Some ([], (0 <: consumed_length b))
  else
    match p b with
    | None -> None
    | Some (v, n) ->
      if n = 0
      then None (* elements cannot be empty *)
      else
        match parse_list_aux p (Seq.slice b n (Seq.length b)) with
	| Some (l, n') -> Some (v :: l, (n + n' <: consumed_length b))
	| _ -> None

noextract
val parse_list_bare
  (#t: Type0)
  (p: bare_parser t)
: Tot (bare_parser (list t))

let parse_list_bare #t p = (fun b -> parse_list_aux #t p b) <: bare_parser (list t)

noextract
let rec parse_list_bare_consumed
  (#t: Type0)
  (p: bare_parser t)
  (b: bytes32)
: Lemma
  (requires (Some? (parse_list_bare p b)))
  (ensures (
    let pb = parse_list_bare p b in (
    Some? pb /\ (
    let (Some (_, consumed)) = pb in
    consumed == Seq.length b
  ))))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then ()
  else
    let (Some (_, consumed1)) = p b in
    let b' = Seq.slice b consumed1 (Seq.length b) in
    parse_list_bare_consumed p b'

let no_lookahead_weak_on_parse_list_bare
  (#t: Type0)
  (p: bare_parser t)
  (x x' : bytes32)
: Lemma
  (no_lookahead_weak_on (list t) (parse_list_bare p) x x')
= match parse_list_bare p x with
  | Some _ -> parse_list_bare_consumed p x
  | _ -> ()

let parse_list_bare_injective
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Lemma
  (ensures (injective (parse_list_bare p)))
= let f () : Lemma
    (injective p)
  = ()
  in
  let rec aux
    (b1: bytes32)
    (b2: bytes32)
  : Lemma
    (requires (injective_precond (parse_list_bare p) b1 b2))
    (ensures (injective_postcond (parse_list_bare p) b1 b2))
    (decreases (Seq.length b1 + Seq.length b2))
  = if Seq.length b1 = 0
    then begin
      () // assert (Seq.equal b1 b2)
    end else begin
      assert (injective_precond p b1 b2);
      f ();
      assert (injective_postcond p b1 b2);
      let (Some (_, len1)) = parse p b1 in
      let (Some (_, len2)) = parse p b2 in
      assert ((len1 <: nat) == (len2 <: nat));
      let b1' : bytes32 = Seq.slice b1 len1 (Seq.length b1) in
      let b2' : bytes32 = Seq.slice b2 len2 (Seq.length b2) in
      aux b1' b2';
      let (Some (_, len1')) = parse (parse_list_bare p) b1' in
      let (Some (_, len2')) = parse (parse_list_bare p) b2' in
      Seq.lemma_split (Seq.slice b1 0 (len1 + len1')) len1;
      Seq.lemma_split (Seq.slice b2 0 (len2 + len2')) len2;
      assert (injective_postcond (parse_list_bare p) b1 b2)
    end
  in
  Classical.forall_intro_2 (fun b -> Classical.move_requires (aux b))

noextract
val parse_list
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Tot (weak_parser (list t))

let parse_list #b #t p =
  Classical.forall_intro_2 (no_lookahead_weak_on_parse_list_bare p);
  parse_list_bare_injective p;
  parse_list_bare p

noextract
let parse_list_consumed
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: bytes32)
: Lemma
  (requires (Some? (parse (parse_list p) b)))
  (ensures (
    let pb = parse (parse_list p) b in (
    Some? pb /\ (
    let (Some (_, consumed)) = pb in
    consumed == Seq.length b
  ))))
  (decreases (Seq.length b))
= parse_list_bare_consumed p b

let parse_list_consumes_all
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
: Lemma
  (consumes_all (parse_list p))
  [SMTPat (consumes_all (parse_list p))]
= Classical.forall_intro (Classical.move_requires (parse_list_consumed p))

let parse_list_exactly_parses
  (h: HS.mem)
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (s: S.bslice)
  (pred: ((list t * consumed_slice_length s) -> GTot Type0))
: Lemma
  (requires (parses h (parse_list p) s pred))
  (ensures (exactly_parses h (parse_list p) s (fun v -> pred (v, S.length s))))
= parse_list_consumed p (S.as_seq h s)

noextract
let rec parse_list_tailrec
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: bytes32)
: Tot ((aux: list t) -> GTot (option (list t)))
  (decreases (Seq.length b))
= fun aux ->
  if Seq.length b = 0
  then 
    Some aux
  else
    match p b with
    | None -> None
    | Some (v, n) ->
      if n = 0
      then None (* elements cannot be empty *)
      else
	parse_list_tailrec p (Seq.slice b n (Seq.length b)) (L.append aux [v])

noextract
let rec parse_list_tailrec_append
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: bytes32)
  (auxl: list t)
  (auxr: list t)
: Lemma
  (requires True)
  (ensures (
    parse_list_tailrec p b (L.append auxl auxr) == (
    match parse_list_tailrec p b auxr with
    | None -> None
    | Some l -> Some (L.append auxl l)
  )))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then ()
  else
    match p b with
    | None -> ()
    | Some (v, n) ->
      if n = 0
      then ()
      else begin
	parse_list_tailrec_append p (Seq.slice b n (Seq.length b)) auxl (L.append auxr [v]);
	L.append_assoc auxl auxr [v]
      end

noextract
let rec parse_list_tailrec_correct
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: bytes32)
  (aux: list t)
: Lemma
  (requires True)
  (ensures (
    parse_list_tailrec p b aux == (
    match parse (parse_list p) b with
    | Some (l, n) -> Some (L.append aux l)
    | None -> None
  )))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then
    L.append_l_nil aux
  else
    match p b with
    | None -> ()
    | Some (v, n) ->
      if n = 0
      then ()
      else begin
	let s = Seq.slice b n (Seq.length b) in
	parse_list_tailrec_correct p s (L.append aux [v]);
	match parse (parse_list p) s with
	| Some (l, n') ->
	  L.append_assoc aux [v] l
	| None -> ()
      end
