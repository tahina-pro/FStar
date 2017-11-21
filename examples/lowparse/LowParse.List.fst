module LowParse.List
include LowParse.Base

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

#set-options "--z3rlimit 32"

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

(* No stateful parser for lists, because we do not know how to extract the resulting list -- or even the list while it is being constructed *)

inline_for_extraction
val list_head_tail
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    parses h (parse_list p) b (fun (l, _) ->
    Cons? l
  )))
  (ensures (fun h r h' ->
    S.modifies_none h h' /\ (
    let (bh, bt) = r in
    S.is_concat_gen b [bh; bt] /\
    parses h (parse_list p) b (fun (l, _) ->
    exactly_parses h p bh (fun a ->
    parses h' (parse_list p) bt (fun (q, _) ->
    l == a :: q
  ))))))

let list_head_tail #b #t #p sv b =
  split sv b

inline_for_extraction
val list_is_empty
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: S.bslice)
: HST.Stack bool
  (requires (fun h ->
    parses h (parse_list p) b (fun _ -> True)
  ))
  (ensures (fun h b' h' ->
    S.modifies_none h h' /\
    parses h (parse_list p) b (fun (l, _) ->
    b' == Nil? l
  )))

let list_is_empty #b #t p b =
  S.length b = 0ul

let list_nth_slice_precond
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
  (h: HS.mem)
: GTot Type0
= parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l
  )

let list_nth_slice_inv
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
  (h0: Ghost.erased HS.mem)
  (sl: B.buffer S.bslice)
  (h: HS.mem)
  (j: nat)
: GTot Type0
= B.disjoint (S.as_buffer b) sl /\
  B.length sl == 1 /\
  list_nth_slice_precond p sv b i (Ghost.reveal h0) /\
  B.modifies_1 sl (Ghost.reveal h0) h /\
  j <= U32.v i /\
  B.live h sl /\ (
  let b' = Seq.index (B.as_seq h sl) 0 in (
  S.includes b b' /\ (
  parses (Ghost.reveal h0) (parse_list p) b (fun (l, _) ->
  parses (Ghost.reveal h0) (parse_list p) b' (fun (lr, _) ->
  U32.v i < L.length l /\
  L.length lr == L.length l - j /\
  L.index l (U32.v i) == L.index lr (U32.v i - j)
  )))))

inline_for_extraction
val list_nth_slice_advance
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
  (h0: Ghost.erased HS.mem)
  (sl: B.buffer S.bslice)
  (j: U32.t)
: HST.Stack unit
  (requires (fun h ->
    list_nth_slice_inv p sv b i h0 sl h (U32.v j) /\
    U32.v j < U32.v i
  ))
  (ensures (fun h1 _ h2 ->
    list_nth_slice_inv p sv b i h0 sl h1 (U32.v j) /\
    U32.v j < U32.v i /\
    list_nth_slice_inv p sv b i h0 sl h2 (U32.v j + 1)
  ))

let list_nth_slice_advance #b #t p sv b i h0 sl j =
  let h1 = HST.get () in
  B.no_upd_lemma_1 (Ghost.reveal h0) h1 sl (S.as_buffer b);
  let s = B.index sl 0ul in
  assert (S.as_seq h1 s == S.as_seq (Ghost.reveal h0) s);
  let h2 = HST.get () in
  assert (B.modifies_1 sl h1 h2);
  assert (S.as_seq h2 s == S.as_seq (Ghost.reveal h0) s);
  let (_, s') = list_head_tail sv s in
  let h3 = HST.get () in
  assert (B.modifies_none h2 h3);
  assert (S.as_seq h3 s == S.as_seq (Ghost.reveal h0) s);
  assert (S.as_seq h3 s' == S.as_seq (Ghost.reveal h0) s');
  B.lemma_intro_modifies_1 sl h2 h3;
  B.upd sl 0ul s';
  let h = HST.get () in
  assert (B.modifies_1 sl (Ghost.reveal h0) h);
  S.includes_trans b s s';
  ()

inline_for_extraction
val list_nth_slice
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
: HST.Stack S.bslice
  (requires (fun h ->
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l
  )))
  (ensures (fun h b' h' ->
    S.modifies_none h h' /\
    S.includes b b' /\
    parses h (parse_list p) b (fun (l, _) ->
    exactly_parses h p b' (fun v ->
    U32.v i < L.length l /\
    v == L.index l (U32.v i)
  ))))

let list_nth_slice #b #t p sv b i =
  let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let sl : B.buffer S.bslice = B.create b 1ul in
  let h2 = HST.get () in
  B.lemma_reveal_modifies_0 h1 h2; // I really need to switch to my new modifies clauses very soon!
  assert (S.as_seq h2 b == S.as_seq h0 b);
  assert (list_nth_slice_inv p sv b i (Ghost.hide h2) sl h2 0);
  C.Loops.for
    0ul
    i
    (fun h j -> list_nth_slice_inv p sv b i (Ghost.hide h2) sl h j)
    (fun j -> list_nth_slice_advance p sv b i (Ghost.hide h2) sl j)
  ;
  let h3 = HST.get () in
  B.lemma_reveal_modifies_1 sl h2 h3;
  let tail = B.index sl 0ul in
  let (res, _) = list_head_tail sv tail in
  let h4 = HST.get () in
  assert (S.as_seq h4 b == S.as_seq h0 b);
  assert (S.as_seq h4 res == S.as_seq h0 res);
  HST.pop_frame ();
  let h = HST.get () in
  assert (S.as_seq h b == S.as_seq h0 b);
  assert (S.as_seq h res == S.as_seq h0 res);
  res

let validate_list_inv
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (sv: stateful_validator p)
  (b: S.bslice)
  (h0: Ghost.erased HS.mem)
  (sl: B.buffer (option S.bslice))
  (h: HS.mem)
  (j: nat)
  (interrupt: bool)
: GTot Type0
= B.disjoint (S. as_buffer b) sl /\
  B.length sl == 1 /\
  S.live (Ghost.reveal h0) b /\
  B.modifies_1 sl (Ghost.reveal h0) h /\
  B.live h sl /\ (
  let sq = S.as_seq (Ghost.reveal h0) b in
  let slo = Seq.index (B.as_seq h sl) 0 in
  if interrupt
  then
    (Some? slo ==> Some? (parse (parse_list p) sq))
  else (
    Some? slo /\ (
    let (Some sl) = slo in (
    S.includes b sl /\
    S.live (Ghost.reveal h0) sl /\
    j <= U32.v (S.length b) /\
    U32.v (S.length sl) <= U32.v (S.length b) - j /\ (
    let sq' = S.as_seq (Ghost.reveal h0) sl in
    (Some? (parse (parse_list p) sq') ==> Some? (parse (parse_list p) sq))
  )))))

inline_for_extraction
val validate_list_advance
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (sv: stateful_validator p)
  (b: S.bslice)
  (h0: Ghost.erased HS.mem)
  (sl: B.buffer (option S.bslice))
  (j: U32.t)
: HST.Stack bool
  (requires (fun h ->
    U32.v j < U32.v (S.length b) /\
    validate_list_inv sv b h0 sl h (U32.v j) false
  ))
  (ensures (fun h1 res h2 ->
    U32.v j < U32.v (S.length b) /\
    validate_list_inv sv b h0 sl h1 (U32.v j) false /\
    validate_list_inv sv b h0 sl h2 (U32.v j + 1) res
  ))

let validate_list_advance #b #t #p sv b h0 sl j =
  let h1 = HST.get () in
  B.no_upd_lemma_1 (Ghost.reveal h0) h1 sl (S.as_buffer b);
  let os = B.index sl 0ul in
  let (Some s) = os in
  assert (S.as_seq h1 s == S.as_seq (Ghost.reveal h0) s);
  if S.length s = 0ul
  then true
  else begin
    let svs = sv s in
    let h2 = HST.get () in
    assert (S.as_seq h2 s == S.as_seq (Ghost.reveal h0) s);
    B.lemma_intro_modifies_1 sl h1 h2;
    match svs with
    | None ->
      B.upd sl 0ul None;
      true
    | Some off ->
      if off = 0ul
      then begin
	B.upd sl 0ul None;
	true
      end else begin
	let s' = S.advance_slice s off in
	assert (S.as_seq h2 s' == S.as_seq (Ghost.reveal h0) s');
	B.upd sl 0ul (Some s');
	false
      end
  end  

inline_for_extraction
val validate_list
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (sv: stateful_validator p)
: Tot (stateful_validator (parse_list p))

let validate_list #b #t #p sv =
  fun (b: S.bslice) ->
  let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let sl : B.buffer (option S.bslice) = B.create (Some b) 1ul in
  let h2 = HST.get () in
  B.lemma_reveal_modifies_0 h1 h2; // I really need to switch to my new modifies clauses very soon!
  assert (S.as_seq h2 b == S.as_seq h0 b);
  assert (validate_list_inv sv b (Ghost.hide h2) sl h2 0 false);
  let slen = S.length b in
  let (_, interrupt) = C.Loops.interruptible_for
    0ul
    slen
    (fun h j inter -> validate_list_inv sv b (Ghost.hide h2) sl h j inter)
    (fun j -> validate_list_advance sv b (Ghost.hide h2) sl j)
  in
  let h3 = HST.get () in
  B.lemma_reveal_modifies_1 sl h2 h3;
  assert (S.as_seq h3 b == S.as_seq h0 b);
  let tail = B.index sl 0ul in
  let res : option (n: consumed_slice_length b) =
    if interrupt
    then match tail with
    | None -> None
    | Some _ -> Some (S.length b)
    else None
  in
  HST.pop_frame ();
  let h = HST.get () in
  assert (S.as_seq h b == S.as_seq h0 b);
  assert (S.live h0 b);
  let pre : Type0 =
    Some? res
  in
  let post : Type0 =
    pre /\
    S.live h0 b /\ (
    let s = S.as_seq h0 b in
    let pl = parse (parse_list p) s in (
    Some? pl /\ (
    let (Some (_, consumed)) = pl in
    let (Some consumed') = res in
    consumed == U32.v consumed'
  )))
  in
  let f () : Lemma
    (requires pre)
    (ensures post)
  = let s = S.as_seq h0 b in
    parse_list_consumed p s
  in
  Classical.move_requires f ();
  res
