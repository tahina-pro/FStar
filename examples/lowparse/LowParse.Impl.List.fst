module LowParse.Impl.List
include LowParse.Impl.Combinators
include LowParse.Spec.List

module Seq = FStar.Seq
module L = FStar.List.Tot
module S = LowParse.Slice
module B = FStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module Classical = FStar.Classical

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

#set-options "--z3rlimit 32"

let list_head_tail #b #t #p sv b =
  split sv b

#reset-options

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

#set-options "--z3rlimit 64"

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

#reset-options

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

#set-options "--z3rlimit 32"

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

#reset-options

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

#set-options "--z3rlimit 32"

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

#reset-options
