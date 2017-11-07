module MITLSLow.List
include MITLSLow
include MITLSLow.Continued

module S = Slice
module P = GhostParsing
module IP = IntegerParsing
module B = FStar.Buffer

(* Parse a list, until there is nothing left to read. This parser will mostly fail EXCEPT if the whole size is known and the slice has been suitably truncated beforehand, or if the elements of the list all have a known constant size. *)

val parse_list_aux
  (#t: Type0)
  (p: P.parser t)
  (b: P.bytes32)
: Tot (P.parse_arrow unit (fun _ -> option (list t * (n: nat { n <= Seq.length b } ))))
  (decreases (Seq.length b))

let rec parse_list_aux #t p b =
  let () = () in
  fun () ->
  if Seq.length b = 0
  then 
    Some ([], 0)
  else
    match p b with
    | None -> None
    | Some (v, n) ->
      if n = 0
      then None (* elements cannot be empty *)
      else
        match parse_list_aux p (Seq.slice b n (Seq.length b)) () with
	| Some (l, n') -> Some (v :: l, n + n')
	| _ -> None

val parse_list
  (#t: Type0)
  (p: P.parser t)
: Tot (P.parser (list t))

let parse_list #t p b = parse_list_aux #t p b ()

let rec parse_list_consumed
  (#t: Type0)
  (p: P.parser t)
  (b: P.bytes32)
: Lemma
  (requires (Some? (parse_list p b)))
  (ensures (
    let pb = parse_list p b in (
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
    parse_list_consumed p b'

let rec parse_list_tailrec
  (#t: Type0)
  (p: P.parser t)
  (b: P.bytes32)
: Tot (P.parse_arrow (aux: list t) (fun _ -> option (list t)))
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
	parse_list_tailrec p (Seq.slice b n (Seq.length b)) (List.Tot.append aux [v])

let rec parse_list_tailrec_append
  (#t: Type0)
  (p: P.parser t)
  (b: P.bytes32)
  (auxl: list t)
  (auxr: list t)
: Lemma
  (requires True)
  (ensures (
    parse_list_tailrec p b (List.Tot.append auxl auxr) == (
    match parse_list_tailrec p b auxr with
    | None -> None
    | Some l -> Some (List.Tot.append auxl l)
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
	parse_list_tailrec_append p (Seq.slice b n (Seq.length b)) auxl (List.Tot.append auxr [v]);
	List.Tot.append_assoc auxl auxr [v]
      end

let rec parse_list_tailrec_correct
  (#t: Type0)
  (p: P.parser t)
  (b: P.bytes32)
  (aux: list t)
: Lemma
  (requires True)
  (ensures (
    parse_list_tailrec p b aux == (
    match parse_list p b with
    | Some (l, n) -> Some (List.Tot.append aux l)
    | None -> None
  )))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then
    List.Tot.append_l_nil aux
  else
    match p b with
    | None -> ()
    | Some (v, n) ->
      if n = 0
      then ()
      else begin
	let s = Seq.slice b n (Seq.length b) in
	parse_list_tailrec_correct p s (List.Tot.append aux [v]);
	match parse_list p s with
	| Some (l, n') ->
	  List.Tot.append_assoc aux [v] l
	| None -> ()
      end

(* No stateful parser for lists, because we do not know how to extract the resulting list -- or even the list while it is being constructed *)

let advance_slice_advance_slice
  (b: S.bslice)
  (off1: UInt32.t {UInt32.v off1 <= UInt32.v b.S.len } )
  (off2: UInt32.t {UInt32.v off2 <= UInt32.v (S.advance_slice b off1).S.len } )
: Lemma
  (requires (
    S.u32_add_overflows off1 off2 == false
  ))
  (ensures (
    S.u32_add_overflows off1 off2 == false /\
    S.advance_slice (S.advance_slice b off1) off2 == S.advance_slice b (UInt32.add off1 off2)
  ))
= let s1 = S.advance_slice b off1 in
  let s2 = S.advance_slice s1 off2 in
  B.sub_sub (S.BSlice?.p b) off1 (S.BSlice?.len s1) off2 (S.BSlice?.len s2)

(* TODO: move to FStar.List.Tot.Properties *)

let rec list_append_index_r
  (#t: Type0)
  (l1: list t)
  (l2: list t)
  (i: nat)
: Lemma
  (requires (
    i >= List.Tot.length l1 /\
    i < List.Tot.length l1 + List.Tot.length l2
  ))
  (ensures (
    i >= List.Tot.length l1 /\
    i < List.Tot.length l1 + List.Tot.length l2 /\
    i < List.Tot.length (List.Tot.append l1 l2) /\
    List.Tot.index (List.Tot.append l1 l2) i ==
    List.Tot.index l2 (i - List.Tot.length l1)
  ))
  (decreases l1)
= List.Tot.append_length l1 l2; // TODO: replace/augment the patterns on @ with patterns on List.Tot.append
  match l1 with
  | [] -> ()
  | _ :: l1' ->
    list_append_index_r l1' l2 (i - 1)

module HS = FStar.HyperStack

(* TODO: move to FStar.Buffer or FStar.HyperStack? *)
   
let modifies_tip_popped h0 h1 h2 h3 : Lemma
  (requires (HS.fresh_frame h0 h1 /\ HS.popped h2 h3 /\ HS.modifies_one h1.HS.tip h1 h2 /\ h1.HS.tip == h2.HS.tip))
  (ensures  (B.modifies_none h0 h3))
  = ()

(* TODO: move to C.Loops *)
(* To be extracted as:
    for (int i = <start>; i != <finish>; ++i)
      <f> i;
*)
(*
val for_with_ghost_state:
  (#gt: Type0) ->
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish >= UInt32.v start} ->
  gt_start: Ghost.erased gt ->
  inv:(HS.mem -> nat -> gt -> GTot Type0) ->
  f:(
    i:UInt32.t{FStar.UInt32.(v start <= v i /\ v i < v finish)} ->
    g : Ghost.erased gt ->
    HST.Stack (Ghost.erased gt)
    (requires (fun h -> inv h (UInt32.v i) (Ghost.reveal g)))
    (ensures (fun h_1 g' h_2 -> FStar.UInt32.(inv h_1 (v i) (Ghost.reveal g) /\ inv h_2 (v i + 1) (Ghost.reveal g'))))
  ) ->
  HST.Stack (Ghost.erased gt)
    (requires (fun h -> inv h (UInt32.v start) (Ghost.reveal gt_start)))
    (ensures (fun _ g' h_2 -> inv h_2 (UInt32.v finish) (Ghost.reveal g')))
let rec for_with_ghost_state #gt start finish gt_start inv f =
  if start = finish then
    gt_start
  else begin
    let g' = f start gt_start in
    for_with_ghost_state (FStar.UInt32.(start +^ 1ul)) finish g' inv f
  end
*)

module HST = FStar.HyperStack.ST

val list_head
  (#t: Type0)
  (p: P.parser t)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    S.live h b /\ (
    let sq = S.as_seq h b in
    let pl = parse_list p sq in (
    Some? pl /\ (
    let (Some (l, _)) = pl in (
    Cons? l
  ))))))
  (ensures (fun h b' h' ->
    B.modifies_none h h' /\
    S.live h b /\
    S.live h b' /\
    B.includes b.S.p b'.S.p /\ (
    let sq = S.as_seq h b in
    let pl = parse_list p sq in (
    Some? pl /\ (
    let (Some (l, _)) = pl in (
    Cons? l /\ (
    let sq' = S.as_seq h b' in
    let pb' = p sq' in (
    Some? pb' /\ (
    let (Some (v, _)) = pb' in (
    v == List.Tot.hd l
  ))))))))))

let list_head #t p b = b

val list_tail
  (#t: Type0)
  (#p: P.parser t)
  (sv: P.stateful_validator_nochk p)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    S.live h b /\ (
    let sq = S.as_seq h b in
    let pl = parse_list p sq in (
    Some? pl /\ (
    let (Some (l, _)) = pl in (
    Cons? l
  ))))))
  (ensures (fun h b' h' ->
    B.modifies_none h h' /\
    S.live h b /\
    S.live h b' /\
    B.includes b.S.p b'.S.p /\ (
    let sq = S.as_seq h b in
    let pl = parse_list p sq in (
    Some? pl /\ (
    let (Some (l, _)) = pl in (
    Cons? l /\ (
    let sq' = S.as_seq h b' in
    let pb' = parse_list p sq' in (
    Some? pb' /\ (
    let (Some (v, _)) = pb' in (
    v == List.Tot.tl l
  ))))))))))

let list_tail #t #p sv b =
  let off = sv b in
  let b' = S.advance_slice b off in
  b'

val list_is_empty
  (#t: Type0)
  (p: P.parser t)
  (b: S.bslice)
: HST.Stack bool
  (requires (fun h ->
    S.live h b /\ (
    let sq = S.as_seq h b in
    let pl = parse_list p sq in
    Some? pl
  )))
  (ensures (fun h b' h' ->
    B.modifies_none h h' /\
    S.live h b /\ (
    let sq = S.as_seq h b in
    let pl = parse_list p sq in (
    Some? pl /\ (
    let (Some (l, _)) = pl in (
    b' == Nil? l
  ))))))

let list_is_empty #t p b =
  b.S.len = 0ul

let index_tail
  (#a: Type0)
  (l: list a)
  (i: nat)
: Lemma
  (requires (
    i < List.Tot.length l /\
    0 < i
  ))
  (ensures (
    i < List.Tot.length l /\
    0 < i /\
    List.Tot.index l i == List.Tot.index (List.Tot.tl l) (i - 1)
  ))
= ()

let list_nth_slice_precond
  (#t: Type0)
  (p: P.parser t)
  (sv: P.stateful_validator_nochk p)
  (b: S.bslice)
  (i: UInt32.t)
  (h: HS.mem)
: GTot Type0
=   S.live h b /\ (
    let sq = S.as_seq h b in
    let pl = parse_list p sq in (
    Some? pl /\ (
    let (Some (l, _)) = pl in
    UInt32.v i < List.Tot.length l
  )))

let list_nth_slice_inv
  (#t: Type0)
  (p: P.parser t)
  (sv: P.stateful_validator_nochk p)
  (b: S.bslice)
  (i: UInt32.t)
  (h0: Ghost.erased HS.mem)
  (sl: B.buffer S.bslice)
  (h: HS.mem)
  (j: nat)
: GTot Type0
= B.disjoint b.S.p sl /\
  B.length sl == 1 /\
  list_nth_slice_precond p sv b i (Ghost.reveal h0) /\
  B.modifies_1 sl (Ghost.reveal h0) h /\
  j <= UInt32.v i /\
  B.live h sl /\ (
  let b' = Seq.index (B.as_seq h sl) 0 in (
  S.live (Ghost.reveal h0) b' /\
  B.includes b.S.p b'.S.p /\ (
  let sq = S.as_seq (Ghost.reveal h0) b in
  let pl = parse_list p sq in (
  let (Some (l, _)) = pl in (
  let sq' = S.as_seq (Ghost.reveal h0) b' in
  let pb' = parse_list p sq' in (
  Some? pb' /\ (
  let (Some (lr, _)) = pb' in (
  List.Tot.length lr == List.Tot.length l - j /\
  List.Tot.index l (UInt32.v i) == List.Tot.index lr (UInt32.v i - j)
  ))))))))

val list_nth_slice_advance
  (#t: Type0)
  (p: P.parser t)
  (sv: P.stateful_validator_nochk p)
  (b: S.bslice)
  (i: UInt32.t)
  (h0: Ghost.erased HS.mem)
  (sl: B.buffer S.bslice)
  (j: UInt32.t)
: HST.Stack unit
  (requires (fun h ->
    list_nth_slice_inv p sv b i h0 sl h (UInt32.v j) /\
    UInt32.v j < UInt32.v i
  ))
  (ensures (fun h1 _ h2 ->
    list_nth_slice_inv p sv b i h0 sl h1 (UInt32.v j) /\
    UInt32.v j < UInt32.v i /\
    list_nth_slice_inv p sv b i h0 sl h2 (UInt32.v j + 1)
  ))

let list_nth_slice_advance #t p sv b i h0 sl j =
  let h1 = HST.get () in
  B.no_upd_lemma_1 (Ghost.reveal h0) h1 sl b.S.p;
  let s = B.index sl 0ul in
  assert (S.as_seq h1 s == S.as_seq (Ghost.reveal h0) s);
  let h2 = HST.get () in
  assert (B.modifies_1 sl h1 h2);
  assert (S.as_seq h2 s == S.as_seq (Ghost.reveal h0) s);
  let s' = list_tail sv s in
  let h3 = HST.get () in
  assert (B.modifies_none h2 h3);
  assert (S.as_seq h3 s == S.as_seq (Ghost.reveal h0) s);
  assert (S.as_seq h3 s' == S.as_seq (Ghost.reveal h0) s');
  B.lemma_intro_modifies_1 sl h2 h3;
  B.upd sl 0ul s';
  let h = HST.get () in
  assert (B.modifies_1 sl (Ghost.reveal h0) h);
  B.includes_trans b.S.p s.S.p s'.S.p;
  ()

val list_nth_slice
  (#t: Type0)
  (p: P.parser t)
  (sv: P.stateful_validator_nochk p)
  (b: S.bslice)
  (i: UInt32.t)
: HST.Stack S.bslice
  (requires (fun h ->
    S.live h b /\ (
    let sq = S.as_seq h b in
    let pl = parse_list p sq in (
    Some? pl /\ (
    let (Some (l, _)) = pl in (
    UInt32.v i < List.Tot.length l
  ))))))
  (ensures (fun h b' h' ->
    B.modifies_none h h' /\
    S.live h b /\
    S.live h b' /\
    B.includes b.S.p b'.S.p /\ (
    let sq = S.as_seq h b in
    let pl = parse_list p sq in (
    Some? pl /\ (
    let (Some (l, _)) = pl in (
    UInt32.v i < List.Tot.length l /\ (
    let sq' = S.as_seq h b' in
    let pb' = p sq' in (
    Some? pb' /\ (
    let (Some (v, _)) = pb' in (
    v == List.Tot.index l (UInt32.v i)
  ))))))))))

let list_nth_slice #t p sv b i =
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
  let res = list_head p tail in
  let h4 = HST.get () in
  assert (S.as_seq h4 b == S.as_seq h0 b);
  assert (S.as_seq h4 res == S.as_seq h0 res);
  HST.pop_frame ();
  let h = HST.get () in
  assert (S.as_seq h b == S.as_seq h0 b);
  assert (S.as_seq h res == S.as_seq h0 res);
  res

let validate_list_inv
  (#t: Type0)
  (#p: P.parser t)
  (sv: P.stateful_validator p)
  (b: S.bslice)
  (h0: Ghost.erased HS.mem)
  (sl: B.buffer (option S.bslice))
  (h: HS.mem)
  (j: nat)
  (interrupt: bool)
: GTot Type0
= B.disjoint b.S.p sl /\
  B.length sl == 1 /\
  S.live (Ghost.reveal h0) b /\
  B.modifies_1 sl (Ghost.reveal h0) h /\
  B.live h sl /\ (
  let sq = S.as_seq (Ghost.reveal h0) b in
  let slo = Seq.index (B.as_seq h sl) 0 in
  if interrupt
  then
    (Some? slo ==> Some? (parse_list p sq))
  else (
    Some? slo /\ (
    let (Some sl) = slo in (
    B.includes b.S.p sl.S.p /\
    S.live (Ghost.reveal h0) sl /\
    j <= UInt32.v b.S.len /\
    UInt32.v sl.S.len <= UInt32.v b.S.len - j /\ (
    let sq' = S.as_seq (Ghost.reveal h0) sl in
    (Some? (parse_list p sq') ==> Some? (parse_list p sq))
  )))))

#set-options "--z3rlimit 16"

val validate_list_advance
  (#t: Type0)
  (#p: P.parser t)
  (sv: P.stateful_validator p)
  (b: S.bslice)
  (h0: Ghost.erased HS.mem)
  (sl: B.buffer (option S.bslice))
  (j: UInt32.t)
: HST.Stack bool
  (requires (fun h ->
    UInt32.v j < UInt32.v b.S.len /\
    validate_list_inv sv b h0 sl h (UInt32.v j) false
  ))
  (ensures (fun h1 res h2 ->
    UInt32.v j < UInt32.v b.S.len /\
    validate_list_inv sv b h0 sl h1 (UInt32.v j) false /\
    validate_list_inv sv b h0 sl h2 (UInt32.v j + 1) res
  ))

let validate_list_advance #t #p sv b h0 sl j =
  let h1 = HST.get () in
  B.no_upd_lemma_1 (Ghost.reveal h0) h1 sl b.S.p;
  let os = B.index sl 0ul in
  let (Some s) = os in
  assert (S.as_seq h1 s == S.as_seq (Ghost.reveal h0) s);
  if s.S.len = 0ul
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

val validate_list
  (#t: Type0)
  (#p: P.parser t)
  (sv: P.stateful_validator p)
: Tot (P.stateful_validator (parse_list p))

let validate_list #t #p sv b =
  let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let sl : B.buffer (option S.bslice) = B.create (Some b) 1ul in
  let h2 = HST.get () in
  B.lemma_reveal_modifies_0 h1 h2; // I really need to switch to my new modifies clauses very soon!
  assert (S.as_seq h2 b == S.as_seq h0 b);
  assert (validate_list_inv sv b (Ghost.hide h2) sl h2 0 false);
  let (_, interrupt) = C.Loops.interruptible_for
    0ul
    b.S.len
    (fun h j inter -> validate_list_inv sv b (Ghost.hide h2) sl h j inter)
    (fun j -> validate_list_advance sv b (Ghost.hide h2) sl j)
  in
  let h3 = HST.get () in
  B.lemma_reveal_modifies_1 sl h2 h3;
  assert (S.as_seq h3 b == S.as_seq h0 b);
  let tail = B.index sl 0ul in
  let res : option (n: UInt32.t { UInt32.v n <= UInt32.v b.S.len } ) =
    if interrupt
    then match tail with
    | None -> None
    | Some _ -> Some b.S.len
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
    let pl = parse_list p s in (
    Some? pl /\ (
    let (Some (_, consumed)) = pl in
    let (Some consumed') = res in
    consumed == UInt32.v consumed'
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
