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

let list_length_inv
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (h0: Ghost.erased HS.mem)
  (sl: B.buffer S.bslice)
  (h: HS.mem)
  (j: nat)
  (interrupt: bool)
: GTot Type0
= B.modifies_1 sl (Ghost.reveal h0) h /\
  B.disjoint sl (S.as_buffer b) /\
  B.length sl == 1 /\
  B.live h sl /\ (
  let s = Seq.index (B.as_seq h sl) 0 in
  S.includes b s /\
  j + U32.v (S.length s) <= U32.v (S.length b) /\
  parses (Ghost.reveal h0) (parse_list p) b (fun (l, _) ->
  parses (Ghost.reveal h0) (parse_list p) s (fun (l', _) ->
    if interrupt
    then
      (L.length l + 1 == j)
    else
      L.length l == j + L.length l'
  )))

inline_for_extraction
val list_length_advance
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (h0: Ghost.erased HS.mem)
  (sl: B.buffer S.bslice)
  (j: U32.t)
: HST.Stack bool
  (requires (fun h ->
    U32.v j < U32.v (S.length b) /\
    list_length_inv p sv b h0 sl h (U32.v j) false
  ))
  (ensures (fun h interrupt h' ->
    U32.v j < U32.v (S.length b) /\
    list_length_inv p sv b h0 sl h (U32.v j) false /\
    list_length_inv p sv b h0 sl h' (U32.v j + 1) interrupt
  ))

#set-options "--z3rlimit 64"

let list_length_advance #b #t p sv b h0 sl j =
  let s = B.index sl 0ul in
  if S.length s = 0ul
  then true
  else begin
    let h = HST.get () in
    let len = sv s in
    let s' = S.advance_slice s len in
    let h2 = HST.get () in
    assert (B.modifies_none h h2);
    B.lemma_intro_modifies_1 sl h h2;
    B.upd sl 0ul s' ;
    false
  end

#reset-options

val list_length
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
: HST.Stack U32.t
  (requires (fun h ->
    parses h (parse_list p) b (fun _ -> True)
  ))
  (ensures (fun h i h' ->
    S.modifies_none h h' /\
    parses h (parse_list p) b (fun (l, _) ->
    L.length l == U32.v i
  )))

#set-options "--z3rlimit 32"

let list_length #b #t #p sv b =
  let h0 = HST.get () in
  HST.push_frame () ;
  let h1 = HST.get () in
  let sl : B.buffer S.bslice = B.create b 1ul in
  let h2 = HST.get () in
  let len = S.length b in
  let (j, interrupt) = C.Loops.interruptible_for
    0ul
    len
    (fun h j -> list_length_inv p sv b (Ghost.hide h2) sl h j)
    (fun j -> list_length_advance p sv b (Ghost.hide h2) sl j)
  in
  let res =
    if interrupt
    then U32.sub j 1ul
    else j
  in
  let h3 = HST.get () in
  HST.pop_frame () ;
  let h4 = HST.get () in
  B.lemma_modifies_0_push_pop h0 h1 h3 h4;
  res

#reset-options

val list_length_constant_size_parser_correct
  (#n: nat)
  (#b: bool)
  (#t: Type0)
  (p: constant_size_parser b n t)
  (b: S.bslice)
  (h: HS.mem)
: Lemma
  (requires (
    parses h (parse_list p) b (fun _ -> True)
  ))
  (ensures (
    parses h (parse_list p) b (fun (l, _) ->
    FStar.Mul.op_Star (L.length l) n == U32.v (S.length b)
  )))
  (decreases (U32.v (S.length b)))

#set-options "--z3rlimit 16"

let rec list_length_constant_size_parser_correct #n #b #t p b h =
  if S.length b = 0ul
  then ()
  else
    let b' = S.advanced_slice b (U32.uint_to_t n) in
    list_length_constant_size_parser_correct p b' h

#reset-options

inline_for_extraction
val list_length_constant_size_parser
  (#n: U32.t)
  (#b: bool)
  (#t: Type0)
  (p: constant_size_parser b (U32.v n) t)
  (b: S.bslice)
: HST.Stack U32.t
  (requires (fun h ->
    U32.v n <> 0 /\
    parses h (parse_list p) b (fun _ -> True)
  ))
  (ensures (fun h i h' ->
    S.modifies_none h h' /\
    parses h (parse_list p) b (fun (l, _) ->
    L.length l == U32.v i
  )))

#set-options "--z3rlimit 16"

let list_length_constant_size_parser #n #b #t p b =
  let h = HST.get () in
  list_length_constant_size_parser_correct p b h;
  let len = S.length b in
  U32.div len n

#reset-options

val list_nth_spec
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: S.bslice)
  (i: U32.t)
  (h: HS.mem)
: Ghost S.bslice
  (requires (
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l
  )))
  (ensures (fun b' ->
    S.includes b b' /\
    parses h (parse_list p) b (fun (l, _) ->
    exactly_parses h p b' (fun (x) ->
    U32.v i < L.length l /\
    x == L.index l (U32.v i)
  ))))
  (decreases (U32.v i))

#set-options "--z3rlimit 16"

let rec list_nth_spec #b #t p b i h =
  let s = S.as_seq h b in
  let (Some (v, len)) = parse p s in
  if i = 0ul
  then begin
    let b' = S.truncated_slice b (U32.uint_to_t len) in
    let s' = S.as_seq h b' in
    assert (no_lookahead_weak_on _ p s s');
    b'
  end else
    let b' = S.advanced_slice b (U32.uint_to_t len) in
    list_nth_spec p b' (U32.sub i 1ul) h

#reset-options

val list_nth_spec_ext
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: S.bslice)
  (i: U32.t)
  (h h': HS.mem)
: Lemma
  (requires (
    parses h (parse_list p) b (fun (l, _) -> U32.v i < L.length l) /\
    S.live h' b /\
    S.as_seq h' b == S.as_seq h b
  ))
  (ensures (
    parses h (parse_list p) b (fun (l, _) -> U32.v i < L.length l) /\
    parses h' (parse_list p) b (fun (l, _) -> U32.v i < L.length l) /\
    list_nth_spec p b i h' == list_nth_spec p b i h
  ))
  (decreases (U32.v i))

let rec list_nth_spec_ext #b #t p b i h h' =
  if i = 0ul
  then ()
  else
    let s = S.as_seq h b in
    let (Some (v, len)) = parse p s in
    let b' = S.advanced_slice b (U32.uint_to_t len) in
    list_nth_spec_ext p b' (U32.sub i 1ul) h h'

val list_nth_spec_lt_disjoint
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: S.bslice)
  (i j: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    U32.v i < U32.v j /\
    parses h (parse_list p) b (fun (l, _) ->
    U32.v j < L.length l
  )))
  (ensures (
    U32.v i < U32.v j /\
    parses h (parse_list p) b (fun (l, _) ->
    U32.v j < L.length l /\
    S.disjoint (list_nth_spec p b i h) (list_nth_spec p b j h)
  )))
  (decreases (U32.v i))

let rec list_nth_spec_lt_disjoint #b #t p b i j h =
  let s = S.as_seq h b in
  let (Some (v, len)) = parse p s in
  let b' = S.advanced_slice b (U32.uint_to_t len) in
  if i = 0ul
  then begin
    assert (list_nth_spec p b j h == list_nth_spec p b' (U32.sub j 1ul) h);
    assert (S.includes b' (list_nth_spec p b j h));
    assert (S.disjoint (list_nth_spec p b i h) b')
  end else
    list_nth_spec_lt_disjoint p b' (U32.sub i 1ul) (U32.sub j 1ul) h

val list_nth_spec_disjoint
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (b: S.bslice)
  (i j: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    U32.v i <> U32.v j /\
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l /\
    U32.v j < L.length l
  )))
  (ensures (
    U32.v i <> U32.v j /\
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l /\
    U32.v j < L.length l /\
    S.disjoint (list_nth_spec p b i h) (list_nth_spec p b j h)
  )))

let list_nth_spec_disjoint #b #t p b i j h =
  if U32.lt i j
  then list_nth_spec_lt_disjoint p b i j h
  else list_nth_spec_lt_disjoint p b j i h

let list_nth_precond
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

let list_nth_inv
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
  list_nth_precond p sv b i (Ghost.reveal h0) /\
  B.modifies_1 sl (Ghost.reveal h0) h /\
  j <= U32.v i /\
  B.live h sl /\ (
  let b' = Seq.index (B.as_seq h sl) 0 in (
  S.includes b b' /\ (
  parses (Ghost.reveal h0) (parse_list p) b (fun (l, _) ->
  parses (Ghost.reveal h0) (parse_list p) b' (fun (lr, _) ->
    U32.v i < L.length l /\
    L.length lr == L.length l - j
  ))) /\
  list_nth_spec p b i (Ghost.reveal h0) == list_nth_spec p b' (U32.sub i (U32.uint_to_t j)) (Ghost.reveal h0)
  ))

inline_for_extraction
val list_nth_advance
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
    list_nth_inv p sv b i h0 sl h (U32.v j) /\
    U32.v j < U32.v i
  ))
  (ensures (fun h1 _ h2 ->
    list_nth_inv p sv b i h0 sl h1 (U32.v j) /\
    U32.v j < U32.v i /\
    list_nth_inv p sv b i h0 sl h2 (U32.v j + 1)
  ))

#set-options "--z3rlimit 128"

let list_nth_advance #b #t p sv b i h0 sl j =
  let s = B.index sl 0ul in
  let h1 = HST.get () in
  let len = sv s in
  let s' = S.advance_slice s len in
  let h2 = HST.get () in
  assert (B.modifies_none h1 h2);
  B.upd sl 0ul s';
  let h3 = HST.get () in
  B.lemma_modifies_none_1_trans sl h1 h2 h3

#reset-options

inline_for_extraction
val list_nth
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
      U32.v i < L.length l
    ) /\
    b' == list_nth_spec p b i h
  ))

#set-options "--z3rlimit 32"

let list_nth #b #t p sv b i =
  let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let sl : B.buffer S.bslice = B.create b 1ul in
  let h2 = HST.get () in
  C.Loops.for
    0ul
    i
    (fun h j -> list_nth_inv p sv b i (Ghost.hide h2) sl h j)
    (fun j -> list_nth_advance p sv b i (Ghost.hide h2) sl j)
  ;
  let h3 = HST.get () in
  let tail = B.index sl 0ul in
  let len = sv tail in
  let res = S.truncate_slice tail len in
  let h4 = HST.get () in
  assert (B.modifies_none h3 h4);
  B.lemma_intro_modifies_1 sl h3 h4;
  B.lemma_modifies_1_trans sl h2 h3 h4;
  B.lemma_modifies_0_1' sl h1 h2 h4;
  HST.pop_frame ();
  let h5 = HST.get () in
  B.lemma_modifies_0_push_pop h0 h1 h4 h5;
  list_nth_spec_ext p b i h2 h0;
  res

let list_nth_constant_size_parser_postcond
  (#n: nat)
  (#b: bool)
  (#t: Type0)
  (p: constant_size_parser b n t)
  (b: S.bslice)
  (i: U32.t)
  (h: HS.mem)
: GTot Type0
=    parses h (parse_list p) b (fun (l, _) ->
      U32.v i < L.length l
    ) /\
    Prims.op_Multiply (U32.v i) n <= U32.v (S.length b) /\ (
    let b1 = S.advanced_slice b (U32.mul i (U32.uint_to_t n)) in
    n <= U32.v (S.length b1) /\ (
    let b2 = S.truncated_slice b1 (U32.uint_to_t n) in
    list_nth_spec p b i h == b2
  ))

val list_nth_constant_size_parser_correct
  (#n: nat)
  (#b: bool)
  (#t: Type0)
  (p: constant_size_parser b n t)
  (b: S.bslice)
  (i: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l
  )))
  (ensures (
    list_nth_constant_size_parser_postcond p b i h
  ))
  (decreases (U32.v i))

inline_for_extraction
let bounded_mult (a b c: U32.t) 
  (l: unit -> Lemma (Prims.op_Multiply (U32.v a) (U32.v b) <= U32.v c))
: Pure U32.t
  (requires True)
  (ensures (fun y ->
     FStar.UInt.size (Prims.op_Multiply (U32.v a) (U32.v b)) U32.n /\
     U32.v y == Prims.op_Multiply (U32.v a) (U32.v b) /\
     U32.v y <= U32.v c /\
     y == U32.mul a b
  ))
= l ();
  U32.mul a b

#set-options "--z3rlimit 512"

let rec list_nth_constant_size_parser_correct #n #b #t p b i h =
  if i = 0ul
  then begin
    S.advanced_slice_zero b;
    assert (list_nth_constant_size_parser_postcond p b i h)
  end else begin
    let b' = S.advanced_slice b (U32.uint_to_t n) in
    assert (list_nth_spec p b i h == list_nth_spec p b' (U32.sub i 1ul) h);
    list_nth_constant_size_parser_correct p b' (U32.sub i 1ul) h;
    assert (list_nth_constant_size_parser_postcond p b' (U32.sub i 1ul) h);
    let ka : U32.t = U32.sub i 1ul in
    let kb : U32.t = U32.uint_to_t n in
    let nj : nat = Prims.op_Multiply (U32.v ka) (U32.v kb) in
    let lemma1 () : Lemma (nj <= U32.v (S.length b')) = () in
    lemma1 ();
    let b1' = S.advanced_slice b' (U32.mul ka kb) in
    FStar.Math.Lemmas.distributivity_add_left 1 (U32.v i - 1) n;
    assert (n + Prims.op_Multiply (U32.v i - 1) n == Prims.op_Multiply (U32.v i) n);
    assert (Prims.op_Multiply (U32.v i) n <= n + U32.v (S.length b'));
    let l () : Lemma (Prims.op_Multiply (U32.v i) n <= U32.v (S.length b)) = () in
    let m : U32.t = bounded_mult i (U32.uint_to_t n) (S.length b) l in
    assert (U32.v m <= U32.v (S.length b));
    let b1 = S.advanced_slice b m in
    assert (b1 == b1');
    assert (list_nth_constant_size_parser_postcond p b i h)
  end

#reset-options

inline_for_extraction
val list_nth_constant_size_parser
  (#n: U32.t)
  (#b: bool)
  (#t: Type0)
  (p: constant_size_parser b (U32.v n) t)
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
      U32.v i < L.length l
    ) /\
    b' == list_nth_spec p b i h
  ))

#set-options "--z3rlimit 32"

let list_nth_constant_size_parser #n #b #t p b i =
  let h = HST.get () in
  list_nth_constant_size_parser_correct p b i h;
  let b1 = S.advance_slice b (U32.mul i n) in
  let b2 = S.truncate_slice b1 n in
  let h' = HST.get () in
  list_nth_spec_ext p b i h h' ;
  b2

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
