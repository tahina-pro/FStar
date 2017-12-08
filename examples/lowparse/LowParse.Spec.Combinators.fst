module LowParse.Spec.Combinators
include LowParse.Spec.Base

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

(** Constant-size parsers *)

inline_for_extraction
let make_constant_size_parser_aux
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot (option t)))
: Tot (bare_parser t)
= fun (s: bytes32) ->
  if Seq.length s < sz
  then None
  else begin
    let s' : bytes32 = Seq.slice s 0 sz in
    match f s' with
    | None -> None
    | Some v ->
      let (sz: consumed_length s) = sz in
      Some (v, sz)
  end

let make_constant_size_parser_precond_precond
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot (option t)))
  (s1: bytes32 { Seq.length s1 == sz } )
  (s2: bytes32 { Seq.length s2 == sz } )
: GTot Type0
= (Some? (f s1) \/ Some? (f s2)) /\ f s1 == f s2

let make_constant_size_parser_precond
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot (option t)))
: GTot Type0
= forall (s1: bytes32 {Seq.length s1 == sz}) (s2: bytes32 {Seq.length s2 == sz}) .
    make_constant_size_parser_precond_precond sz t f s1 s2 ==> Seq.equal s1 s2

let make_constant_size_parser_precond'
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot (option t)))
: GTot Type0
= forall (s1: bytes32 {Seq.length s1 == sz}) (s2: bytes32 {Seq.length s2 == sz}) .
    make_constant_size_parser_precond_precond sz t f s1 s2 ==> s1 == s2

let make_constant_size_parser_injective
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot (option t)) {
    make_constant_size_parser_precond sz t f
  })
: Lemma
  (injective (make_constant_size_parser_aux sz t f))
= let p : bare_parser t = make_constant_size_parser_aux sz t f in
  let prf1
    (b1 b2: bytes32)
  : Lemma
    (requires (injective_precond p b1 b2))
    (ensures (injective_postcond p b1 b2))
  = assert (Some? (parse p b1));
    assert (Some? (parse p b2));
    let (Some (v1, len1)) = parse p b1 in
    let (Some (v2, len2)) = parse p b2 in
    assert ((len1 <: nat) == (len2 <: nat));
    assert ((len1 <: nat) == sz);
    assert ((len2 <: nat) == sz);
    assert (make_constant_size_parser_precond_precond sz t f (Seq.slice b1 0 len1) (Seq.slice b2 0 len2));
    assert (make_constant_size_parser_precond' sz t f)
  in
  Classical.forall_intro_2 (fun (b1: bytes32) -> Classical.move_requires (prf1 b1))

inline_for_extraction
let make_constant_size_parser
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot (option t)) {
    make_constant_size_parser_precond sz t f
  })
: Tot (parser (ParserStrong (StrongConstantSize sz ConstantSizeUnknown)) t)
= let p : bare_parser t = make_constant_size_parser_aux sz t f in
  make_constant_size_parser_injective sz t f;
  p

let make_total_constant_size_parser_precond
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot t))
: GTot Type0
= forall (s1: bytes32 {Seq.length s1 == sz}) (s2: bytes32 {Seq.length s2 == sz}) .
  f s1 == f s2 ==> Seq.equal s1 s2

inline_for_extraction
let make_total_constant_size_parser
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot t) {
    make_total_constant_size_parser_precond sz t f
  })
: Tot (parser (ParserStrong (StrongConstantSize sz ConstantSizeTotal)) t)
= let p : bare_parser t = make_constant_size_parser sz t (fun x -> Some (f x)) in
  p

(** Combinators *)

/// monadic return for the parser monad
unfold
let parse_ret' (#t:Type) (v:t) : Tot (bare_parser t) =
  fun (b: bytes32) -> Some (v, (0 <: consumed_length b))

unfold
let parse_ret (#t:Type) (v:t) : Tot (parser (ParserStrong (StrongConstantSize 0 ConstantSizeTotal)) t) =
  parse_ret' v

#set-options "--z3rlimit 16"

let fail_parser_kind_precond
  (k: parser_kind)
: GTot Type0
= match k with
  | ParserStrong ks ->
    begin match ks with
    | StrongConstantSize _ kc ->
      begin match kc with
      | ConstantSizeTotal -> False
      | _ -> True
      end
    | _ -> True
    end
  | _ -> True

inline_for_extraction
let fail_parser'
  (t: Type0)
: Tot (bare_parser t)
= fun _ -> None

inline_for_extraction
let fail_parser
  (k: parser_kind)
  (t: Type0)
: Pure (parser k t)
  (requires (fail_parser_kind_precond k))
  (ensures (fun _ -> True))
= let p = fail_parser' t in
  assert (forall (sz: nat) . is_constant_size_parser sz p);
  p

/// monadic bind for the parser monad

inline_for_extraction
val and_then_bare : #t:Type -> #t':Type ->
                p:bare_parser t ->
                p': (t -> Tot (bare_parser t')) ->
                Tot (bare_parser t')
let and_then_bare #t #t' p p' =
    fun (b: bytes32) ->
    match parse p b with
    | Some (v, l) ->
      begin
	let p'v = p' v in
	let s' : bytes32 = Seq.slice b l (Seq.length b) in
	match parse p'v s' with
	| Some (v', l') ->
	  let res : consumed_length b = l + l' in
	  Some (v', res)
	| None -> None
      end
    | None -> None

val and_then_no_lookahead_weak_on
    (#t:Type)
    (#t':Type)
    (p: bare_parser t)
    (p': (t -> Tot (bare_parser t')))
    (x: bytes32) 
    (x' : bytes32)
  : Lemma
    (requires (
      no_lookahead_weak p /\
      (forall (x: t) . no_lookahead_weak (p' x))
    ))
    (ensures (no_lookahead_weak_on (and_then_bare p p') x x'))

let and_then_no_lookahead_weak_on #t #t' p p' x x' =
    let f = and_then_bare p p' in
    match f x with
    | Some v -> 
      let (y, off) = v in
      let off : nat = off in
      let (off_x : consumed_length x ) = off in
      if off <= Seq.length x'
      then
	let (off_x' : consumed_length x') = off in
	let g () : Lemma
	  (requires (Seq.length x' <= Seq.length x /\ Seq.slice x' 0 off_x' == Seq.slice x 0 off_x))
	  (ensures (
	    Some? (parse f x') /\ (
	    let (Some v') = parse f x' in
	    let (y', off') = v' in
	    y == y' /\ (off <: nat) == (off' <: nat)
	  )))
	= assert (Some? (parse p x));
	  let (Some (y1, off1)) = parse p x in
	  assert (off1 <= off);
	  assert (off1 <= Seq.length x');
	  assert (Seq.slice x' 0 off1 == Seq.slice (Seq.slice x' 0 off_x') 0 off1);
	  assert (Seq.slice x' 0 off1 == Seq.slice x 0 off1);
	  assert (no_lookahead_weak_on p x x');
	  assert (Some? (parse p x'));
	  let (Some v1') = parse p x' in
	  let (y1', off1') = v1' in
	  assert (y1 == y1' /\ (off1 <: nat) == (off1' <: nat));
	  let x2 : bytes32 = Seq.slice x off1 (Seq.length x) in
	  let x2' : bytes32 = Seq.slice x' off1 (Seq.length x') in
	  let p2 = p' y1 in
	  assert (Some? (parse p2 x2));
	  let (Some (y', off2)) = parse p2 x2 in
	  assert (off == off1 + off2);
	  assert (off2 <= Seq.length x2);
	  assert (off2 <= Seq.length x2');
	  assert (Seq.length x2' <= Seq.length x2);
	  assert (Seq.slice x2' 0 off2 == Seq.slice (Seq.slice x' 0 off_x') off1 (off1 + off2));
	  assert (Seq.slice x2' 0 off2 == Seq.slice x2 0 off2);
	  assert (no_lookahead_weak_on p2 x2 x2');
	  ()
	in
	Classical.move_requires g ()
      else ()
    | _ -> ()

let and_then_no_lookahead_weak
  (#t:Type)
  (#t':Type)
  (p: bare_parser t)
  (p': (t -> Tot (bare_parser t')))
: Lemma
  (requires (
    no_lookahead_weak p /\
    (forall (x: t) . no_lookahead_weak (p' x))
  ))
  (ensures (no_lookahead_weak (and_then_bare p p')))
= Classical.forall_intro_2 (fun x -> Classical.move_requires (and_then_no_lookahead_weak_on p p' x))

let and_then_cases_injective_precond
  (#t:Type)
  (#t':Type)
  (p': (t -> Tot (bare_parser t')))
  (x1 x2: t)
  (b1 b2: bytes32)
: GTot Type0
= Some? ((p' x1) b1) /\
  Some? ((p' x2) b2) /\ (
    let (Some (v1, _)) = (p' x1) b1 in
    let (Some (v2, _)) = (p' x2) b2 in
    v1 == v2
  )

let and_then_cases_injective
  (#t:Type)
  (#t':Type)
  (p': (t -> Tot (bare_parser t')))
: GTot Type0
= forall (x1 x2: t) (b1 b2: bytes32) .
  and_then_cases_injective_precond p' x1 x2 b1 b2 ==>
  x1 == x2

val and_then_injective
  (#t:Type)
  (#t':Type)
  (p: bare_parser t)
  (p': (t -> Tot (bare_parser t')))
: Lemma
  (requires (
    injective p /\
    (forall (x: t) . injective (p' x)) /\
    and_then_cases_injective p'
  ))
  (ensures (
    injective (and_then_bare p p')
  ))

let and_then_injective #t #t' p p' =
  let ps = and_then_bare p p' in
  let f
    (b1 b2: bytes32)
  : Lemma
    (requires (injective_precond ps b1 b2))
    (ensures (injective_postcond ps b1 b2))
  = let (Some (v1, len1)) = p b1 in
    let (Some (v2, len2)) = p b2 in
    let b1' : bytes32 = Seq.slice b1 len1 (Seq.length b1) in
    let b2' : bytes32 = Seq.slice b2 len2 (Seq.length b2) in
    assert (Some? ((p' v1) b1'));
    assert (Some? ((p' v2) b2'));
    assert (and_then_cases_injective_precond p' v1 v2 b1' b2');
    assert (v1 == v2);
    assert (injective_precond p b1 b2);
    assert ((len1 <: nat) == (len2 <: nat));
    assert (injective (p' v1));
    assert (injective_precond (p' v1) b1' b2');
    assert (injective_postcond (p' v1) b1' b2');
    let (Some (_, len1')) = (p' v1) b1' in
    let (Some (_, len2')) = (p' v2) b2' in
    assert ((len1' <: nat) == (len2' <: nat));
    Seq.lemma_split (Seq.slice b1 0 (len1 + len1')) len1;
    Seq.lemma_split (Seq.slice b2 0 (len2 + len2')) len1;
    assert (injective_postcond ps b1 b2)
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (f x))

val and_then_no_lookahead_on
    (#t:Type)
    (#t':Type)
    (p: bare_parser t)
    (p': (t -> Tot (bare_parser t')))
    (x: bytes32) 
    (x' : bytes32)
  : Lemma
    (requires (
      no_lookahead p /\
      injective p /\
      (forall (x: t) . no_lookahead (p' x))
    ))
    (ensures (no_lookahead_on (and_then_bare p p') x x'))

let and_then_no_lookahead_on #t #t' p p' x x' =
    let f = and_then_bare p p' in
    match f x with
    | Some v -> 
      let (y, off) = v in
      let off : nat = off in
      let (off_x : consumed_length x ) = off in
      if off <= Seq.length x'
      then
	let (off_x' : consumed_length x') = off in
	let g () : Lemma
	  (requires (Seq.slice x' 0 off_x' == Seq.slice x 0 off_x))
	  (ensures (
	    Some? (f x') /\ (
	    let (Some v') = f x' in
	    let (y', off') = v' in
	    y == y'
	  )))
	= assert (Some? (p x));
	  let (Some (y1, off1)) = p x in
	  assert (off1 <= off);
	  assert (off1 <= Seq.length x');
	  assert (Seq.slice x' 0 off1 == Seq.slice (Seq.slice x' 0 off_x') 0 off1);
	  assert (Seq.slice x' 0 off1 == Seq.slice x 0 off1);
	  assert (no_lookahead_on p x x');
	  assert (Some? (p x'));
	  let (Some v1') = p x' in
	  let (y1', off1') = v1' in
	  assert (y1 == y1');
	  assert (injective_precond p x x');
	  assert ((off1 <: nat) == (off1' <: nat));
	  let x2 : bytes32 = Seq.slice x off1 (Seq.length x) in
	  let x2' : bytes32 = Seq.slice x' off1 (Seq.length x') in
	  let p2 = p' y1 in
	  assert (Some? (p2 x2));
	  let (Some (y2, off2)) = p2 x2 in
	  assert (off == off1 + off2);
	  assert (off2 <= Seq.length x2);
	  assert (off2 <= Seq.length x2');
	  assert (Seq.slice x2' 0 off2 == Seq.slice (Seq.slice x' 0 off_x') off1 (off1 + off2));
	  assert (Seq.slice x2' 0 off2 == Seq.slice x2 0 off2);
	  assert (no_lookahead_on p2 x2 x2');
	  assert (Some? (p2 x2'));
	  let (Some v2') = p2 x2' in
	  let (y2', _) = v2' in
	  assert (y2 == y2')
	in
	Classical.move_requires g ()
      else ()
    | _ -> ()

let and_then_kind
  (k1 k2: parser_kind)
: Tot parser_kind
= match k1 with
  | ParserStrong k1s ->
    begin match k2 with
    | ParserStrong k2s -> ParserStrong
      begin match k1s with
      | StrongConstantSize sz1 k1c ->
	begin match k2s with
	| StrongConstantSize sz2 k2c -> StrongConstantSize (sz1 + sz2)
	  begin match k1c with
	  | ConstantSizeTotal ->
	    begin match k2c with
	    | ConstantSizeTotal -> ConstantSizeTotal
	    | _ -> ConstantSizeUnknown
	    end
	  | _ -> ConstantSizeUnknown
	  end
	| _ -> StrongUnknown
	end
      | _ -> StrongUnknown
      end
    | ParserConsumesAll -> ParserConsumesAll
    | _ -> ParserUnknown
    end
  | _ ->
    begin match k2 with
    | ParserConsumesAll -> ParserConsumesAll
    | ParserStrong k2s ->
      begin match k2s with
      | StrongConstantSize sz2 k2c ->
	if sz2 = 0
	then k1
	else ParserUnknown
      | _ -> ParserUnknown
      end
    | _ -> ParserUnknown
    end

let and_then_no_lookahead
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
: Lemma
  (requires (
    and_then_cases_injective p'
  ))
  (ensures ((ParserStrong? k /\ ParserStrong? k') ==> no_lookahead (and_then_bare p p')))
= if ParserStrong? k && ParserStrong? k' then
    Classical.forall_intro_2 (fun x -> Classical.move_requires (and_then_no_lookahead_on p p' x))
  else ()

inline_for_extraction
val and_then
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
: Pure (parser (and_then_kind k k') t')
  (requires (
    and_then_cases_injective p'
  ))
  (ensures (fun _ -> True))
		
let and_then #k #t p #k' #t' p' =
  let f : bare_parser t' = and_then_bare p p' in
  and_then_no_lookahead_weak p p';
  and_then_injective p p';
  and_then_no_lookahead p p';
  f

(* Special case for non-dependent parsing *)

inline_for_extraction
let nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
: Tot (parser (and_then_kind k1 k2) (t1 * t2))
= p1 `and_then` (fun v1 -> p2 `and_then` (fun v2 -> (parse_ret (v1, v2))))

(** Apply a total transformation on parsed data *)

unfold
let coerce
  (t2: Type)
  (#t1: Type)
  (x: t1)
: Pure t2
  (requires (t1 == t2))
  (ensures (fun _ -> True))
= (x <: t2)

inline_for_extraction
let parse_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
: Pure (parser k t2)
  (requires (
    forall (x x' : t1) . f2 x == f2 x' ==> x == x'
  ))
  (ensures (fun _ -> True))
= coerce (parser k t2) (and_then p1 (fun v1 -> parse_ret (f2 v1)))

(** Refinements *)

let parse_filter_kind (k: parser_kind) : Tot parser_kind =
  match k with
  | ParserStrong ks -> ParserStrong
    begin match ks with
    | StrongConstantSize sz _ -> StrongConstantSize sz ConstantSizeUnknown
    | _ -> ks
    end
  | _ -> k

inline_for_extraction
let parse_filter_payload
  (#t: Type0)
  (f: (t -> Tot bool))
  (v: t)
: Tot (parser (ParserStrong (StrongConstantSize 0 ConstantSizeUnknown)) (x: t { f x == true }))
= if f v
  then
    let v' : (x: t { f x == true } ) = v in
    weaken (ParserStrong (StrongConstantSize 0 ConstantSizeUnknown)) (parse_ret v')
  else fail_parser (ParserStrong (StrongConstantSize 0 ConstantSizeUnknown)) (x: t {f x == true} )

inline_for_extraction
let parse_filter
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (f: (t -> Tot bool))
: Tot (parser (parse_filter_kind k) (x: t { f x == true }))
= p `and_then` (parse_filter_payload f)

(* Helpers to define `if` combinators *)

let cond_true (cond: bool) : Tot Type0 = (u: unit { cond == true } )

let cond_false (cond: bool) : Tot Type0 = (u: unit { cond == false } )

let if_combinator
  (t: Type0)
: Tot Type0
= (cond: bool) ->
  (sv_true: (cond_true cond -> Tot t)) ->
  (sv_false: (cond_false cond -> Tot t)) ->
  Tot t

inline_for_extraction
let default_if
  (t: Type0)
: Tot (if_combinator t)
= fun
  (cond: bool)
  (s_true: (cond_true cond -> Tot t))
  (s_false: (cond_false cond -> Tot t))
-> if cond
  then s_true ()
  else s_false ()
