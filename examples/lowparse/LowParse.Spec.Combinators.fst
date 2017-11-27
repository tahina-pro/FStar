module LowParse.Spec.Combinators
include LowParse.Spec.Base

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Ghost = FStar.Ghost

(** Combinators *)
 
/// monadic return for the parser monad
noextract
let parse_ret (#t:Type) (v:t) : Tot (parser t) =
  ((fun (b: bytes32) ->
    let z : consumed_length b = 0 in
    Some (v, z)) <: parser t)

/// parser that always fails
noextract
let fail_parser (#t: Type0) : Tot (parser t) =
  (fun b -> None) <: parser t

/// monadic bind for the parser monad

noextract
val and_then_bare : #t:Type -> #t':Type ->
                p:bare_parser t ->
                p': (t -> GTot (bare_parser t')) ->
                Tot (bare_parser t')
let and_then_bare #t #t' p p' =
    fun (b: bytes32) ->
    match p b with
    | Some (v, l) ->
      begin
	let p'v = p' v in
	match p'v (Seq.slice b l (Seq.length b)) with
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
    (p': (t -> GTot (bare_parser t')))
    (x: bytes32) 
    (x' : bytes32)
  : Lemma
    (requires (
      no_lookahead_weak t p /\
      (forall (x: t) . no_lookahead_weak t' (p' x))
    ))
    (ensures (no_lookahead_weak_on t' (and_then_bare p p') x x'))

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
	  assert (no_lookahead_weak_on t p x x');
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
	  assert (no_lookahead_weak_on t' p2 x2 x2');
	  ()
	in
	Classical.move_requires g ()
      else ()
    | _ -> ()

let and_then_cases_injective_precond
  (#t:Type)
  (#t':Type)
  (p': (t -> GTot (bare_parser t')))
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
  (p': (t -> GTot (bare_parser t')))
: GTot Type0
= forall (x1 x2: t) (b1 b2: bytes32) .
  and_then_cases_injective_precond p' x1 x2 b1 b2 ==>
  x1 == x2

val and_then_injective
  (#t:Type)
  (#t':Type)
  (p: bare_parser t)
  (p': (t -> GTot (bare_parser t')))
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
    (p': (t -> GTot (bare_parser t')))
    (x: bytes32) 
    (x' : bytes32)
  : Lemma
    (requires (
      no_lookahead t p /\
      injective p /\
      (forall (x: t) . no_lookahead t' (p' x))
    ))
    (ensures (no_lookahead_on t' (and_then_bare p p') x x'))

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
	  assert (no_lookahead_on t p x x');
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
	  assert (no_lookahead_on t' p2 x2 x2');
	  assert (Some? (p2 x2'));
	  let (Some v2') = p2 x2' in
	  let (y2', _) = v2' in
	  assert (y2 == y2')
	in
	Classical.move_requires g ()
      else ()
    | _ -> ()

noextract
val and_then
  (#b: bool)
  (#t:Type)
  (#t':Type)
  (p:parser' b t)
  (p': (t -> GTot (parser' b t')))
: Pure (parser' b t')
  (requires (
    and_then_cases_injective p'
  ))
  (ensures (fun _ -> True))
		
let and_then #b #t #t' p p' =
  let f = and_then_bare p p' in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (and_then_no_lookahead_weak_on p p' x));
  and_then_injective p p';
  if b then begin
    Classical.forall_intro_2 (fun x -> Classical.move_requires (and_then_no_lookahead_on p p' x));
    (f <: parser t')
  end else
    (f <: weak_parser t')

(* Special case for non-dependent parsing *)

noextract
let nondep_then
  (#b: bool)
  (#t1 #t2: Type0)
  (p1: parser' b t1)
  (p2: parser' b t2)
: Tot (parser' b (t1 * t2))
= p1 `and_then` (fun v1 -> p2 `and_then` (fun v2 -> (weaken' b (parse_ret (v1, v2)))))

(** Apply a total transformation on parsed data *)

noextract
let parse_synth
  (#b: bool)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser' b t1)
  (f2: t1 -> GTot t2)
: Pure (parser' b t2)
  (requires (
    forall (x x' : t1) . f2 x == f2 x' ==> x == x'
  ))
  (ensures (fun _ -> True))
= let f (v1: t1) : GTot (parser' b t2) =
    let v2 = f2 v1 in
    weaken' b (parse_ret v2)
  in
  and_then p1 f


(** Parsing data of constant size *)

let constant_size_parser_prop
  (sz: nat)
  (t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes32) .
  Some? (f s) ==> (
    let (_, consumed) = Some?.v (f s) in
    sz == consumed
  )
  
let constant_size_parser
  (b: bool)
  (sz: nat)
  (t: Type0)
: Tot Type0
= (f: parser' b t { constant_size_parser_prop sz t f } )

noextract
let make_constant_size_parser
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot (option t)) {
    forall (s1: bytes32 {Seq.length s1 == sz}) (s2: bytes32 {Seq.length s2 == sz}) .
    ((Some? (f s1) \/ Some? (f s2)) /\ f s1 == f s2) ==> Seq.equal s1 s2
  })
: Tot (constant_size_parser true sz t)
= let () = () in
  let prf
    (s1: bytes32 {Seq.length s1 == sz})
    (s2: bytes32 {Seq.length s2 == sz})
  : Lemma
    (requires (
      (Some? (f s1) \/ Some? (f s2)) /\
      f s1 == f s2
    ))
    (ensures (s1 == s2))
  = assert (Seq.equal s1 s2)
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf x));
  fun (s: bytes32) ->
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

let total_constant_size_parser
  (sz: nat)
  (t: Type0)
: Tot Type0
= (f: constant_size_parser true sz t {
    forall (s: bytes32) . {:pattern (f s) }
    (Seq.length s < sz) == (None? (f s))
  })

noextract
let make_total_constant_size_parser
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot t) {
    forall (s1: bytes32 {Seq.length s1 == sz}) (s2: bytes32 {Seq.length s2 == sz}) .
    f s1 == f s2 ==> Seq.equal s1 s2
  })
: Tot (total_constant_size_parser sz t)
= make_constant_size_parser sz t (fun x -> Some (f x))

(** Refinements *)

noextract
let parse_filter
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (f: (t -> GTot bool))
: Tot (parser' b (x: t { f x == true }))
= p `and_then` (fun (v: t) -> weaken' b (
    if f v
    then
      let (v' : t { f v' == true } ) = v in
      parse_ret v'
    else fail_parser
  ))

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
