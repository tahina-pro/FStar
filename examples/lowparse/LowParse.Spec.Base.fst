module LowParse.Spec.Base
include LowParse.Bytes

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

/// parse a value of type t
///
/// - the parser can fail (currently reporting an uninformative [None])
/// - it returns the parsed value as well as the number of bytes read
///   (this is intended to be the number of bytes to advance the input pointer)
///
/// note that the type now forbids lookahead; the parser cannot depend on
/// values beyond the returned offset
///
/// these parsers are used as specifications, and thus use unrepresentable types
/// such as byte sequences and natural numbers and are always pure

[@"substitute"]
inline_for_extraction
let consumed_length (b: bytes32) : Tot Type0 = (n: nat { n <= Seq.length b } )

// switch to Tot if you want OCaml extraction
let bare_parser (t:Type0) : Tot Type0 = (b: bytes32) -> GTot (option (t * consumed_length b))

let parse
  (#t: Type0)
  (p: bare_parser t)
  (input: bytes32)
: GTot (option (t * consumed_length input))
= p input

let no_lookahead_weak_on
  (t: Type0)
  (f: bare_parser t)
  (x x' : bytes32)
: GTot Type0
= Some? (parse f x) ==> (
  let (Some v) = parse f x in
  let (y, off) = v in (
  (off <= Seq.length x' /\ Seq.length x' <= Seq.length x /\ Seq.slice x' 0 off == Seq.slice x 0 off) ==>
  Some? (parse f x') /\ (
  let (Some v') = parse f x' in
  let (y', off') = v' in
  y == y' /\ (off <: nat) == (off' <: nat)
  )))

let no_lookahead_weak_on_ext
  (#t: Type0)
  (f1 f2: bare_parser t)
  (x x' : bytes32)
: Lemma
  (requires (
    parse f2 x == parse f1 x /\
    parse f2 x' == parse f1 x'
  ))
  (ensures (
    no_lookahead_weak_on _ f2 x x' <==> no_lookahead_weak_on _ f1 x x'
  ))
= ()

let no_lookahead_weak
  (t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (x x' : bytes32) . no_lookahead_weak_on t f x x'

let no_lookahead_weak_ext
  (#t: Type0)
  (f1 f2: bare_parser t)
: Lemma
  (requires (
    (forall (b: bytes32) . parse f2 b == parse f1 b)
  ))
  (ensures (
    no_lookahead_weak t f2 <==> no_lookahead_weak t f1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (no_lookahead_weak_on_ext f1 f2 b1))

(** Injectivity of parsing *)

let injective_precond
  (#t: Type0)
  (p: bare_parser t)
  (b1 b2: bytes32)
: GTot Type0
= Some? (parse p b1) /\
  Some? (parse p b2) /\ (
    let (Some (v1, len1)) = parse p b1 in
    let (Some (v2, len2)) = parse p b2 in
    v1 == v2
  )

let injective_precond_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
  (b1 b2: bytes32)
: Lemma
  (requires (
    parse p2 b1 == parse p1 b1 /\
    parse p2 b2 == parse p1 b2
  ))
  (ensures (
    injective_precond p2 b1 b2 <==> injective_precond p1 b1 b2
  ))
= ()

let injective_postcond
  (#t: Type0)
  (p: bare_parser t)
  (b1 b2: bytes32)
: GTot Type0
= Some? (parse p b1) /\
  Some? (parse p b2) /\ (
    let (Some (v1, len1)) = parse p b1 in
    let (Some (v2, len2)) = parse p b2 in
    (len1 <: nat) == (len2 <: nat) /\
    Seq.slice b1 0 len1 == Seq.slice b2 0 len2
  )

let injective_postcond_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
  (b1 b2: bytes32)
: Lemma
  (requires (
    parse p2 b1 == parse p1 b1 /\
    parse p2 b2 == parse p1 b2
  ))
  (ensures (
    injective_postcond p2 b1 b2 <==> injective_postcond p1 b1 b2
  ))
= ()

let injective (#t: Type0) (p: bare_parser t) : GTot Type0 =
  forall (b1 b2: bytes32) .
  injective_precond p b1 b2 ==>
  injective_postcond p b1 b2

let injective_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
: Lemma
  (requires (
    forall (b: bytes32) . parse p2 b == parse p1 b
  ))
  (ensures (
    injective p2 <==> injective p1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (injective_precond_ext p1 p2 b1));
  Classical.forall_intro_2 (fun b1 -> Classical.move_requires (injective_postcond_ext p1 p2 b1))
  
let no_lookahead_on_precond
  (t: Type0)
  (f: bare_parser t)
  (x x' : bytes32)
: GTot Type0
= Some? (parse f x) /\ (
    let (Some v) = parse f x in
    let (_, off) = v in
    off <= Seq.length x' /\
    Seq.slice x' 0 off == Seq.slice x 0 off
  )

let no_lookahead_on_postcond
  (t: Type0)
  (f: bare_parser t)
  (x x' : bytes32)
: GTot Type0
= Some? (parse f x) ==> (
  let (Some v) = parse f x in
  let (y, _) = v in
  Some? (parse f x') /\ (
  let (Some v') = parse f x' in
  let (y', _) = v' in
  y == y'
  ))

let no_lookahead_on
  (t: Type0)
  (f: bare_parser t)
  (x x' : bytes32)
: GTot Type0
= no_lookahead_on_precond t f x x' ==> no_lookahead_on_postcond t f x x'

let no_lookahead_on_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
  (b1 b2: bytes32)
: Lemma
  (requires (
    parse p2 b1 == parse p1 b1 /\
    parse p2 b2 == parse p1 b2
  ))
  (ensures (
    no_lookahead_on _ p2 b1 b2 <==> no_lookahead_on _ p1 b1 b2
  ))
= ()

let no_lookahead
  (t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (x x' : bytes32) . no_lookahead_on t f x x'

let no_lookahead_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
: Lemma
  (requires (
    forall (b: bytes32) . parse p2 b == parse p1 b
  ))
  (ensures (
    no_lookahead _ p2 <==> no_lookahead _ p1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (no_lookahead_on_ext p1 p2 b1))

let parser'
  (b: bool)
  (t: Type0)
: Tot Type0
= (f: bare_parser t { no_lookahead_weak t f /\ injective f /\ (if b then no_lookahead t f else True) } )

let weak_parser (t: Type0) : Tot Type0 = parser' false t

let parser (t: Type0) : Tot Type0 = parser' true t

unfold
let weaken (#t: Type0) (p: parser t) : Tot (weak_parser t) = (p <: bare_parser t) <: weak_parser t

unfold
let weaken' (b: bool) (#t: Type0) (p: parser t) : Tot (parser' b t) = (p <: bare_parser t) <: parser' b t

unfold
let strengthen
  (#t: Type0)
  (p: weak_parser t)
: Pure (parser t)
  (requires (no_lookahead t p))
  (ensures (fun _ -> True))
= (p <: bare_parser t) <: parser t

(** A parser that always consumes all its input *)

let consumes_all
  (#t: Type0)
  (p: bare_parser t)
: GTot Type0
= forall (b: bytes32) . Some? (parse p b) ==> (
    let (Some (_, len)) = parse p b in
    Seq.length b == len
  )
