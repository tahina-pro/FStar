module LowParse.Base

module S = LowParse.Slice
module Seq = FStar.Seq
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Ghost = FStar.Ghost

type byte = U8.t
let bytes = S.bytes
/// the abstract model of input is a sequence of bytes, with a limit on size so
/// offsets always fit in a U32.t
let bytes32 = S.bytes32

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

[@"substitute"]
inline_for_extraction
let consumed_slice_length (input: S.bslice) : Tot Type0 =
  (off:U32.t{U32.v off <= U32.v (S.length input)})

/// A stateful parser that implements the same behavior as a pure parser. This
/// includes both the output and offset. The specification parser is an erased
/// type index; erasure helps guide extraction. The type is inlined for
/// extraction to make it clear that parsers are first-order functions taking a
/// buffer as input (as opposed to higher-order implementations that return a
/// function).
inline_for_extraction
let parser_st #t (p: bare_parser t) : Tot Type0 =
  input:S.bslice -> HST.Stack (option (t * consumed_slice_length input))
  (requires (fun h0 -> S.live h0 input))
  (ensures (fun h0 r h1 -> S.live h1 input /\
            S.modifies_none h0 h1 /\
            (let bs = S.as_seq h1 input in
            match p bs with
            | Some (v, n) -> Some? r /\
              begin
                let (rv, off) = Some?.v r in
                  v == rv /\ n == U32.v off
              end
            | None -> r == None)))

/// A stateful parser much like parser_st, except that error cases are
/// precluded. The precondition includes that the specification parser succeeds
/// on the input, and under this assumption a parser_st_nochk does not fail and
/// has the same behavior as the specification parser. The implementation need
/// not make error checks since those cases are impossible.
inline_for_extraction
let parser_st_nochk #t (p: bare_parser t) : Tot Type0 =
  input: S.bslice -> HST.Stack (t * consumed_slice_length input)
  (requires (fun h0 -> S.live h0 input /\
                    (let bs = S.as_seq h0 input in
                     Some? (parse p bs))))
  (ensures (fun h0 r h1 -> S.live h1 input /\
                  S.modifies_none h0 h1 /\
                  (let bs = S.as_seq h1 input in
                    Some? (parse p bs) /\
                    (let (v, n) = Some?.v (parse p bs) in
                     let (rv, off) = r in
                       v == rv /\
                       n == U32.v off))))

(** Slices that exactly correspond to some parsed data *)

unfold
let parses
  (#t: Type0)
  (h: HS.mem)
  (p: bare_parser t)
  (s: S.bslice)
  (k: ((t * consumed_slice_length s) -> GTot Type0))
: GTot Type0
= S.live h s /\ (
  let sq : bytes32 = S.as_seq h s in
  let y = parse p sq in (
  Some? y /\ (
  let (Some (v', l)) = y in
  k (v', U32.uint_to_t l)
  )))

unfold
let exactly_parses
  (#t: Type0)
  (h: HS.mem)
  (p: bare_parser t)
  (s: S.bslice)
  (k: (t -> GTot Type0))
: GTot Type0
= parses h p s (fun (v, len) -> S.length s == len /\ k v)

let parses_consumes_all_exactly_parses
  (#t: Type0)
  (h: HS.mem)
  (p: bare_parser t)
  (s: S.bslice)
  (k: ((t * consumed_slice_length s) -> GTot Type0))
: Lemma
  (requires (parses h p s k /\ consumes_all p))
  (ensures (exactly_parses h p s (fun v -> k (v, S.length s))))
= ()


/// A validation is an [option U32.t], where [Some off] indicates success and
/// consumes [off] bytes. A validation checks a parse result if it returns [Some
/// off] only when the parser also succeeds and returns the same offset, with
/// any result. Note that a validation need not be complete (in particular,
/// [None] validates any parse).


/// A stateful validator is parametrized by a specification parser. A validator
/// does not produce a value but only checks that the data is valid. The
/// specification ensures that when a validator accepts the input the parser
/// would succeed on the same input.
inline_for_extraction
let stateful_validator (#t: Type0) (p: bare_parser t) : Tot Type0 =
  input: S.bslice ->
  HST.Stack (option (consumed_slice_length input))
    (requires (fun h0 -> S.live h0 input))
    (ensures (fun h0 r h1 -> S.modifies_none h0 h1 /\ (
      Some? r ==> (
      let (Some len) = r in
      parses h0 p input (fun (_, len') -> len == len')
    ))))


/// Same thing, but where we already know that the data is valid. (In other words, how many offsets are skipped by the data being parsed.)
inline_for_extraction
let stateful_validator_nochk (#t: Type0) (p: bare_parser t) : Tot Type0 =
  input: S.bslice ->
  HST.Stack (consumed_slice_length input)
  (requires (fun h0 ->
    parses h0 p input (fun _ -> True)
  ))
  (ensures (fun h0 r h1 ->
    S.modifies_none h0 h1 /\
    parses h0 p input (fun (_, len) ->
      len == r
  )))
