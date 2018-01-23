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
let consumed_length (b: bytes) : Tot Type0 = (n: nat { n <= Seq.length b } )

// switch to Tot if you want OCaml extraction
let bare_parser (t:Type0) : Tot Type0 = (b: bytes) -> Tot (option (t * consumed_length b))

inline_for_extraction
let parse
  (#t: Type0)
  (p: bare_parser t)
  (input: bytes)
: Tot (option (t * consumed_length input))
= p input

let no_lookahead_weak_on
  (#t: Type0)
  (f: bare_parser t)
  (x x' : bytes)
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
  (x x' : bytes)
: Lemma
  (requires (
    parse f2 x == parse f1 x /\
    parse f2 x' == parse f1 x'
  ))
  (ensures (
    no_lookahead_weak_on f2 x x' <==> no_lookahead_weak_on f1 x x'
  ))
= ()

let no_lookahead_weak
  (#t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (x x' : bytes) . no_lookahead_weak_on f x x'

let no_lookahead_weak_ext
  (#t: Type0)
  (f1 f2: bare_parser t)
: Lemma
  (requires (
    (forall (b: bytes) . parse f2 b == parse f1 b)
  ))
  (ensures (
    no_lookahead_weak f2 <==> no_lookahead_weak f1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (no_lookahead_weak_on_ext f1 f2 b1))

(** Injectivity of parsing *)

let injective_precond
  (#t: Type0)
  (p: bare_parser t)
  (b1 b2: bytes)
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
  (b1 b2: bytes)
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
  (b1 b2: bytes)
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
  (b1 b2: bytes)
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
  forall (b1 b2: bytes) .
  injective_precond p b1 b2 ==>
  injective_postcond p b1 b2

let injective_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
: Lemma
  (requires (
    forall (b: bytes) . parse p2 b == parse p1 b
  ))
  (ensures (
    injective p2 <==> injective p1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (injective_precond_ext p1 p2 b1));
  Classical.forall_intro_2 (fun b1 -> Classical.move_requires (injective_postcond_ext p1 p2 b1))
  
let no_lookahead_on_precond
  (#t: Type0)
  (f: bare_parser t)
  (x x' : bytes)
: GTot Type0
= Some? (parse f x) /\ (
    let (Some v) = parse f x in
    let (_, off) = v in
    off <= Seq.length x' /\
    Seq.slice x' 0 off == Seq.slice x 0 off
  )

let no_lookahead_on_postcond
  (#t: Type0)
  (f: bare_parser t)
  (x x' : bytes)
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
  (#t: Type0)
  (f: bare_parser t)
  (x x' : bytes)
: GTot Type0
= no_lookahead_on_precond f x x' ==> no_lookahead_on_postcond f x x'

let no_lookahead_on_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
  (b1 b2: bytes)
: Lemma
  (requires (
    parse p2 b1 == parse p1 b1 /\
    parse p2 b2 == parse p1 b2
  ))
  (ensures (
    no_lookahead_on p2 b1 b2 <==> no_lookahead_on p1 b1 b2
  ))
= ()

let no_lookahead
  (#t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (x x' : bytes) . no_lookahead_on f x x'

let no_lookahead_ext
  (#t: Type0)
  (p1 p2: bare_parser t)
: Lemma
  (requires (
    forall (b: bytes) . parse p2 b == parse p1 b
  ))
  (ensures (
    no_lookahead p2 <==> no_lookahead p1
  ))
= Classical.forall_intro_2 (fun b1 -> Classical.move_requires (no_lookahead_on_ext p1 p2 b1))


(** A parser that always consumes all its input *)

let consumes_all
  (#t: Type0)
  (p: bare_parser t)
: GTot Type0
= forall (b: bytes) . Some? (parse p b) ==> (
    let (Some (_, len)) = parse p b in
    Seq.length b == len
  )

(** Parsing data of bounded size *)

let parses_at_least
  (sz: nat)
  (#t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes) .
  Some? (parse f s) ==> (
    let (_, consumed) = Some?.v (parse f s) in
    sz <= (consumed <: nat)
  )

let parses_at_least_0
  (#t: Type0)
  (f: bare_parser t)
: Lemma
  (parses_at_least 0 f)
= ()

let parses_at_least_le
  (sz sz': nat)
  (#t: Type0)
  (f: bare_parser t)
: Lemma
  (requires (
    parses_at_least sz f /\
    sz' <= sz
  ))
  (ensures (
    parses_at_least sz' f
  ))
= ()


(** A parser that always consumes at least one byte.

A list can be serialized only if the parser for elements always
consumes at least one byte. Anyway, since we require such a parser to
have the prefix property, this is always true except for the parser
for empty data.

*)

let nonempty_strong_parser_consumes_at_least_one_byte
  (#t: Type0)
  (p: bare_parser t)
  (x: bytes)
: Lemma
  (requires (
    no_lookahead_weak p /\
    no_lookahead p /\
    injective p /\ (
    let px = parse p x in
    Some? px /\ (
    let (Some (_, len)) = px in
    len > 0
  ))))
  (ensures (
    parses_at_least 1 p
  ))
= let prf
    (x' : bytes)
  : Lemma
    (requires (Some? (parse p x')))
    (ensures (
      let px' = parse p x' in
      Some? px' /\ (
      let (Some (_, len')) = px' in
      len' > 0
    )))
  = let (Some (_, len')) = parse p x' in
    if len' > 0
    then ()
    else begin
      assert (no_lookahead_weak_on p x' Seq.createEmpty);
      assert (no_lookahead_on p Seq.createEmpty x);
      assert (no_lookahead_on_precond p Seq.createEmpty x);
      assert (no_lookahead_on_postcond p Seq.createEmpty x);
      assert (injective_precond p Seq.createEmpty x);
      assert (injective_postcond p Seq.createEmpty x)
    end
  in
  Classical.forall_intro (Classical.move_requires prf)


let parses_at_most
  (sz: nat)
  (#t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes) .
  Some? (parse f s) ==> (
    let (_, consumed) = Some?.v (parse f s) in
    sz >= (consumed <: nat)
  )

let is_constant_size_parser
  (sz: nat)
  (#t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes) .
  Some? (parse f s) ==> (
    let (_, consumed) = Some?.v (parse f s) in
    sz == (consumed <: nat)
  )

let is_constant_size_parser_equiv
  (sz: nat)
  (#t: Type0)
  (f: bare_parser t)
: Lemma
  (is_constant_size_parser sz f <==> (parses_at_least sz f /\ parses_at_most sz f))
= ()

let is_total_constant_size_parser
  (sz: nat)
  (#t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes) . {:pattern (f s) }
  (Seq.length s < sz) == (None? (f s))

type parser_subkind =
  | ParserStrong
  | ParserConsumesAll

let parser_subkind_prop (k: parser_subkind) (#t: Type0) (f: bare_parser t) : GTot Type0 =
  match k with
  | ParserStrong ->
    no_lookahead f
  | ParserConsumesAll ->
    consumes_all f

type parser_kind' = {
  parser_kind_low: nat;
  parser_kind_high: option nat;
  parser_kind_total: bool;
  parser_kind_subkind: option parser_subkind;
}

let parser_kind = (x: parser_kind' {
  Some? x.parser_kind_high ==> x.parser_kind_low <= Some?.v x.parser_kind_high
})

let parser_kind_prop (#t: Type0) (k: parser_kind) (f: bare_parser t) : GTot Type0 =
  no_lookahead_weak f /\
  injective f /\
  parses_at_least k.parser_kind_low f /\
  (Some? k.parser_kind_high ==> (parses_at_most (Some?.v k.parser_kind_high) f)) /\
  (((k.parser_kind_high == Some k.parser_kind_low) /\ (k.parser_kind_total == true)) ==> is_total_constant_size_parser k.parser_kind_low f) /\
  (Some? k.parser_kind_subkind ==> parser_subkind_prop (Some?.v k.parser_kind_subkind) f)

let parser
  (k: parser_kind)
  (t: Type0)
: Tot Type0
= (f: bare_parser t { parser_kind_prop k f } )

let parser_kind_prop_intro
  (k: parser_kind)
  (#t: Type0)
  (f: parser k t)
: Lemma
  (parser_kind_prop k f)
= ()

let is_weaker_than
  (k1 k2: parser_kind)
: GTot Type0
= k1.parser_kind_low <= k2.parser_kind_low /\
  (Some? k1.parser_kind_high ==> (
    Some? k2.parser_kind_high /\
    Some?.v k2.parser_kind_high <= Some?.v k1.parser_kind_high
  )) /\
  (k1.parser_kind_total == true ==> k2.parser_kind_total == true) /\
  (Some? k1.parser_kind_subkind ==> k1.parser_kind_subkind == k2.parser_kind_subkind)

// inline_for_extraction
unfold
let weaken (k1: parser_kind) (#k2: parser_kind) (#t: Type0) (p2: parser k2 t) : Pure (parser k1 t)
  (requires (k1 `is_weaker_than` k2))
  (ensures (fun _ -> True))
= let p : bare_parser t = p2 in
  p

// inline_for_extraction
unfold
let strengthen (k: parser_kind) (#t: Type0) (f: bare_parser t) : Pure (parser k t)
  (requires (parser_kind_prop k f))
  (ensures (fun _ -> True))
= f

let glb
  (k1 k2: parser_kind)
: Pure parser_kind
  (requires True)
  (ensures (fun k ->
    k `is_weaker_than` k1 /\
    k `is_weaker_than` k2 /\
    (forall k' . (k' `is_weaker_than` k1 /\ k' `is_weaker_than` k2) ==> k' `is_weaker_than` k)
  ))
= {
    parser_kind_low = (if k1.parser_kind_low < k2.parser_kind_low then k1.parser_kind_low else k2.parser_kind_low);
    parser_kind_high = (
      if Some? k1.parser_kind_high && Some? k2.parser_kind_high
      then if Some?.v k2.parser_kind_high < Some?.v k1.parser_kind_high
	   then k1.parser_kind_high
	   else k2.parser_kind_high
      else None
    );
    parser_kind_total = k1.parser_kind_total && k2.parser_kind_total;
    parser_kind_subkind = if k1.parser_kind_subkind = k2.parser_kind_subkind then k1.parser_kind_subkind else None
  }

let default_parser_kind : (x: parser_kind {
  forall (t: Type0) (p: bare_parser t) .
  (no_lookahead_weak p /\ injective p) ==> parser_kind_prop x p
})
= {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_total = false;
    parser_kind_subkind = None;
  }

#set-options "--max_fuel 8 --max_ifuel 8"

module L = FStar.List.Tot

let rec glb_list_of
  (#t: eqtype)
  (f: (t -> Tot parser_kind))
  (l: list t)
: Pure parser_kind
  (requires True)
  (ensures (fun k ->
    (forall kl . L.mem kl l ==> k `is_weaker_than` (f kl)) /\
    (forall k' . (Cons? l /\ (forall kl . L.mem kl l ==> k' `is_weaker_than` (f kl))) ==> k' `is_weaker_than` k)
  ))
= match l with
  | [] -> default_parser_kind
  | [k] -> f k
  | k1 :: q ->
    let k' = glb_list_of f q in
    glb (f k1) k'

#reset-options

let glb_list
  (l: list parser_kind)
: Pure parser_kind
  (requires True)
  (ensures (fun k ->
    (forall kl . L.mem kl l ==> k `is_weaker_than` kl) /\
    (forall k' . (Cons? l /\ (forall kl . L.mem kl l ==> k' `is_weaker_than` kl)) ==> k' `is_weaker_than` k)
  ))
= glb_list_of id l

(* Coercions *)

unfold
let coerce
  (t2: Type)
  (#t1: Type)
  (x: t1)
: Pure t2
  (requires (t1 == t2))
  (ensures (fun _ -> True))
= (x <: t2)

unfold
let coerce_parser
  (t2: Type0)
  (#k: parser_kind)
  (#t1: Type0)
  (p: parser k t1)
: Pure (parser k t2)
  (requires (t2 == t1))
  (ensures (fun _ -> True))
= p

(* Pure serializers *)

let bare_serializer
  (t: Type0)
: Tot Type0
= t -> Tot bytes

let serializer_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (f: bare_serializer t)
: GTot Type0
= forall (x: t) . parse p (f x) == Some (x, Seq.length (f x))

let serializer_correct_ext
  (#k1: parser_kind)
  (#t: Type0)
  (p1: parser k1 t)
  (f: bare_serializer t)
  (#k2: parser_kind)
  (p2: parser k2 t)
: Lemma
  (requires (forall (input: bytes) . parse p1 input == parse p2 input))
  (ensures (serializer_correct p1 f <==> serializer_correct p2 f))
= ()

let serializer_complete
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (f: bare_serializer t)
: GTot Type0
= forall (s: bytes) .
  Some? (parse p s) ==> (
    let (Some (x, len)) = parse p s in
    f x == Seq.slice s 0 len
  )

let serializer_correct_implies_complete
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (f: bare_serializer t)
: Lemma
  (requires (serializer_correct p f))
  (ensures (serializer_complete p f))
= let prf
    (s: bytes)
  : Lemma
    (requires (Some? (parse p s)))
    (ensures (
      Some? (parse p s) /\ (
      let (Some (x, len)) = parse p s in
      f x == Seq.slice s 0 len
    )))
  = let (Some (x, len)) = parse p s in
    assert (no_lookahead_weak_on p (f x) s);
    assert (injective_precond p (f x) s);
    assert (injective_postcond p (f x) s)
  in
  Classical.forall_intro (Classical.move_requires prf)

let serializer
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (f: bare_serializer t { serializer_correct p f } )

let serialize_ext
  (#k1: parser_kind)
  (#t: Type0)
  (p1: parser k1 t)
  (s1: serializer p1)
  (#k2: parser_kind)
  (p2: parser k2 t)
: Pure (serializer p2)
  (requires (forall (input: bytes) . parse p1 input == parse p2 input))
  (ensures (fun _ -> True))
= serializer_correct_ext p1 s1 p2;
  (s1 <: bare_serializer t)

let serialize
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
: Tot bytes
= s x

let serializer_unique
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s1 s2: serializer p)
  (x: t)
: Lemma
  (s1 x == s2 x)
= serializer_correct_implies_complete p s2

let serializer_injective
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
  (x1 x2: t)
: Lemma
  (requires (s x1 == s x2))
  (ensures (x1 == x2))
= ()

let serializer_parser_unique'
  (#k1: parser_kind)
  (#t: Type0)
  (p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (s: bare_serializer t)
  (x: bytes)
: Lemma
  (requires (
    k2.parser_kind_subkind == Some ParserStrong /\
    serializer_correct p1 s /\
    serializer_correct p2 s /\
    Some? (p1 x)
  ))
  (ensures (
    p1 x == p2 x
  ))
= serializer_correct_implies_complete p1 s;
  let (Some (y, len)) = p1 x in
  let x' = Seq.slice x 0 len in
  assert (s y == x');
  let len' = Seq.length x' in
  assert (len == len');
  assert (p1 x' == Some (y, len'));
  assert (p2 x' == Some (y, len'));
  assert (no_lookahead_on p2 x' x);
  assert (no_lookahead_on_postcond p2 x' x);
  assert (injective_postcond p2 x' x)

let serializer_parser_unique
  (#k1: parser_kind)
  (#t: Type0)
  (p1: parser k1 t)
  (#k2: parser_kind)
  (p2: parser k2 t)
  (s: bare_serializer t)
  (x: bytes)
: Lemma
  (requires (
    k1.parser_kind_subkind == Some ParserStrong /\
    k2.parser_kind_subkind == Some ParserStrong /\
    serializer_correct p1 s /\
    serializer_correct p2 s
  ))
  (ensures (
    p1 x == p2 x
  ))
= if Some? (p1 x)
  then serializer_parser_unique' p1 p2 s x
  else if Some? (p2 x)
  then serializer_parser_unique' p2 p1 s x
  else ()
