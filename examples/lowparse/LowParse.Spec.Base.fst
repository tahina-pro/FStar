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

(** Parsing data of constant size *)

let is_constant_size_parser
  (sz: nat)
  (#t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes) .
  Some? (f s) ==> (
    let (_, consumed) = Some?.v (f s) in
    sz == (consumed <: nat)
  )

let is_total_constant_size_parser
  (sz: nat)
  (#t: Type0)
  (f: bare_parser t)
: GTot Type0
= forall (s: bytes) . {:pattern (f s) }
  (Seq.length s < sz) == (None? (f s))

(* Type hierarchy *)

type constant_size_parser_kind =
  | ConstantSizeTotal
  | ConstantSizeUnknown

let constant_size_parser_kind_prop (k: constant_size_parser_kind) (sz: nat) (#t: Type0) (f: bare_parser t) : GTot Type0 =
  match k with
  | ConstantSizeTotal -> is_total_constant_size_parser sz f
  | _ -> True

type strong_parser_kind =
  | StrongConstantSize: (sz: nat) -> (k: constant_size_parser_kind) -> strong_parser_kind
  | StrongUnknown

let strong_parser_kind_prop (k: strong_parser_kind) (#t: Type0) (f: bare_parser t) : GTot Type0 =
  match k with
  | StrongConstantSize sz k' ->
    is_constant_size_parser sz f /\
    constant_size_parser_kind_prop k' sz f
  | _ -> True

type parser_kind =
  | ParserStrong: (k' : strong_parser_kind) -> parser_kind
  | ParserConsumesAll
  | ParserUnknown

let parser_kind_prop (k: parser_kind) (#t: Type0) (f: bare_parser t) : GTot Type0 =
  match k with
  | ParserStrong k' ->
    no_lookahead f /\
    strong_parser_kind_prop k' f
  | ParserConsumesAll ->
    consumes_all f
  | _ -> True

let parser
  (k: parser_kind)
  (t: Type0)
: Tot Type0
= (f: bare_parser t { no_lookahead_weak f /\ injective f /\ parser_kind_prop k f } )

let is_weaker_than
  (k1 k2: parser_kind)
: GTot Type0
= match k1 with
  | ParserUnknown -> True
  | ParserConsumesAll -> k2 == ParserConsumesAll
  | ParserStrong k1s ->
    begin match k2 with
    | ParserStrong k2s ->
      begin match k1s with
      | StrongUnknown -> True
      | StrongConstantSize sz1 k1c ->
	begin match k2s with
	| StrongConstantSize sz2 k2c ->
	  sz1 == sz2 /\
	  begin match k1c with
	  | ConstantSizeUnknown -> True
	  | ConstantSizeTotal -> k2c == ConstantSizeTotal
	  end
	| _ -> False
	end
      end
    | _ -> False
    end

inline_for_extraction
let weaken (k1: parser_kind) (#k2: parser_kind) (#t: Type0) (p2: parser k2 t) : Pure (parser k1 t)
  (requires (k1 `is_weaker_than` k2))
  (ensures (fun _ -> True))
= let p : bare_parser t = p2 in
  p

inline_for_extraction
let strengthen (k: parser_kind) (#t: Type0) (f: bare_parser t) : Pure (parser k t)
  (requires (no_lookahead_weak f /\ injective f /\ parser_kind_prop k f))
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
= match k1 with
  | ParserStrong k1s ->
    begin match k2 with
    | ParserStrong k2s -> ParserStrong
      begin match k1s with
      | StrongConstantSize sz1 k1c ->
	begin match k2s with
	| StrongConstantSize sz2 k2c ->
	  if sz1 = sz2
	  then StrongConstantSize sz1
	    begin match k1c with
	    | ConstantSizeTotal -> k2c
	    | _ -> ConstantSizeUnknown
	    end
	  else StrongUnknown
	| _ -> StrongUnknown
	end
      | _ -> StrongUnknown
      end
    | _ -> ParserUnknown
    end
  | ParserConsumesAll ->
    begin match k2 with
    | ParserConsumesAll -> ParserConsumesAll
    | _ -> ParserUnknown
    end
  | _ -> ParserUnknown

module L = FStar.List.Tot

#set-options "--max_fuel 8 --max_ifuel 8"

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
  | [] -> ParserUnknown
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
