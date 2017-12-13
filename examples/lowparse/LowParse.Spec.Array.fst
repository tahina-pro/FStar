module LowParse.Spec.Array
include LowParse.Spec.FLBytes
include LowParse.Spec.Seq

module Seq = FStar.Seq
module PL = LowParse.Spec.List

module U32 = FStar.UInt32

type array (t: Type) (n: nat) = (s: Seq.seq t { Seq.length s == n } )

let array_type_of_parser_kind_precond
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size: nat)
: GTot bool
= elem_byte_size > 0 &&
  array_byte_size % elem_byte_size = 0

let array_type_of_parser'
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size: nat)
: Pure Type0
  (requires (
    array_type_of_parser_kind_precond p array_byte_size
  ))
  (ensures (fun _ -> True))
= array t (array_byte_size / elem_byte_size)

val parse_array_correct
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size: nat)
  (b: bytes32)
: Lemma
  (requires (
    array_type_of_parser_kind_precond p array_byte_size /\
    Some? (parse (parse_flbytes (parse_seq p) array_byte_size) b)
  ))
  (ensures (
    array_type_of_parser_kind_precond p array_byte_size /\ (
    let pb = parse (parse_flbytes (parse_seq p) array_byte_size) b in
    Some? pb /\ (
    let (Some (data, _)) = pb in
    Seq.length data == array_byte_size / elem_byte_size
  ))))

let parse_array_correct #elem_byte_size #k #t p array_byte_size b =
  let (Some (data, consumed)) = parse (parse_flbytes (parse_seq p) array_byte_size) b in
  assert (consumed == array_byte_size);
  let b' = Seq.slice b 0 consumed in
  seq_length_constant_size_parser_correct p b';
  FStar.Math.Lemmas.multiple_division_lemma (Seq.length data) elem_byte_size

let parse_array'
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size: nat)
  (precond: squash (array_type_of_parser_kind_precond p array_byte_size))
: Tot (bare_parser (array_type_of_parser' p array_byte_size))
= fun (b: bytes32) ->
  match parse (parse_flbytes (parse_seq p) array_byte_size) b with
  | None -> None
  | Some (data, consumed) ->
    parse_array_correct p array_byte_size b;
    let data' : array t (array_byte_size / elem_byte_size) = data in
    Some (data' , consumed)

let parse_array_injective
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size: nat)
  (precond: squash (array_type_of_parser_kind_precond p array_byte_size))
: Lemma
  (injective (parse_array' p array_byte_size precond))
= let p' : bare_parser (array_type_of_parser' p array_byte_size) = parse_array' p array_byte_size precond in
  let prf
    (b1 b2: bytes32)
  : Lemma
    (requires (injective_precond p' b1 b2))
    (ensures (injective_postcond p' b1 b2))
  = assert (injective_postcond (parse_flbytes (parse_seq p) array_byte_size) b1 b2)
  in
  let prf'
    (b1 b2: bytes32)
  : Lemma
    (injective_precond p' b1 b2 ==> injective_postcond p' b1 b2)
  = Classical.move_requires (prf b1) b2
  in
  Classical.forall_intro_2 prf'

val parse_total_constant_size_elem_parse_list_total
  (#elem_byte_size: nat)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size ConstantSizeTotal)) t)
  (array_byte_size: nat)
  (b: bytes32)
: Lemma
  (requires (
    array_type_of_parser_kind_precond p array_byte_size /\
    Seq.length b % elem_byte_size == 0
  ))
  (ensures (
    Some? (parse (PL.parse_list p) b)
  ))
  (decreases (Seq.length b))

#set-options "--z3rlimit 128"

let rec parse_total_constant_size_elem_parse_list_total #elem_byte_size #t p array_byte_size b =
  if Seq.length b = 0
  then ()
  else begin
    assert (Seq.length b >= elem_byte_size);
    let pe = parse p b in
    assert (Some? pe);
    let (Some (_, consumed)) = pe in
    assert ((consumed <: nat) == elem_byte_size);
    let b' = Seq.slice b consumed (Seq.length b) in
    FStar.Math.Lemmas.lemma_mod_plus (Seq.length b') 1 elem_byte_size;
    parse_total_constant_size_elem_parse_list_total p array_byte_size b' ;    
    assert (Some? (parse (PL.parse_list p) b))
  end

#reset-options

val parse_total_constant_size_elem_parse_array_total'
  (#elem_byte_size: nat)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size ConstantSizeTotal)) t)
  (array_byte_size: nat)
  (precond: squash (array_type_of_parser_kind_precond p array_byte_size))
  (b: bytes32)
: Lemma
  (requires (
    Seq.length b >= array_byte_size
  ))
  (ensures (
    Some? (parse (parse_array' p array_byte_size precond) b)
  ))

let parse_total_constant_size_elem_parse_array_total' #elem_byte_size #t p array_byte_size precond b =
  let b' = Seq.slice b 0 array_byte_size in
  parse_total_constant_size_elem_parse_list_total p array_byte_size b';
  parse_seq_correct p b'

let parse_total_constant_size_elem_parse_array_total
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size: nat)
  (precond: squash (array_type_of_parser_kind_precond p array_byte_size))
: Lemma
  (ensures (
    ConstantSizeTotal? k ==> (forall (b: bytes32) .
    Seq.length b >= array_byte_size ==>
    Some? (parse (parse_array' p array_byte_size precond) b)
  )))
= if ConstantSizeTotal? k
  then
    let p' : parser (ParserStrong (StrongConstantSize elem_byte_size ConstantSizeTotal)) t = p in
    Classical.forall_intro (Classical.move_requires (parse_total_constant_size_elem_parse_array_total' p' array_byte_size ()))
  else ()

abstract
let parse_array_precond
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size: U32.t)
: Tot Type0
= unit -> Lemma
  (array_type_of_parser_kind_precond p (U32.v array_byte_size))

abstract
let parse_array_precond_intro
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size: U32.t)
  (x: (
    unit -> Lemma
    (array_type_of_parser_kind_precond p (U32.v array_byte_size))
  ))
: Tot (parse_array_precond p array_byte_size)
= x

abstract
let parse_array_precond_elim
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (#array_byte_size: U32.t)
  (x: parse_array_precond p array_byte_size)
: Lemma
  (array_type_of_parser_kind_precond p (U32.v array_byte_size))
= x ()

let array_type_of_parser
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (#array_byte_size: U32.t)
  (precond: parse_array_precond p array_byte_size)
: Tot Type0
= parse_array_precond_elim precond;
  array_type_of_parser' p (U32.v array_byte_size)

#set-options "--z3rlimit 32"

let parse_array
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (#array_byte_size: U32.t)
  (precond: parse_array_precond p array_byte_size)
: Tot (parser (ParserStrong (StrongConstantSize (U32.v array_byte_size) k)) (array_type_of_parser precond))
= parse_array_precond_elim precond;
  parse_array_injective p (U32.v array_byte_size) ();
  parse_total_constant_size_elem_parse_array_total p (U32.v array_byte_size) ();
  parse_array' p (U32.v array_byte_size) ()

#reset-options

include LowParse.Spec.VLBytes

type vlarray (t: Type) (min max: nat) =
  (s: Seq.seq t {
    let l = Seq.length s in
    min <= l /\ l <= max
  })

let vlarray_type_of_parser_kind_precond'
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size_min array_byte_size_max: nat) : GTot bool =
  elem_byte_size > 0 &&
  array_byte_size_min % elem_byte_size = 0 &&
  array_byte_size_max % elem_byte_size = 0 &&
  array_byte_size_max > 0

let vlarray_type_of_parser_kind_precond
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size_min array_byte_size_max: U32.t) : GTot bool =
  vlarray_type_of_parser_kind_precond' p (U32.v array_byte_size_min) (U32.v array_byte_size_max)

let vlarray_type_of_parser'
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
: Pure Type0
  (requires (
    vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max
  ))
  (ensures (fun _ -> True))
= vlarray t (U32.v array_byte_size_min / elem_byte_size) (U32.v array_byte_size_max / elem_byte_size)

val parse_vlarray_correct
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
  (b: bytes32)
: Lemma
  (requires (
    vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max /\
    Some? (parse (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p)) b)
  ))
  (ensures (
    vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max /\ (
    let pb = parse (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p)) b in
    Some? pb /\ (
    let (Some (data, _)) = pb in
    let l = Seq.length data in
    U32.v array_byte_size_min / elem_byte_size <= l /\
    l <= U32.v array_byte_size_max / elem_byte_size
  ))))

#set-options "--z3rlimit 256"

let parse_vlarray_correct #elem_byte_size #k #t p array_byte_size_min array_byte_size_max b =
  let (Some (data, consumed)) = parse (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p)) b in
  let sz : integer_size = log256 array_byte_size_max in
  assert (consumed >= sz);
  let b' : bytes32 = Seq.slice b sz consumed in
  assert (b' == Seq.slice (Seq.slice b sz (Seq.length b)) 0 (consumed - sz));
  let (Some (data', consumed')) = parse (parse_seq p) b' in
  assert (data == data');
  assert ((consumed' <: nat) == consumed - sz);
  seq_length_constant_size_parser_correct p b';
  FStar.Math.Lemmas.multiple_division_lemma (Seq.length data) elem_byte_size;
  FStar.Math.Lemmas.lemma_div_le (U32.v array_byte_size_min) consumed' elem_byte_size ;
  FStar.Math.Lemmas.lemma_div_le consumed' (U32.v array_byte_size_max) elem_byte_size

#reset-options

#set-options "--z3rlimit 64"

let parse_vlarray'
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
  (precond: squash (vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max))
: Tot (bare_parser (vlarray_type_of_parser' p array_byte_size_min array_byte_size_max))
= fun (b: bytes32) ->
  match parse (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p)) b with
  | None -> None
  | Some (data, consumed) ->
    parse_vlarray_correct p array_byte_size_min array_byte_size_max b;
    let data' : vlarray t (U32.v array_byte_size_min / elem_byte_size) (U32.v array_byte_size_max / elem_byte_size) = data in
    Some (data' , consumed)

#reset-options

let parse_vlarray_injective
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
  (precond: squash (vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max))
: Lemma
  (injective (parse_vlarray' p array_byte_size_min array_byte_size_max precond))
= let p' : bare_parser (vlarray_type_of_parser' p array_byte_size_min array_byte_size_max) = parse_vlarray' p array_byte_size_min array_byte_size_max precond in
  let prf
    (b1 b2: bytes32)
  : Lemma
    (requires (injective_precond p' b1 b2))
    (ensures (injective_postcond p' b1 b2))
  = assert (injective_postcond (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p)) b1 b2)
  in
  let prf'
    (b1 b2: bytes32)
  : Lemma
    (injective_precond p' b1 b2 ==> injective_postcond p' b1 b2)
  = Classical.move_requires (prf b1) b2
  in
  Classical.forall_intro_2 prf'

#set-options "--z3rlimit 32"

let parse_vlarray_no_lookahead
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
  (precond: squash (vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max))
: Lemma
  (no_lookahead (parse_vlarray' p array_byte_size_min array_byte_size_max precond))
= let p' : bare_parser (vlarray_type_of_parser' p array_byte_size_min array_byte_size_max) = parse_vlarray' p array_byte_size_min array_byte_size_max precond in
  let prf
    (b1 b2: bytes32)
  : Lemma
    (requires (no_lookahead_on_precond p' b1 b2))
    (ensures (no_lookahead_on_postcond p' b1 b2))
  = assert (no_lookahead_on (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p)) b1 b2)
  in
  let prf'
    (b1 b2: bytes32)
  : Lemma
    (no_lookahead_on p' b1 b2)
  = Classical.move_requires (prf b1) b2
  in
  Classical.forall_intro_2 prf'

let parse_vlarray_no_lookahead_weak
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
  (precond: squash (vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max))
: Lemma
  (no_lookahead_weak (parse_vlarray' p array_byte_size_min array_byte_size_max precond))
= let p' : bare_parser (vlarray_type_of_parser' p array_byte_size_min array_byte_size_max) = parse_vlarray' p array_byte_size_min array_byte_size_max precond in
  let prf
    (b1 b2: bytes32)
  : Lemma
    (no_lookahead_weak_on p' b1 b2)
  = assert (no_lookahead_weak_on (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p)) b1 b2)
  in
  Classical.forall_intro_2 prf

abstract
let parse_vlarray_precond
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
: Tot Type0
= unit -> Lemma
  (vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max)

abstract
let parse_vlarray_precond_intro
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
  (x: (unit -> Lemma
    (vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max)
  ))
: Tot (parse_vlarray_precond p array_byte_size_min array_byte_size_max)
= x

abstract
let parse_vlarray_precond_elim
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (#array_byte_size_min #array_byte_size_max: U32.t)
  (x: parse_vlarray_precond p array_byte_size_min array_byte_size_max)
: Lemma
  (vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max)
= x ()

let vlarray_type_of_parser
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (#array_byte_size_min #array_byte_size_max: U32.t)
  (precond: parse_vlarray_precond p array_byte_size_min array_byte_size_max)
: Tot Type0
= parse_vlarray_precond_elim precond;
  vlarray_type_of_parser' p array_byte_size_min array_byte_size_max

let parse_vlarray
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (#array_byte_size_min #array_byte_size_max: U32.t)
  (precond: parse_vlarray_precond p array_byte_size_min array_byte_size_max)
: Tot (parser (ParserStrong StrongUnknown) (vlarray_type_of_parser precond))
= parse_vlarray_precond_elim precond;
  parse_vlarray_injective p array_byte_size_min array_byte_size_max ();
  parse_vlarray_no_lookahead_weak p array_byte_size_min array_byte_size_max ();
  parse_vlarray_no_lookahead p array_byte_size_min array_byte_size_max ();
  parse_vlarray' p array_byte_size_min array_byte_size_max ()
