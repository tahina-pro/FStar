module LowParse.Spec.Array
include LowParse.Spec.FLBytes
include LowParse.Spec.Seq

module Seq = FStar.Seq
module PL = LowParse.Spec.List

module U32 = FStar.UInt32

let array_pred (#t: Type) (n: nat) (s: Seq.seq t) : GTot Type0 =
  Seq.length s == n

type array (t: Type) (n: nat) = (s: Seq.seq t { array_pred n s } )

let array_type_of_parser_kind_precond
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size: nat)
: GTot bool
= elem_byte_size > 0 &&
  array_byte_size % elem_byte_size = 0

(* TODO: move to FStar.Math.Lemmas *)

#set-options "--z3rlimit 64"

let div_nonneg
  (x: nat)
  (y: pos)
: Lemma
  (0 <= x / y)
  [SMTPat (x / y)]
= ()

#reset-options

let array_type_of_parser'
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size: nat)
: Pure Type0
  (requires (
    array_type_of_parser_kind_precond p array_byte_size == true
  ))
  (ensures (fun _ -> True))
= array t (array_byte_size / elem_byte_size)

let parse_array_correct
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size: nat)
  (u' : unit {array_type_of_parser_kind_precond p array_byte_size == true})
  (b: bytes)
  (consumed: consumed_length b)
  (data: Seq.seq t)
: Lemma
  (requires (parse (parse_flbytes (parse_seq p) array_byte_size) b == Some (data, consumed)))
  (ensures (array_pred #t (array_byte_size / elem_byte_size) data))
= assert (consumed == array_byte_size);
  let b' = Seq.slice b 0 consumed in
  seq_length_constant_size_parser_correct p b';
  FStar.Math.Lemmas.multiple_division_lemma (Seq.length data) elem_byte_size;
  ()

let parse_array'
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size: nat)
  (precond: unit {array_type_of_parser_kind_precond p array_byte_size == true})
: Tot (parser (ParserStrong (StrongParserKind (StrongConstantSize array_byte_size ConstantSizeUnknown) (array_byte_size > 0) ())) (array_type_of_parser' p array_byte_size))
= assert_norm (array_type_of_parser' p array_byte_size == (x: Seq.seq t { array_pred (array_byte_size / elem_byte_size) x}));
  coerce
    (parser (ParserStrong (StrongParserKind (StrongConstantSize array_byte_size ConstantSizeUnknown) (array_byte_size > 0) ())) (array_type_of_parser' p array_byte_size))
    (parse_strengthen (parse_flbytes (parse_seq p) array_byte_size) (array_pred (array_byte_size / elem_byte_size)) (parse_array_correct p array_byte_size precond))

(*
abstract
let parse_array_precond
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size: U32.t)
: Tot Type0
= unit -> Lemma
  (array_type_of_parser_kind_precond p (U32.v array_byte_size))

abstract
let parse_array_precond_intro
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
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
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (#p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (#array_byte_size: U32.t)
  (x: parse_array_precond p array_byte_size)
: Lemma
  (array_type_of_parser_kind_precond p (U32.v array_byte_size))
= x ()

let array_type_of_parser
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (#p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (#array_byte_size: U32.t)
  (precond: parse_array_precond p array_byte_size)
: Tot Type0
= parse_array_precond_elim precond;
  array_type_of_parser' p (U32.v array_byte_size)
*)

let mod_plus_p_r
  (a: nat)
  (p: pos)
: Lemma
  ((a + p) % p == a % p)
= FStar.Math.Lemmas.lemma_mod_plus a 1 p

let mod_plus_p_l
  (a: nat)
  (p: pos)
: Lemma
  ((p + a) % p == a % p)
= mod_plus_p_r a p

val parse_total_constant_size_elem_parse_list_total
  (#elem_byte_size: nat)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) ConstantSizeTotal) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size ConstantSizeTotal) b u)) t)
  (b: bytes)
: Lemma
  (requires (
    elem_byte_size > 0 /\
    Seq.length b % elem_byte_size == 0
  ))
  (ensures (
    Some? (parse (PL.parse_list p) b)
  ))
  (decreases (Seq.length b))

// #reset-options "--z3rlimit 128 --max_fuel 8 --max_ifuel 8 --z3cliopt smt.arith.nl=false"

#set-options "--z3rlimit 16"

let rec parse_total_constant_size_elem_parse_list_total #elem_byte_size #b #u #t p b =
  if Seq.length b = 0
  then ()
  else begin
    Classical.move_requires (FStar.Math.Lemmas.modulo_lemma (Seq.length b)) elem_byte_size;
    assert (Seq.length b >= elem_byte_size);
    let pe = parse p b in
    assert (Some? pe);
    let (Some (_, consumed)) = pe in
    assert ((consumed <: nat) == elem_byte_size);
    let b' = Seq.slice b consumed (Seq.length b) in
    assert (Seq.length b' == Seq.length b - consumed);
    mod_plus_p_l (Seq.length b') elem_byte_size;
    assert (Seq.length b == elem_byte_size + Seq.length b');
    assert (Seq.length b % elem_byte_size == Seq.length b' % elem_byte_size);
    parse_total_constant_size_elem_parse_list_total p b' ;    
    assert (Some? (parse (PL.parse_list p) b))
  end

#reset-options

val parse_total_constant_size_elem_parse_array_total'
  (#elem_byte_size: nat)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) ConstantSizeTotal) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size ConstantSizeTotal) b u)) t)
  (array_byte_size: nat)
  (precond: unit {array_type_of_parser_kind_precond p array_byte_size == true})
  (b: bytes)
: Lemma
  (requires (
    Seq.length b >= array_byte_size
  ))
  (ensures (
    Some? (parse (parse_array' p array_byte_size precond) b)
  ))

#set-options "--z3rlimit 16"

let parse_total_constant_size_elem_parse_array_total' #elem_byte_size #b #u #t p array_byte_size precond b =
  let b' = Seq.slice b 0 array_byte_size in
  parse_total_constant_size_elem_parse_list_total p b';
  parse_seq_correct p b'

#reset-options

let parse_total_constant_size_elem_parse_array_total
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size: nat)
  (precond: unit {array_type_of_parser_kind_precond p array_byte_size == true})
: Lemma
  (ensures (
    ConstantSizeTotal? k ==>
    is_total_constant_size_parser array_byte_size (parse_array' p array_byte_size precond)
  ))
= if ConstantSizeTotal? k
  then
    let p' : parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size ConstantSizeTotal) b u)) t = p in
    Classical.forall_intro (Classical.move_requires (parse_total_constant_size_elem_parse_array_total' p' array_byte_size ()))
  else ()

let parse_array_prop
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size: nat)
  (precond: unit { array_type_of_parser_kind_precond p array_byte_size } )
: Lemma
  (parser_kind_prop (ParserStrong (StrongParserKind (StrongConstantSize (array_byte_size) k) (array_byte_size > 0) ())) (parse_array' p (array_byte_size) precond))
= parse_total_constant_size_elem_parse_array_total p array_byte_size precond

let parse_array
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size: U32.t)
  (precond: unit { array_type_of_parser_kind_precond p (U32.v array_byte_size) == true } )
: Tot (parser (ParserStrong (StrongParserKind (StrongConstantSize (U32.v array_byte_size) k) (U32.v array_byte_size > 0) ())) (array_type_of_parser' p (U32.v array_byte_size)))
= parse_array_prop p (U32.v array_byte_size) precond ;
  strengthen (ParserStrong (StrongParserKind (StrongConstantSize (U32.v array_byte_size) k) (U32.v array_byte_size > 0) ())) (parse_array' p (U32.v array_byte_size) precond)


include LowParse.Spec.VLBytes

let vlarray_pred (#t: Type) (min max: nat) (s: Seq.seq t) : GTot Type0 =
    let l = Seq.length s in
    min <= l /\ l <= max

type vlarray (t: Type) (min max: nat) =
  (s: Seq.seq t {vlarray_pred min max s})

let vlarray_type_of_parser_kind_precond'
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size_min array_byte_size_max: nat) : GTot bool =
  elem_byte_size > 0 &&
  array_byte_size_min % elem_byte_size = 0 &&
  array_byte_size_max % elem_byte_size = 0 &&
  array_byte_size_max > 0

let vlarray_type_of_parser_kind_precond
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size_min array_byte_size_max: U32.t) : GTot bool =
  vlarray_type_of_parser_kind_precond' p (U32.v array_byte_size_min) (U32.v array_byte_size_max)

val vlarray_type_of_parser'
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
: Pure Type0
  (requires (
    vlarray_type_of_parser_kind_precond #elem_byte_size #k #b #u #t p array_byte_size_min array_byte_size_max
  ))
  (ensures (fun _ -> True))
  
let vlarray_type_of_parser' #elem_byte_size #k #b #u #t p array_byte_size_min array_byte_size_max =
  let min : nat = U32.v array_byte_size_min / elem_byte_size in
  let max : nat = U32.v array_byte_size_max / elem_byte_size in
  vlarray t min max

val parse_vlarray_correct
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
  (u: unit { vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max == true })
  (b: bytes)
  (consumed: consumed_length b)
  (data: Seq.seq t)
: Lemma
  (requires (
    parse (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p)) b == Some (data, consumed)
  ))
  (ensures (
    vlarray_pred (U32.v array_byte_size_min / elem_byte_size) (U32.v array_byte_size_max / elem_byte_size) data
  ))

// #set-options "--z3rlimit 1024"

let parse_vlarray_correct #elem_byte_size #k #b #u #t p array_byte_size_min array_byte_size_max u b consumed data =
(*
  let sz : integer_size = log256 array_byte_size_max in
  assume (consumed >= sz);
  let b' : bytes = Seq.slice b sz consumed in
  assert (b' == Seq.slice (Seq.slice b sz (Seq.length b)) 0 (consumed - sz));
  let (Some (data', consumed')) = parse (parse_seq p) b' in
  assert (data == data');
  assert ((consumed' <: nat) == consumed - sz);
  seq_length_constant_size_parser_correct p b';
  FStar.Math.Lemmas.multiple_division_lemma (Seq.length data) elem_byte_size;
  FStar.Math.Lemmas.lemma_div_le (U32.v array_byte_size_min) consumed' elem_byte_size ;
  FStar.Math.Lemmas.lemma_div_le consumed' (U32.v array_byte_size_max) elem_byte_size
*)
  assume (vlarray_pred (U32.v array_byte_size_min / elem_byte_size) (U32.v array_byte_size_max / elem_byte_size) data)

#reset-options

let parse_vlarray'
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
  (precond: unit {vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max == true})
: Tot (parser (ParserStrong (StrongParserKind StrongUnknown true ())) (vlarray_type_of_parser' p array_byte_size_min array_byte_size_max))
= parse_strengthen
    (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p))
    (vlarray_pred (U32.v array_byte_size_min / elem_byte_size) (U32.v array_byte_size_max / elem_byte_size))
    (parse_vlarray_correct p array_byte_size_min array_byte_size_max precond)

(*
abstract
let parse_vlarray_precond
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (array_byte_size_min array_byte_size_max: U32.t)
: Tot Type0
= unit -> Lemma
  (vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max)

abstract
let parse_vlarray_precond_intro
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
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
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (#p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (#array_byte_size_min #array_byte_size_max: U32.t)
  (x: parse_vlarray_precond p array_byte_size_min array_byte_size_max)
: Lemma
  (vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max)
= x ()

let vlarray_type_of_parser
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (#p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (#array_byte_size_min #array_byte_size_max: U32.t)
  (precond: parse_vlarray_precond p array_byte_size_min array_byte_size_max)
: Tot Type0
= parse_vlarray_precond_elim precond;
  vlarray_type_of_parser' p array_byte_size_min array_byte_size_max

let parse_vlarray
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#b: bool)
  (#u: unit { strong_parser_kind_consumes_at_least_one_byte (StrongConstantSize (elem_byte_size) k) b } )
  (#t: Type0)
  (#p: parser (ParserStrong (StrongParserKind (StrongConstantSize elem_byte_size k) b u)) t)
  (#array_byte_size_min #array_byte_size_max: U32.t)
  (precond: parse_vlarray_precond p array_byte_size_min array_byte_size_max)
: Tot (parser (ParserStrong (StrongParserKind StrongUnknown true ())) (vlarray_type_of_parser precond))
= parse_vlarray_precond_elim precond;
  parse_vlarray' p array_byte_size_min array_byte_size_max ()
