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
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size: nat)
: GTot bool
= let elem_byte_size : nat = get_constant_size_parser_size p in
  elem_byte_size > 0 &&
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

let array_type_of_parser
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size: nat)
: Pure Type0
  (requires (
    array_type_of_parser_kind_precond p array_byte_size // == true
  ))
  (ensures (fun _ -> True))
= let elem_byte_size : pos = get_constant_size_parser_size p in
  array t (array_byte_size / elem_byte_size)

let parse_array_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size: nat)
  (u' : unit {array_type_of_parser_kind_precond p array_byte_size == true})
  (b: bytes)
  (consumed: consumed_length b)
  (data: Seq.seq t)
: Lemma
  (requires (parse (parse_flbytes (parse_seq p) array_byte_size) b == Some (data, consumed)))
  (ensures (array_pred #t (array_byte_size / get_constant_size_parser_size p) data))
= assert (consumed == array_byte_size);
  let b' = Seq.slice b 0 consumed in
  seq_length_constant_size_parser_correct p b';
  FStar.Math.Lemmas.multiple_division_lemma (Seq.length data) (get_constant_size_parser_size p);
  ()

#set-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8"

let parse_array'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size: nat)
  (precond: unit {array_type_of_parser_kind_precond p array_byte_size == true})
: Tot (parser (ParserStrong (StrongParserKind (StrongConstantSize array_byte_size ConstantSizeUnknown) (array_byte_size > 0) ())) (array_type_of_parser p array_byte_size))
= let elem_byte_size = get_constant_size_parser_size p in
  assert (elem_byte_size > 0);
  let elem_byte_size : pos = elem_byte_size in
  assert_norm (array_type_of_parser p array_byte_size == (x: Seq.seq t { array_pred (array_byte_size / elem_byte_size) x}));
  let p' = parse_strengthen (parse_flbytes (parse_seq p) array_byte_size) (array_pred (array_byte_size / elem_byte_size)) (parse_array_correct p array_byte_size precond) in
  coerce_parser (array_type_of_parser p array_byte_size) p'

#reset-options

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
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (b: bytes)
: Lemma
  (requires (
    let elem_byte_size = get_constant_size_parser_size p in
    ConstantSizeTotal? (get_constant_size_parser_kind p) /\
    elem_byte_size > 0 /\
    Seq.length b % elem_byte_size == 0
  ))
  (ensures (
    Some? (parse (PL.parse_list p) b)
  ))
  (decreases (Seq.length b))

#set-options "--z3rlimit 32"

let rec parse_total_constant_size_elem_parse_list_total #k #t p b =
  let elem_byte_size = get_constant_size_parser_size p in
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
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size: nat)
  (precond: unit {array_type_of_parser_kind_precond p array_byte_size == true})
  (b: bytes)
: Lemma
  (requires (
    ConstantSizeTotal? (get_constant_size_parser_kind p) /\
    Seq.length b >= array_byte_size
  ))
  (ensures (
    Some? (parse (parse_array' p array_byte_size precond) b)
  ))

#set-options "--z3rlimit 16"

let parse_total_constant_size_elem_parse_array_total' #k #t p array_byte_size precond b =
  let b' = Seq.slice b 0 array_byte_size in
  parse_total_constant_size_elem_parse_list_total p b';
  parse_seq_correct p b'

#reset-options

#set-options "--z3rlimit 32"

let parse_total_constant_size_elem_parse_array_total
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size: nat)
  (precond: unit {array_type_of_parser_kind_precond p array_byte_size == true})
: Lemma
  (ensures (
    ConstantSizeTotal? (get_constant_size_parser_kind p) ==>
    is_total_constant_size_parser array_byte_size (parse_array' p array_byte_size precond)
  ))
= let k = get_constant_size_parser_kind p in
  let elem_byte_size = get_constant_size_parser_size p in
  if ConstantSizeTotal? k
  then
    Classical.forall_intro (Classical.move_requires (parse_total_constant_size_elem_parse_array_total' p array_byte_size precond))
  else ()

#reset-options

let parse_array_prop
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k })
  (array_byte_size: nat)
  (precond: unit { array_type_of_parser_kind_precond p array_byte_size } )
: Lemma
  (parser_kind_prop (ParserStrong (StrongParserKind (StrongConstantSize (array_byte_size) (get_constant_size_parser_kind p)) (array_byte_size > 0) ())) (parse_array' p (array_byte_size) precond))
= parse_total_constant_size_elem_parse_array_total p array_byte_size precond

let parse_array
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size: U32.t)
  (precond: unit { array_type_of_parser_kind_precond p (U32.v array_byte_size) == true } )
: Tot (parser (ParserStrong (StrongParserKind (StrongConstantSize (U32.v array_byte_size) (get_constant_size_parser_kind p)) (U32.v array_byte_size > 0) ())) (array_type_of_parser p (U32.v array_byte_size)))
= parse_array_prop p (U32.v array_byte_size) precond ;
  strengthen (ParserStrong (StrongParserKind (StrongConstantSize (U32.v array_byte_size) (get_constant_size_parser_kind p)) (U32.v array_byte_size > 0) ())) (parse_array' p (U32.v array_byte_size) precond)


include LowParse.Spec.VLBytes

let vlarray_pred (#t: Type) (min max: nat) (s: Seq.seq t) : GTot Type0 =
    let l = Seq.length s in
    min <= l /\ l <= max

type vlarray (t: Type) (min max: nat) =
  (s: Seq.seq t {vlarray_pred min max s})

let vlarray_type_of_parser_kind_precond'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t {kind_is_constant_size k} )
  (array_byte_size_min array_byte_size_max: nat) : GTot bool =
  let elem_byte_size = get_constant_size_parser_size p in
  elem_byte_size > 0 &&
  array_byte_size_min % elem_byte_size = 0 &&
  array_byte_size_max % elem_byte_size = 0 &&
  array_byte_size_max > 0 &&
  array_byte_size_max < 4294967296 // pow2 32

let vlarray_type_of_parser_kind_precond'_pow2_32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t {kind_is_constant_size k} )
  (array_byte_size_min array_byte_size_max: nat)
: Lemma
  (requires (vlarray_type_of_parser_kind_precond' p array_byte_size_min array_byte_size_max))
  (ensures (array_byte_size_max < pow2 32))
  [SMTPat (vlarray_type_of_parser_kind_precond' p array_byte_size_min array_byte_size_max)]
= ()

let vlarray_type_of_parser_kind_precond
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size_min array_byte_size_max: nat) : GTot bool =
  vlarray_type_of_parser_kind_precond' p (array_byte_size_min) (array_byte_size_max)

val vlarray_type_of_parser
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size_min array_byte_size_max: nat)
: Pure Type0
  (requires (
    vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max
  ))
  (ensures (fun _ -> True))
  
let vlarray_type_of_parser #k #t p array_byte_size_min array_byte_size_max =
  let elem_byte_size = get_constant_size_parser_size p in
  let elem_byte_size : pos = elem_byte_size in
  let min : nat = array_byte_size_min / elem_byte_size in
  let max : nat = array_byte_size_max / elem_byte_size in
  vlarray t min max

val parse_vlarray_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size_min array_byte_size_max: nat)
  (u: unit { vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max == true })
  (b: bytes)
  (consumed: consumed_length b)
  (data: Seq.seq t)
: Lemma
  (requires (
    parse (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p)) b == Some (data, consumed)
  ))
  (ensures (
    let elem_byte_size = get_constant_size_parser_size p in
    vlarray_pred (array_byte_size_min / elem_byte_size) (array_byte_size_max / elem_byte_size) data
  ))

// #set-options "--z3rlimit 1024"

let parse_vlarray_correct #k #t p array_byte_size_min array_byte_size_max u b consumed data =
  let elem_byte_size = get_constant_size_parser_size p in
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
  assume (vlarray_pred (array_byte_size_min / elem_byte_size) (array_byte_size_max / elem_byte_size) data)

#reset-options

let parse_vlarray
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t { kind_is_constant_size k } )
  (array_byte_size_min array_byte_size_max: nat)
  (precond: unit {vlarray_type_of_parser_kind_precond p array_byte_size_min array_byte_size_max == true})
: Tot (parser (ParserStrong (StrongParserKind StrongUnknown true ())) (vlarray_type_of_parser p array_byte_size_min array_byte_size_max))
= let elem_byte_size = get_constant_size_parser_size p in
  parse_strengthen
    (parse_bounded_vlbytes array_byte_size_min array_byte_size_max (parse_seq p))
    (vlarray_pred (array_byte_size_min / elem_byte_size) (array_byte_size_max / elem_byte_size))
    (parse_vlarray_correct p array_byte_size_min array_byte_size_max precond)
