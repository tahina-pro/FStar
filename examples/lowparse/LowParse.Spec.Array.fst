module LowParse.Spec.Array
include LowParse.Spec.FLBytes
include LowParse.Spec.Seq

module Seq = FStar.Seq
module PL = LowParse.Spec.List

type array (t: Type) (n: nat) = (s: Seq.seq t { Seq.length s == n } )

let array_type_of_parser_kind_precond (elem_byte_size: nat) (array_byte_size: nat) : GTot bool =
  elem_byte_size > 0 &&
  array_byte_size % elem_byte_size = 0

let array_type_of_parser
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size: nat)
: Pure Type0
  (requires (
    array_type_of_parser_kind_precond elem_byte_size array_byte_size
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
    array_type_of_parser_kind_precond elem_byte_size array_byte_size /\
    Some? (parse (parse_flbytes (parse_seq p) array_byte_size) b)
  ))
  (ensures (
    array_type_of_parser_kind_precond elem_byte_size array_byte_size /\ (
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
  (precond: squash (array_type_of_parser_kind_precond elem_byte_size array_byte_size))
: Tot (bare_parser (array_type_of_parser p array_byte_size))
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
  (precond: squash (array_type_of_parser_kind_precond elem_byte_size array_byte_size))
: Lemma
  (injective (parse_array' p array_byte_size precond))
= let p' : bare_parser (array_type_of_parser p array_byte_size) = parse_array' p array_byte_size precond in
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
    array_type_of_parser_kind_precond elem_byte_size array_byte_size /\
    Seq.length b % elem_byte_size == 0
  ))
  (ensures (
    Some? (parse (PL.parse_list p) b)
  ))
  (decreases (Seq.length b))

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
    assume (Some? (parse (PL.parse_list p) b))
  end

val parse_total_constant_size_elem_parse_array_total'
  (#elem_byte_size: nat)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size ConstantSizeTotal)) t)
  (array_byte_size: nat)
  (precond: squash (array_type_of_parser_kind_precond elem_byte_size array_byte_size))
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
  (precond: squash (array_type_of_parser_kind_precond elem_byte_size array_byte_size))
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

let parse_array
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (array_byte_size: nat)
  (precond: squash (array_type_of_parser_kind_precond elem_byte_size array_byte_size))
: Tot (parser (ParserStrong (StrongConstantSize array_byte_size k)) (array_type_of_parser p array_byte_size))
= parse_array_injective p array_byte_size precond;
  parse_total_constant_size_elem_parse_array_total p array_byte_size precond;
  parse_array' p array_byte_size precond
