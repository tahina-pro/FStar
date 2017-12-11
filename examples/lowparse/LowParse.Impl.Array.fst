module LowParse.Impl.Array
include LowParse.Impl.FLBytes
include LowParse.Impl.Seq
include LowParse.Spec.Array

module U32 = FStar.UInt32
module S = LowParse.Slice

inline_for_extraction
val validate_array_gen
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (vs: stateful_validator p)
  (array_byte_size: U32.t)
  (precond: squash (array_type_of_parser_kind_precond elem_byte_size (U32.v array_byte_size)))
: Tot (stateful_validator (parse_array p (U32.v array_byte_size) precond))

let validate_array_gen #elem_byte_size #k #t #p vs array_byte_size precond =
  fun (s: S.bslice) -> validate_flbytes (validate_seq vs) array_byte_size s

inline_for_extraction
let validate_array
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (vs: stateful_validator p)
  (array_byte_size: U32.t)
  (precond: squash (array_type_of_parser_kind_precond elem_byte_size (U32.v array_byte_size)))
: Tot (stateful_validator (parse_array p (U32.v array_byte_size) precond))
= if ConstantSizeTotal? k
  then validate_total_constant_size array_byte_size (parse_array p (U32.v array_byte_size) precond)
  else validate_array_gen vs array_byte_size precond
