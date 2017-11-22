module LowParse.Impl.FLBytes
include LowParse.Impl.Combinators
include LowParse.Spec.FLBytes

module U32 = FStar.UInt32
module S = LowParse.Slice

inline_for_extraction
let validate_flbytes
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (ps: stateful_validator p)
  (len: U32.t)
: Tot (stateful_validator (parse_flbytes p (U32.v len)))
= fun (input: S.bslice) ->
  let blen = S.length input in
  if U32.lt blen len
  then begin
    None
  end else begin
    let input'  = S.truncate_slice input len in
    match ps input' with
    | Some consumed ->
      if consumed = len
      then Some ((consumed <: U32.t) <: consumed_slice_length input)
      else None
    | _ -> None
  end

inline_for_extraction
let validate_flbytes_nochk
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (len: U32.t)
: Tot (stateful_validator_nochk (parse_flbytes p (U32.v len)))
= validate_constant_size_nochk len (parse_flbytes p (U32.v len))
