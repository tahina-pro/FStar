module LowParseMLExamples
open LowParse.Spec

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

inline_for_extraction
let exa : enum string U32.t = [
  "K_EREF", 2ul;
  "K_HJEU", 3ul;
]

inline_for_extraction
let test : sum =
  make_sum exa (function
    | "K_EREF" -> U8.t
    | "K_HJEU" -> U16.t
  )

let parse_test_cases (x: sum_key test) : Tot (parser (sum_cases test x)) =
  match x with
    | "K_HJEU" -> parse_u16
    | "K_EREF" -> parse_u8

let parse_test
: parser (sum_type test)
= parse_sum test parse_u32 parse_test_cases

noeq
type fstar_test =
  | K_HJEU of U16.t
  | K_EREF of U8.t

let parse_fstar_test
: parser fstar_test
= parse_test `parse_synth` (fun (x: sum_type test) -> match x with
  | (| "K_HJEU", x |) -> K_HJEU x
  | (| "K_EREF", y |) -> K_EREF y
  )
