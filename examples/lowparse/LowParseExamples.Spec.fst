module LowParseExamples.Spec
open LowParse.Spec

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module L = FStar.List.Tot

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

let weaken_parse_cases_kind
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_cases s x)))
: Tot parser_kind
= let keys : list (sum_key_type s) = List.Tot.map fst (sum_enum s) in
  glb_list_of #(sum_key_type s) (fun (x: sum_key_type s) ->
    if List.Tot.mem x keys
    then let (| k, _ |) = f x in k
    else ParserUnknown
  ) (List.Tot.map fst (sum_enum s))

let parse_sum_cases
  (s: sum)
  (f: (x: sum_key s) -> Tot (k: parser_kind & parser k (sum_cases s x)))
  (x: sum_key s)
: Tot (parser _ (sum_cases s x))
= let (| _, p |) = f x in
  weaken (weaken_parse_cases_kind s f) p

let parse_test_cases : (x: sum_key test) -> Tot (parser _ (sum_cases test x)) =
  parse_sum_cases test (fun (x: sum_key test) -> match x with
    | "K_HJEU" -> (| _, parse_u16 |)
    | "K_EREF" -> (| _, parse_u8 |)
  )

let parse_test
: parser _ (sum_type test)
= parse_sum test parse_u32 parse_test_cases

noeq
type fstar_test =
  | K_HJEU of U16.t
  | K_EREF of U8.t

let parse_fstar_test
: parser _ fstar_test
= parse_test `parse_synth` (fun (x: sum_type test) -> match x with
  | (| "K_HJEU", x |) -> K_HJEU x
  | (| "K_EREF", y |) -> K_EREF y
  )
