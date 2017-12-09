module LowParseExamples.Impl
include LowParseExamples.Spec
open LowParse

module T = FStar.Tactics

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module L = FStar.List.Tot

inline_for_extraction
let exa_discr_K_EREF'
  (x: U32.t)
: Pure bool
  (requires True)
  (ensures (fun y -> y == true <==> (L.mem x (L.map snd exa) /\ enum_key_of_repr exa x == "K_EREF" )))
= let f = normalize_term (discr exa "K_EREF") in
  normalize_term (f x)

inline_for_extraction
let univ_destr_gen_exa
  (t: ((k: maybe_unknown_key exa) -> Tot Type0))
  (f: ((k: maybe_unknown_key exa) -> Tot (t k)))
  (combine_if: ((k: maybe_unknown_key exa) -> Tot (if_combinator (t k))))
: (k: U32.t) ->
  Tot (t (maybe_unknown_key_of_repr exa k))
= T.synth_by_tactic (gen_enum_univ_destr_gen exa t f combine_if)

inline_for_extraction
let univ_destr_gen_exa_strong
  (t: ((k: maybe_unknown_key exa) -> Tot Type0))
  (f: ((k: maybe_unknown_key exa) -> Tot (t k)))
: (k: U32.t) ->
  Tot (y: t (maybe_unknown_key_of_repr exa k) { y == f (maybe_unknown_key_of_repr exa k) } )
= let t' (k : maybe_unknown_key exa) : Tot Type0 = (u: t k { u == f k } ) in
  let f' (k : maybe_unknown_key exa) : Tot (t' k) = f k in
  let combine_if' (k : maybe_unknown_key exa) : Tot (if_combinator (t' k)) =
    default_if (t' k)
  in
  univ_destr_gen_exa t' f' combine_if'

module S = LowParse.Slice

#set-options "--z3rlimit 128"

inline_for_extraction
let validate_exa_key_3 : stateful_validator (parse_enum_key parse_u32 exa) =
  let f =
    univ_destr_gen_exa
      (fun k -> (b: bool { b == Known? k } ))
      (fun k -> is_known exa k)
      (fun k -> default_if _)
  in
  fun (s: S.bslice) ->
    validate_filter_st
      #_
      #U32.t
      #parse_u32
      parse_u32_st
      (fun r -> Known? (maybe_unknown_key_of_repr exa r))
      (fun x -> f x)
      s

#reset-options

inline_for_extraction
val univ_destr_exa
  (t: ((k: enum_key exa) -> Tot Type0))
  (f: ((k: enum_key exa) -> Tot (t k)))
: (r: enum_repr exa) ->
  Tot (t (enum_key_of_repr exa r))

let univ_destr_exa t f =
  T.synth_by_tactic (gen_enum_univ_destr exa t f)

inline_for_extraction
val univ_destr_exa_strong
  (t: ((k: enum_key exa) -> Tot Type0))
  (f: ((k: enum_key exa) -> Tot (t k)))
: (r: enum_repr exa) ->
  Tot (y: t (enum_key_of_repr exa r) { y == f (enum_key_of_repr exa r) } )

let univ_destr_exa_strong t f =
  let t' (k : enum_key exa) : Tot Type0 = (u: t k { u == f k } ) in
  let f' (k : enum_key exa) : Tot (t' k) = f k in
  univ_destr_exa t' f'

inline_for_extraction
val repr_lift_validator_cases_exa
  (#k: parser_kind)
  (cases: (enum_key exa -> Tot Type0))
  (pc: ((x: enum_key exa) -> Tot (parser k (cases x))))
  (vs: ((x: enum_key exa) -> Tot (stateful_validator (pc x))))
: Tot ((x: U32.t) -> Tot (stateful_validator (lift_parser_cases (exa) (cases) pc (maybe_unknown_key_of_repr (exa) x))))  

let repr_lift_validator_cases_exa #k cases pc vs =
  univ_destr_gen_exa
  (fun k -> stateful_validator (lift_parser_cases exa cases pc k))
  (lift_validator_cases exa cases pc vs)
  (fun k -> validate_if _)

inline_for_extraction
val validate_test
: stateful_validator parse_test

let validate_test =
  gen_validate_sum_partial
    test
    parse_u32
    parse_u32_st
    parse_test_cases
    (repr_lift_validator_cases_exa (sum_cases test) parse_test_cases
      (function
	"K_HJEU" -> validate_u16_st
      | "K_EREF" -> validate_u8_st
    ))

inline_for_extraction
let validate_fstar_test
: stateful_validator parse_fstar_test
= validate_test `validate_synth` (fun (x: sum_type test) -> match x with
  | (| "K_HJEU", x |) -> K_HJEU x
  | (| "K_EREF", y |) -> K_EREF y
  )

// inline_for_extraction // FIXME: if set, then KreMLin produces no code
let validate_list_fstar_test
: stateful_validator (parse_list parse_fstar_test)
= validate_list validate_fstar_test

inline_for_extraction
let test_function
: stateful_validator (parse_vlbytes 3 (parse_list parse_fstar_test))
=  (validate_vlbytes 3 validate_list_fstar_test)


(* TODO: convert the following example into new style 

(*

type example' =
| Left_:
    (u1: U8.t) ->
    (u2: U8.t) ->
    example'
| Right_ of U16.t

let parse_example' : parser example' =
  parse_u8 `and_then` (fun j ->
    let j' = Int.Cast.uint8_to_uint32 j in
    if j' = 0ul
    then parse_synth (nondep_then parse_u8 parse_u8) (fun (u1, u2) -> Left_ u1 u2)
    else parse_synth parse_u16 (fun v -> Right_ v)
  )
let validate_example_st' : stateful_validator parse_example' =
   parse_then_check #_ #parse_u8 parse_u8_st #_ #(fun j -> (* FIXME: WHY WHY WHY do I need this F* explicit argument? *)
     let j' = Int.Cast.uint8_to_uint32 j in
     if j' = 0ul
     then parse_synth (nondep_then parse_u8 parse_u8) (fun (u1, u2) -> Left_ u1 u2)
     else parse_synth parse_u16 (fun v -> Right_ v)
   ) (fun j ->
     let j' = Int.Cast.uint8_to_uint32 j in
     if j' = 0ul
     then
        (validate_synth (validate_nondep_then #_ #parse_u8 validate_u8_st #_ #parse_u8 validate_u8_st) (fun (u1, u2) -> Left_ u1 u2))
     else
        (validate_synth #_ #_ #parse_u16 validate_u16_st (fun v -> Right_ v))
   )

[@"substitute"]
inline_for_extraction
let validate_u8_st_nochk : stateful_validator_nochk parse_u8 = fun _ -> 1ul
[@"substitute"]
inline_for_extraction
let validate_u16_st_nochk: stateful_validator_nochk parse_u16 = fun _ -> 2ul

let validate_example_st_nochk' : stateful_validator_nochk parse_example' =
   parse_nochk_then_nochk #_ #parse_u8 parse_u8_st_nochk #_ #(fun j -> (* FIXME: WHY WHY WHY do I need this F* explicit argument? *)
     let j' = Int.Cast.uint8_to_uint32 j in
     if j' = 0ul
     then parse_synth (nondep_then parse_u8 parse_u8) (fun (u1, u2) -> Left_ u1 u2)
     else parse_synth parse_u16 (fun v -> Right_ v)
   ) (fun j ->
     let j' = Int.Cast.uint8_to_uint32 j in
     if j' = 0ul
     then
        (validate_synth_nochk (validate_nondep_then_nochk #_ #parse_u8 validate_u8_st_nochk #_ #parse_u8 validate_u8_st_nochk) (fun (u1, u2) -> Left_ u1 u2))
     else
        (validate_synth_nochk #_ #_ #parse_u16 validate_u16_st_nochk (fun v -> Right_ v))
   )
*)


