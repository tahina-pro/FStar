module MITLSLow.Example
open MITLSLow.Continued

module S = Slice
module P = GhostParsing
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = FStar.Buffer
module T = FStar.Tactics
module E = FStar.Kremlin.Endianness

inline_for_extraction
let exa : enum UInt32.t = [
  "K_EREF", 2ul;
  "K_HJEU", 3ul;
]

inline_for_extraction
let exa_discr_K_EREF'
  (x: UInt32.t)
: Pure bool
  (requires True)
  (ensures (fun y -> y == true <==> (List.Tot.mem x (List.Tot.map snd exa) /\ enum_key_of_repr exa x == "K_EREF" )))
= let f = normalize_term (discr exa "K_EREF") in
  normalize_term (f x)

inline_for_extraction
let univ_destr_gen_exa
  (t: ((k: maybe_unknown_key exa) -> Tot Type0))
  (f: ((k: maybe_unknown_key exa) -> Tot (t k)))
  (combine_if: ((k: maybe_unknown_key exa) -> Tot (if_combinator (t k))))
: (k: UInt32.t) ->
  Tot (t (maybe_unknown_key_of_repr exa k))
= T.synth_by_tactic (gen_enum_univ_destr_gen exa t f combine_if)

inline_for_extraction
let univ_destr_gen_exa_strong
  (t: ((k: maybe_unknown_key exa) -> Tot Type0))
  (f: ((k: maybe_unknown_key exa) -> Tot (t k)))
: (k: UInt32.t) ->
  Tot (y: t (maybe_unknown_key_of_repr exa k) { y == f (maybe_unknown_key_of_repr exa k) } )
= let t' (k : maybe_unknown_key exa) : Tot Type0 = (u: t k { u == f k } ) in
  let f' (k : maybe_unknown_key exa) : Tot (t' k) = f k in
  let combine_if' (k : maybe_unknown_key exa) : Tot (if_combinator (t' k)) =
    default_if (t' k)
  in
  univ_destr_gen_exa t' f' combine_if'

inline_for_extraction
let validate_exa_key_3 : P.stateful_validator (parse_enum_key parse_u32 exa) =
  let f =
    univ_destr_gen_exa
      (fun k -> (b: bool { b == Known? k } ))
      (fun k -> is_known exa k)
      (fun k -> default_if _)
  in
  fun s ->
    validate_filter_st
      #UInt32.t
      #parse_u32
      parse_u32_st
      (fun r -> Known? (maybe_unknown_key_of_repr exa r))
      (fun x -> f x)
      s

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
  (cases: (enum_key exa -> Tot Type0))
  (pc: ((x: enum_key exa) -> Tot (P.parser (cases x))))
  (vs: ((x: enum_key exa) -> Tot (P.stateful_validator (pc x))))
: Tot ((x: UInt32.t) -> Tot (P.stateful_validator (lift_parser_cases (exa) (cases) pc (maybe_unknown_key_of_repr (exa) x))))  

let repr_lift_validator_cases_exa cases pc vs =
  univ_destr_gen_exa
  (fun k -> P.stateful_validator (lift_parser_cases exa cases pc k))
  (lift_validator_cases exa cases pc vs)
  (fun k -> validate_if _)

inline_for_extraction
let test : sum =
  make_sum exa (function
    | "K_EREF" -> UInt8.t
    | "K_HJEU" -> UInt16.t
  )

let parse_test_cases (x: sum_key test) : Tot (P.parser (sum_cases test x)) =
  match x with
    | "K_HJEU" -> parse_u16
    | "K_EREF" -> parse_u8

inline_for_extraction
val validate_test
: P.stateful_validator (parse_sum test parse_u32 parse_test_cases)

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

(* TODO: convert the following example into new style 

(*

type example' =
| Left_:
    (u1: UInt8.t) ->
    (u2: UInt8.t) ->
    example'
| Right_ of UInt16.t

let parse_example' : P.parser example' =
  parse_u8 `P.and_then` (fun j ->
    let j' = Int.Cast.uint8_to_uint32 j in
    if j' = 0ul
    then parse_synth (nondep_then parse_u8 parse_u8) (fun (u1, u2) -> Left_ u1 u2)
    else parse_synth parse_u16 (fun v -> Right_ v)
  )
let validate_example_st' : P.stateful_validator parse_example' =
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
let validate_u8_st_nochk : P.stateful_validator_nochk parse_u8 = fun _ -> 1ul
[@"substitute"]
inline_for_extraction
let validate_u16_st_nochk: P.stateful_validator_nochk parse_u16 = fun _ -> 2ul

let validate_example_st_nochk' : P.stateful_validator_nochk parse_example' =
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
