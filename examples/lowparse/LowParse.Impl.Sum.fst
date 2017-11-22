module LowParse.Impl.Sum
include LowParse.Impl.Enum
include LowParse.Spec.Sum

module S = LowParse.Slice
module T = FStar.Tactics

let lift_cases
  (#key #repr: eqtype)
  (e: enum key repr)
  (cases: (enum_key e -> Tot Type0))
  (k: maybe_unknown_key e)
: Tot Type0
= match k with
  | Known k' -> cases k'
  | _ -> False

let lift_parser_cases
  (#b: bool)
  (#key #repr: eqtype)
  (e: enum key repr)
  (cases: (enum_key e -> Tot Type0))
  (pc: ((x: enum_key e) -> Tot (parser' b (cases x))))
  (k: maybe_unknown_key e)
: Tot (parser' b (lift_cases e cases k))
= match k with
  | Known k' -> pc k'
  | _ -> weaken' b fail_parser

noextract
let parse_sum_synth
  (t: sum)
  (v: sum_repr_type t)
  (v' : lift_cases (sum_enum t) (sum_cases t) (maybe_unknown_key_of_repr (sum_enum t) v))
: Tot (sum_type t)
= match maybe_unknown_key_of_repr (sum_enum t) v with
  | Known k -> (| k, v' |)
  | _ -> false_elim ()

noextract
let parse_sum_payload
  (#b: bool)
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (parser' b (sum_cases t x))))
  (v: sum_repr_type t)
: Tot (parser' b (sum_type t))
= parse_synth
    #b
    #(lift_cases (sum_enum t) (sum_cases t) (maybe_unknown_key_of_repr (sum_enum t) v))
    #(sum_type t)
    (lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_unknown_key_of_repr (sum_enum t) v))
    (parse_sum_synth t v)

noextract
let parse_sum'
  (#b: bool)
  (t: sum)
  (p: parser' b (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (parser' b (sum_cases t x))))
: Tot (parser' b (sum_type t))
= p `and_then` (parse_sum_payload t pc)

#set-options "--z3rlimit 64"

let parse_sum'_correct
  (#b: bool)
  (t: sum)
  (p: parser' b (sum_repr_type t))
  (pc: ((x: sum_key t) -> Tot (parser' b (sum_cases t x))))
: Lemma
  (forall (input: bytes32) . parse (parse_sum' t p pc) input == parse (parse_sum t p pc) input)
= ()

#reset-options

inline_for_extraction
val gen_validate_sum_partial'
  (#b: bool)
  (t: sum)
  (p: parser' b (sum_repr_type t))
  (ps: parser_st p)
  (pc: ((x: sum_key t) -> Tot (parser' b (sum_cases t x))))
  (vs' : ((x: sum_repr_type t) -> Tot (stateful_validator (lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_unknown_key_of_repr (sum_enum t) x)))))
: Tot (stateful_validator (parse_sum' t p pc))

#set-options "--z3rlimit 16"

let gen_validate_sum_partial' #b t p ps pc vs' =
  let g' (v: sum_repr_type t) : Tot (stateful_validator (parse_sum_payload t pc v)) =
    validate_synth
      #b
      #(lift_cases (sum_enum t) (sum_cases t) (maybe_unknown_key_of_repr (sum_enum t) v))
      #(sum_type t)
      #(lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_unknown_key_of_repr (sum_enum t) v))
      (vs' v)
      (parse_sum_synth t v)
  in
  parse_then_check
    #b
    #(sum_repr_type t)
    #p
    ps
    #(sum_type t)
    #(parse_sum_payload t pc)
    g'

#reset-options

inline_for_extraction
val gen_validate_sum_partial
  (#b: bool)
  (t: sum)
  (p: parser' b (sum_repr_type t))
  (ps: parser_st p)
  (pc: ((x: sum_key t) -> Tot (parser' b (sum_cases t x))))
  (vs' : ((x: sum_repr_type t) -> Tot (stateful_validator (lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_unknown_key_of_repr (sum_enum t) x)))))
: Tot (stateful_validator (parse_sum t p pc))

let gen_validate_sum_partial #b t p ps pc vs' =
  fun (input: S.bslice) ->
  parse_sum'_correct #b t p pc;
  gen_validate_sum_partial' t p ps pc vs' input

inline_for_extraction
let lift_validator_cases
  (#key #repr: eqtype)
  (e: enum key repr)
  (cases: (enum_key e -> Tot Type0))
  (pc: ((x: enum_key e) -> Tot (parser (cases x))))
  (vs: ((x: enum_key e) -> Tot (stateful_validator (pc x))))
  (k: maybe_unknown_key e)
: Tot (stateful_validator (lift_parser_cases e cases pc k))
= match k with
  | Known k' -> vs k'
  | _ -> validate_fail #False
