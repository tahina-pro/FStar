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
  (#pk: parser_kind)
  (#key #repr: eqtype)
  (e: enum key repr)
  (cases: (enum_key e -> Tot Type0))
  (pc: ((x: enum_key e) -> Tot (parser pk (cases x))))
  (k: maybe_unknown_key e)
: Tot (parser (parse_filter_kind pk) (lift_cases e cases k))
= match k with
  | Known k' -> weaken (parse_filter_kind pk) (pc k')
  | _ -> fail_parser (parse_filter_kind pk) (lift_cases e cases k)

let parse_sum_synth
  (t: sum)
  (v: sum_repr_type t)
  (v' : lift_cases (sum_enum t) (sum_cases t) (maybe_unknown_key_of_repr (sum_enum t) v))
: Tot (sum_type t)
= match maybe_unknown_key_of_repr (sum_enum t) v with
  | Known k -> (| k, v' |)
  | _ -> false_elim ()

let parse_sum_payload
  (#k: parser_kind)
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (v: sum_repr_type t)
: Tot (parser (parse_filter_kind k) (sum_type t))
= parse_synth
    #(parse_filter_kind k)
    #(lift_cases (sum_enum t) (sum_cases t) (maybe_unknown_key_of_repr (sum_enum t) v))
    #(sum_type t)
    (lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_unknown_key_of_repr (sum_enum t) v))
    (parse_sum_synth t v)

#set-options "--z3rlimit 16"

let parse_sum_payload_and_then_cases_injective
  (#k: parser_kind)
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
: unit ->
  Lemma
  (and_then_cases_injective (parse_sum_payload t pc))
= fun _ -> ()

#reset-options

let parse_sum'
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
: Tot (parser (and_then_kind kt (parse_filter_kind k)) (sum_type t))
= parse_sum_payload_and_then_cases_injective t pc ();
  p `and_then` (parse_sum_payload t pc)

#set-options "--z3rlimit 256"

let parse_sum'_correct
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
: Lemma
  (forall (input: bytes32) . parse (parse_sum' t p pc) input == parse (parse_sum t p pc) input)
= ()

#reset-options

inline_for_extraction
val gen_validate_sum_partial'
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (ps: parser_st p)
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (vs' : ((x: sum_repr_type t) -> Tot (stateful_validator (lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_unknown_key_of_repr (sum_enum t) x)))))
: Tot (stateful_validator (parse_sum' t p pc))

#set-options "--z3rlimit 16"

let gen_validate_sum_partial' #kt t p ps #k pc vs' =
  let g' (v: sum_repr_type t) : Tot (stateful_validator (parse_sum_payload t pc v)) =
    validate_synth
      #(parse_filter_kind k)
      #(lift_cases (sum_enum t) (sum_cases t) (maybe_unknown_key_of_repr (sum_enum t) v))
      #(sum_type t)
      #(lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_unknown_key_of_repr (sum_enum t) v))
      (vs' v)
      (parse_sum_synth t v)
  in
  parse_then_check'
    #kt
    #(sum_repr_type t)
    #p
    ps
    #(parse_filter_kind k)
    #(sum_type t)
    #(parse_sum_payload t pc)
    (parse_sum_payload_and_then_cases_injective t pc)
    g'

#reset-options

inline_for_extraction
val gen_validate_sum_partial
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (ps: parser_st p)
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (vs' : ((x: sum_repr_type t) -> Tot (stateful_validator (lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_unknown_key_of_repr (sum_enum t) x)))))
: Tot (stateful_validator (parse_sum t p pc))

let gen_validate_sum_partial #kt t p ps #k pc vs' =
  fun (input: S.bslice) ->
  parse_sum'_correct #kt t p #k pc;
  gen_validate_sum_partial' t p ps pc vs' input

inline_for_extraction
let lift_validator_cases
  (#key #repr: eqtype)
  (e: enum key repr)
  (cases: (enum_key e -> Tot Type0))
  (#pk: parser_kind)
  (pc: ((x: enum_key e) -> Tot (parser pk (cases x))))
  (vs: ((x: enum_key e) -> Tot (stateful_validator (pc x))))
  (k: maybe_unknown_key e)
: Tot (stateful_validator (lift_parser_cases e cases pc k))
= match k with
  | Known k' -> vs k'
  | _ -> validate_fail (parse_filter_kind pk) False
