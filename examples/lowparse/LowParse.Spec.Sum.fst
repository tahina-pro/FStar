module LowParse.Spec.Sum
include LowParse.Spec.Enum

module T = FStar.Tactics

inline_for_extraction
val parse_tagged_union
  (#kt: parser_kind)
  (#tag: Type0)
  (#tu: tag -> Type0)
  (pt: parser kt tag)
  (#k: parser_kind)
  (p: (t: tag) -> Tot (parser k (tu t))) // Tot really needed here by validator
: Tot (parser (and_then_kind kt k) (t: tag & tu t))

let parse_tagged_union #kt #tag #tu pt #k p =
  pt `and_then` (fun (v: tag) ->
    let pv : parser k (tu v) = p v in
    let synth : tu v -> Tot (t: tag & tu t) = fun (v': tu v) -> (| v, v' |) in
    parse_synth #k #(tu v) #(t: tag & tu t) pv synth
  )

inline_for_extraction
let sum = (key: eqtype & (repr: eqtype & (e: enum key repr & ((x: enum_key e) -> Tot Type0))))

inline_for_extraction
let sum_key_type (t: sum) : Tot eqtype =
  let (| key,  _ |) = t in key

inline_for_extraction
let sum_repr_type (t: sum) : Tot eqtype =
  let (| _, (| repr,  _ |) |) = t in repr

let sum_enum (t: sum) : Tot (enum (sum_key_type t) (sum_repr_type t)) =
  let (| _, (| _, (| e, _ |) |) |) = t in e

let sum_key (t: sum) : Tot Type0 =
  enum_key (sum_enum t)

let sum_cases (t: sum) : Tot ((x: sum_key t) -> Tot Type0) =
  let (|_, (| _, (| _, c |) |) |) = t in c

let sum_type (t: sum) : Tot Type0 =
  (x: sum_key t & sum_cases t x)

inline_for_extraction
let parse_sum
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
: Tot (parser (and_then_kind (parse_filter_kind kt) k) (sum_type t))
= parse_tagged_union
    #(parse_filter_kind kt)
    #(sum_key t)
    #(sum_cases t)
    (parse_enum_key p (sum_enum t))
    #k
    pc

inline_for_extraction
let make_sum
  (#key #repr: eqtype)
  (e: enum key repr)
  (cases: (enum_key e -> Tot Type0))
: Tot sum
= (| key, (| repr, (| e, cases |) |) |)
