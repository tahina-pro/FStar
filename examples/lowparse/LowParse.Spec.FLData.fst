(* Parse data of some explicitly fixed length *)

module LowParse.Spec.FLData
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module Classical = FStar.Classical

inline_for_extraction
val parse_fldata'
  (#t: Type0)
  (p: bare_parser t)
  (sz: nat)
: Tot (bare_parser t)

let parse_fldata' #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes) ->
  if Seq.length s < sz
  then None
  else
    match p (Seq.slice s 0 sz) with
    | Some (v, consumed) ->
      if (consumed <: nat) = (sz <: nat)
      then Some (v, (sz <: consumed_length s))
      else None
    | _ -> None

let parse_fldata_injective
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
: Lemma
  (ensures (injective (parse_fldata' p sz)))
= let f
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond (parse_fldata' p sz) b1 b2))
    (ensures (injective_postcond (parse_fldata' p sz) b1 b2))
  = assert (injective_precond p (Seq.slice b1 0 sz) (Seq.slice b2 0 sz))
  in
  Classical.forall_intro_2 (fun b -> Classical.move_requires (f b))

// unfold
let parse_fldata_kind
  (sz: nat)
: Tot parser_kind
= {
    parser_kind_low = sz;
    parser_kind_high = Some sz;
    parser_kind_total = false;
    parser_kind_subkind = Some ParserStrong
  }

inline_for_extraction
val parse_fldata
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
: Tot (parser (parse_fldata_kind sz) t)

let parse_fldata #b #t p sz =
  parse_fldata_injective p sz;
  parse_fldata' p sz  

val parse_fldata_consumes_all
  (#t: Type0)
  (p: bare_parser t)
  (sz: nat)
: Pure (bare_parser t)
  (requires (consumes_all p))
  (ensures (fun _ -> True))

let parse_fldata_consumes_all #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes) ->
  if Seq.length s < sz
  then None
  else
    match p (Seq.slice s 0 sz) with
    | Some (v, _) ->
      Some (v, (sz <: consumed_length s))
    | _ -> None

let parse_fldata_consumes_all_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
: Lemma
  (requires (k.parser_kind_subkind == Some ParserConsumesAll))
  (ensures (forall b . parse (parse_fldata p sz) b == parse (parse_fldata_consumes_all p sz) b))
= ()
