(* Parse data of some explicitly fixed length *)

module LowParse.Spec.FLBytes
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module Classical = FStar.Classical

noextract
val parse_flbytes'
  (#t: Type0)
  (p: bare_parser t)
  (sz: nat)
: Tot (bare_parser t)

let parse_flbytes' #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes32) ->
  if Seq.length s < sz
  then None
  else
    match p (Seq.slice s 0 sz) with
    | Some (v, consumed) ->
      if (consumed <: nat) = (sz <: nat)
      then Some (v, (sz <: consumed_length s))
      else None
    | _ -> None

let parse_flbytes_injective
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sz: nat)
: Lemma
  (ensures (injective (parse_flbytes' p sz)))
= let f
    (b1 b2: bytes32)
  : Lemma
    (requires (injective_precond (parse_flbytes' p sz) b1 b2))
    (ensures (injective_postcond (parse_flbytes' p sz) b1 b2))
  = assert (injective_precond p (Seq.slice b1 0 sz) (Seq.slice b2 0 sz))
  in
  Classical.forall_intro_2 (fun b -> Classical.move_requires (f b))

noextract
val parse_flbytes
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sz: nat)
: Tot (constant_size_parser true sz t)

let parse_flbytes #b #t p sz =
  parse_flbytes_injective p sz;
  parse_flbytes' p sz  

noextract
val parse_flbytes_consumes_all
  (#t: Type0)
  (p: bare_parser t)
  (sz: nat)
: Pure (bare_parser t)
  (requires (consumes_all p))
  (ensures (fun _ -> True))

let parse_flbytes_consumes_all #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes32) ->
  if Seq.length s < sz
  then None
  else
    match p (Seq.slice s 0 sz) with
    | Some (v, _) ->
      Some (v, (sz <: consumed_length s))
    | _ -> None

let parse_flbytes_consumes_all_correct
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (sz: nat)
: Lemma
  (consumes_all p ==> (forall b . parse (parse_flbytes p sz) b == parse (parse_flbytes_consumes_all p sz) b))
= ()
