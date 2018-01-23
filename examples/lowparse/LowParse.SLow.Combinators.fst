module LowParse.SLow.Combinators
include LowParse.SLow.Base
include LowParse.Spec.Combinators

module B32 = FStar.Bytes
module U32 = FStar.UInt32

#reset-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8"

inline_for_extraction
let parse32_ret
  (#t: Type)
  (x: t)
: Tot (parser32 (parse_ret x))
= (fun input -> ((Some (x, 0ul)) <: (res: option (t * U32.t) { parser32_correct (parse_ret x) input res } )))

// inline_for_extraction
let parse32_and_then
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (p32: parser32 p)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
  (u: unit { and_then_cases_injective p' } )
  (p32' : ((x: t) -> Tot (parser32 (p' x))))
: GTot (parser32 (p `and_then` p')) // we should not use this combinator
= fun (input: bytes32) ->
  ((match p32 input with
  | Some (v, l) ->
    let input' = B32.slice input l (B32.len input) in
    begin match p32' v input' with
    | Some (v', l') ->
      Some (v', U32.add l l')
    | _ -> None
    end
  | _ -> None
  ) <: (res: option (t' * U32.t) { parser32_correct (p `and_then` p') input res } ))

inline_for_extraction
let parse32_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (p1' : parser32 p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (p2' : parser32 p2)
: Tot (parser32 (nondep_then p1 p2))
= fun (input: bytes32) ->
  ((match p1' input with
  | Some (v, l) ->
    let input' = B32.slice input l (B32.len input) in
    begin match p2' input' with
    | Some (v', l') ->
      Some ((v, v'), U32.add l l')
    | _ -> None
    end
  | _ -> None
  ) <: (res: option ((t1 * t2) * U32.t) { parser32_correct (p1 `nondep_then` p2) input res } ))

let serialize32_kind_precond
  (k1 k2: parser_kind)
: GTot bool
= Some? k1.parser_kind_high &&
  Some? k2.parser_kind_high &&
  Some?.v k1.parser_kind_high + Some?.v k2.parser_kind_high < 4294967296

inline_for_extraction
let serialize32_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (s1' : serializer32 s1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
  (s2' : serializer32 s2)
  (u' : unit {
    serialize32_kind_precond k1 k2
  })
: Tot (serializer32 (serialize_nondep_then p1 s1 u p2 s2))
= fun (input: t1 * t2) ->
  ((B32.append (s1' (fst input)) (s2' (snd input))) <:
    (res: bytes32 { serializer32_correct (serialize_nondep_then p1 s1 u p2 s2) input res } ))

inline_for_extraction
let parse32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
  (p1' : parser32 p1)
  (u: unit {
    forall (x x' : t1) . f2 x == f2 x' ==> x == x'
  })
: Tot (parser32 (parse_synth p1 f2))
= fun (input: bytes32) ->
  ((
    match p1' input with
    | Some (v1, consumed) -> Some (f2 v1, consumed)
    | _ -> None
   ) <: (res: option (t2 * U32.t) { parser32_correct (parse_synth p1 f2) input res } ))

inline_for_extraction
let serialize32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (s1' : serializer32 s1)
  (g1: t2 -> Tot t1)
  (u: unit {
    (forall (x : t2) . f2 (g1 x) == x) /\
    (forall (x x' : t1) . f2 x == f2 x' ==> x == x')
  })
: Tot (serializer32 (serialize_synth p1 f2 s1 g1 u))
= fun (input: t2) ->
  ((s1' (g1 input)) <: (res: bytes32 { serializer32_correct (serialize_synth p1 f2 s1 g1 u) input res } ))


