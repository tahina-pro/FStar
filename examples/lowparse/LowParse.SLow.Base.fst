module LowParse.SLow.Base
include LowParse.Spec.Base

module B32 = FStar.Bytes
module U32 = FStar.UInt32

let bytes32 = B32.bytes

let parser32_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes32)
  (res: option (t * U32.t))
: GTot Type0
= let gp = parse p (B32.reveal input) in
  match res with
  | None -> gp == None
  | Some (hres, consumed) ->
    Some? gp /\ (
      let (Some (hres' , consumed')) = gp in
      hres == hres' /\
      U32.v consumed == (consumed' <: nat)
    )
 
let parser32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: bytes32) -> Tot (res: option (t * U32.t) { parser32_correct p input res } )

let validator_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes32)
  (res: option U32.t)
: GTot Type0
= let gp = parse p (B32.reveal input) in
  match res with
  | None -> gp == None
  | Some (consumed) ->
    Some? gp /\ (
      let (Some (_ , consumed')) = gp in
      U32.v consumed == (consumed' <: nat)
    )

let validator
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: bytes32) -> Tot (res: option U32.t { validator_correct p input res } )

let serializer32_correct
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (input: t)
  (res: bytes32)
: GTot Type0
= B32.reveal res == s input

let serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot Type0
= (input: t) -> Tot (res: bytes32 { serializer32_correct s input res } )

let partial_serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot Type0
= (input: t { Seq.length (s input) < 4294967296 } ) -> Tot (res: bytes32 { serializer32_correct s input res } )

let serializer32_then_parser32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: t)
: Lemma
  (p32 (s32 input) == Some (input, B32.len (s32 input)))
= ()

inline_for_extraction
let b32slice
  (b: bytes32)
  (s: U32.t)
  (e: U32.t)
: Pure bytes32
  (requires (U32.v s <= U32.v e /\ U32.v e <= B32.length b))
  (ensures (fun res -> B32.reveal res == Seq.slice (B32.reveal b) (U32.v s) (U32.v e)))
= B32.slice b s e

let parser32_then_serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: bytes32)
: Lemma
  (requires (Some? (p32 input)))
  (ensures (
    let (Some (v, consumed)) = p32 input in
    s32 v == b32slice input 0ul consumed
  ))
= serializer_correct_implies_complete p s
