module LowParse.SLow.Enum
include LowParse.Spec.Enum
include LowParse.SLow.Combinators

module L = FStar.List.Tot
module U32 = FStar.UInt32

(* Parser for enums *)

let maybe_enum_key_of_repr'_t
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot Type0
= (x: repr) ->
  Tot (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } )

let rec maybe_enum_key_of_repr'
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot (maybe_enum_key_of_repr'_t e)
= match e with
  | [] -> (fun x -> ((Unknown x) <: (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } )))
  | (k, r) :: e' ->
    let f = maybe_enum_key_of_repr' e' in
    (fun x -> ((
      if x = r
      then Known k
      else match f x with
      | Known k' -> Known (k' <: key)
      | Unknown _ -> Unknown x
    ) <: (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } )))

inline_for_extraction
let parse32_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
: Tot (parser32 (parse_maybe_enum_key p e))
= parse32_synth p (maybe_enum_key_of_repr e) (maybe_enum_key_of_repr' e) p32 ()

#set-options "--z3rlimit 32 --max_fuel 8 --max_ifuel 8"

inline_for_extraction
let parse32_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
: Tot (parser32 (parse_enum_key p e))
= (fun (input: bytes32) -> ((
    match parse32_maybe_enum_key p32 e input with
    | Some (k, consumed) ->
      begin match k with
      | Known k' -> Some (k', consumed)
      | _ -> None
      end
    | _ -> None
  ) <: (res: option (enum_key e * U32.t) { parser32_correct (parse_enum_key p e) input res } )))

#reset-options

let enum_repr_of_key'_t
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot Type0
= (x: enum_key e) ->
  Tot (r: enum_repr e { r == enum_repr_of_key e x } )

let rec enum_repr_of_key'
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot (enum_repr_of_key'_t e)
= match e with
  | [] -> (fun (x: enum_key e) -> ((false_elim ()) <: (r: enum_repr e { enum_repr_of_key e x == r } )))
  | (k, r) :: e' ->
    let f = enum_repr_of_key' e' in
    (fun (x: enum_key e) -> (
      if x = k
      then r
      else (f (x <: key) <: repr)
    ) <: (r: enum_repr e { enum_repr_of_key e x == r } ))

inline_for_extraction
let serialize32_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
: Tot (serializer32 (serialize_enum_key p s e))
= let f = enum_repr_of_key' e in
  fun (input: enum_key e) -> ((s32 (f input)) <: (r: bytes32 { serializer32_correct (serialize_enum_key p s e) input r } ))

(*
inline_for_extraction
let maybe_enum_repr_of_key'
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot


  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  
