module GhostParsing

open Slice

open FStar.Tactics
open FStar.Ghost
open FStar.Seq
module List = FStar.List.Tot
open FStar.HyperStack
open FStar.HyperStack.ST
module B = FStar.Buffer

// kremlib libraries
module C = C
open C.Loops

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast

type byte = U8.t
let bytes = seq byte
/// the abstract model of input is a sequence of bytes, with a limit on size so
/// offsets always fit in a UInt32.t
let bytes32 = bs:bytes{length bs < pow2 32}

/// parse a value of type t
///
/// - the parser can fail (currently reporting an uninformative [None])
/// - it returns the parsed value as well as the number of bytes read
///   (this is intended to be the number of bytes to advance the input pointer)
///
/// note that the type does not forbid lookahead; the parser can depend on
/// values beyond the returned offset
///
/// these parsers are used as specifications, and thus use unrepresentable types
/// such as byte sequences and natural numbers and are always pure
let parser (t:Type) = b:bytes32 -> Tot (option (t * n:nat{n <= length b}))
let gparser (t:Type) = b:bytes32 -> GTot (option (t * n:nat{n <= length b}))

/// monadic bind for the parser monad
val and_then : #t:Type -> #t':Type ->
                p:parser t ->
                p': (t -> parser t') ->
                parser t'
let and_then #t #t' p p' b =
  match p b with
  | Some (v, l) ->
    begin
      match p' v (slice b l (length b)) with
      | Some (v', l') -> Some (v', l + l')
      | None -> None
    end
  | None -> None

/// monadic bind for the parser monad (ghost)
val g_and_then : #t:Type -> #t':Type ->
                p:gparser t ->
                p': (t -> GTot (gparser t')) ->
                GTot (gparser t')
let g_and_then #t #t' p p' =
  let () = () in
  fun b ->
  match p b with
  | Some (v, l) ->
    begin
      let p'v = p' v in
      match p'v (slice b l (length b)) with
      | Some (v', l') -> Some (v', l + l')
      | None -> None
    end
  | None -> None

let g_and_then_eq_and_then
  (#t:Type) (#t':Type)
                (p:parser t)
                (p': (t -> parser t'))
:                Lemma
		(p `g_and_then` p' == p `and_then` p')
= ()

/// monadic return for the parser monad
unfold let parse_ret (#t:Type) (v:t) : parser t =
  fun _ -> Some (v, 0)

/// parser that always fails
let fail_parser #t : parser t = fun b -> None

/// parser that succeeds iff at the end-of-input
let parsing_done : parser unit =
  fun b -> if length b = 0 then Some ((), 0) else None

/// projector for correctly parsed results
let parse_result (#t:Type) (#b:bytes)
  (r: option (t * n:nat{n <= length b}){Some? r}) : t =
  fst (Some?.v r)

/// A stateful parser that implements the same behavior as a pure parser. This
/// includes both the output and offset. The specification parser is an erased
/// type index; erasure helps guide extraction. The type is inlined for
/// extraction to make it clear that parsers are first-order functions taking a
/// buffer as input (as opposed to higher-order implementations that return a
/// function).
inline_for_extraction
let parser_st #t (p: gparser t) =
  input:bslice -> Stack (option (t * off:U32.t{U32.v off <= U32.v input.len}))
  (requires (fun h0 -> live h0 input))
  (ensures (fun h0 r h1 -> live h1 input /\
            modifies_none h0 h1 /\
            (let bs = as_seq h1 input in
            match p bs with
            | Some (v, n) -> Some? r /\
              begin
                let (rv, off) = Some?.v r in
                  v == rv /\ n == U32.v off
              end
            | None -> r == None)))

/// A validation is an [option U32.t], where [Some off] indicates success and
/// consumes [off] bytes. A validation checks a parse result if it returns [Some
/// off] only when the parser also succeeds and returns the same offset, with
/// any result. Note that a validation need not be complete (in particular,
/// [None] validates any parse).
unfold let validation_checks_parse #t (b: bytes)
  (v: option (off:U32.t{U32.v off <= length b}))
  (p: option (t * n:nat{n <= length b})) : Type0 =
  Some? v ==> (Some? p /\ U32.v (Some?.v v) == snd (Some?.v p))

/// A stateful validator is parametrized by a specification parser. A validator
/// does not produce a value but only checks that the data is valid. The
/// specification ensures that when a validator accepts the input the parser
/// would succeed on the same input.
inline_for_extraction
let stateful_validator #t (p: gparser t) =
  input:bslice ->
  Stack (option (off:U32.t{U32.v off <= U32.v input.len}))
    (requires (fun h0 -> live h0 input))
    (ensures (fun h0 r h1 -> live h1 input /\
                          modifies_none h0 h1 /\
                          (let bs = as_seq h1 input in
                            validation_checks_parse bs r (p bs))))

#reset-options "--z3rlimit 15 --max_fuel 1 --max_ifuel 1"

/// Validators can be composed monoidally, checking two parsers in sequence.
/// This only works when there is no structural dependency: the two parsers
/// always run one after the other. This validator will check any combination of
/// the results of the two parsers.
[@"substitute"]
let then_check #t (p: gparser t) (v: stateful_validator p)
                #t' (p': gparser t') (v': stateful_validator p')
                #t'' (f: t -> t' -> Tot t'') :
                stateful_validator (p `g_and_then` (fun x -> p' `g_and_then` (fun y -> parse_ret (f x y)))) =
fun input ->
  match v input with
  | Some off -> begin
          match v' (advance_slice input off) with
          | Some off' -> (if u32_add_overflows off off' then None
                      else Some (U32.add off off'))
          | None -> None
    end
  | None -> None

#reset-options

[@"substitute"]
let validate_done_st : stateful_validator parsing_done = fun input ->
  if U32.eq input.len 0ul then Some 0ul else None

let validate_fail : stateful_validator fail_parser =
  fun input -> None

#reset-options "--z3rlimit 40 --max_fuel 4 --max_ifuel 1"

let and_then_offset (#t:Type) (p: gparser t) (#t':Type) (p':t -> GTot (gparser t')) (bs:bytes32) :
  Lemma (requires (Some? (g_and_then p p' bs)))
        (ensures (Some? (p bs) /\
                  Some? (g_and_then p p' bs) /\
                  snd (Some?.v (p bs)) <= snd (Some?.v (g_and_then p p' bs)))) =
  match p bs with
  | Some (v, off) ->
    match p' v (slice bs off (length bs)) with
    | Some (v', off') -> ()
    | None -> ()
  | None -> ()

// TODO: this definition is here out of convenience, but should probably go somewhere else
noextract
val normalize : #t:Type -> list norm_step -> t -> tactic unit
let normalize (#t:Type) (steps : list norm_step) (x:t) : tactic unit =
  x <-- quote x;
  exact (norm_term (List.append steps [delta; primops]) x)

// original implementation, which behaves slightly differently
noextract
val normalize' : #t:Type -> list norm_step -> t -> tactic unit
let normalize' (#t:Type) (steps : list norm_step) (x:t) : tactic unit =
  dup;;
  exact (quote x);;
  norm (FStar.List.Tot.append steps [delta; primops]);;
  trefl
