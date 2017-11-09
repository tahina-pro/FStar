module LowParse.Base

module S = LowParse.Slice
module Seq = FStar.Seq
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U8 = FStar.UInt8
module U32 = FStar.UInt32

type byte = U8.t
let bytes = Seq.seq byte
/// the abstract model of input is a sequence of bytes, with a limit on size so
/// offsets always fit in a U32.t
let bytes32 = bs:bytes{ Seq.length bs < pow2 32}

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

(* Switch to Tot if you want an OCaml executable model for parsers *)
let parse_arrow (a: Type0) (b: (a -> Type0)) = (x: a) -> GTot (b x)

let parser (t:Type) = (b: bytes32) -> GTot (option (t * (n: nat { n <= Seq.length b } )))

/// A stateful parser that implements the same behavior as a pure parser. This
/// includes both the output and offset. The specification parser is an erased
/// type index; erasure helps guide extraction. The type is inlined for
/// extraction to make it clear that parsers are first-order functions taking a
/// buffer as input (as opposed to higher-order implementations that return a
/// function).
inline_for_extraction
let parser_st #t (p: parser t) =
  input:S.bslice -> HST.Stack (option (t * off:U32.t{U32.v off <= U32.v (S.length input)}))
  (requires (fun h0 -> S.live h0 input))
  (ensures (fun h0 r h1 -> S.live h1 input /\
            S.modifies_none h0 h1 /\
            (let bs = S.as_seq h1 input in
            match p bs with
            | Some (v, n) -> Some? r /\
              begin
                let (rv, off) = Some?.v r in
                  v == rv /\ n == U32.v off
              end
            | None -> r == None)))

/// A stateful parser much like parser_st, except that error cases are
/// precluded. The precondition includes that the specification parser succeeds
/// on the input, and under this assumption a parser_st_nochk does not fail and
/// has the same behavior as the specification parser. The implementation need
/// not make error checks since those cases are impossible.
inline_for_extraction
let parser_st_nochk #t (p: parser t) =
  input: S.bslice -> HST.Stack (t * off:U32.t{U32.v off <= U32.v (S.length input)})
  (requires (fun h0 -> S.live h0 input /\
                    (let bs = S.as_seq h0 input in
                     Some? (p bs))))
  (ensures (fun h0 r h1 -> S.live h1 input /\
                  S.modifies_none h0 h1 /\
                  (let bs = S.as_seq h1 input in
                    Some? (p bs) /\
                    (let (v, n) = Some?.v (p bs) in
                     let (rv, off) = r in
                       v == rv /\
                       n == U32.v off))))

/// A validation is an [option U32.t], where [Some off] indicates success and
/// consumes [off] bytes. A validation checks a parse result if it returns [Some
/// off] only when the parser also succeeds and returns the same offset, with
/// any result. Note that a validation need not be complete (in particular,
/// [None] validates any parse).
unfold let validation_checks_parse #t (b: bytes)
  (v: option (off:U32.t{U32.v off <= Seq.length b}))
  (p: option (t * n:nat{n <= Seq.length b})) : Type0 =
  Some? v ==> (Some? p /\ U32.v (Some?.v v) == snd (Some?.v p))

/// A stateful validator is parametrized by a specification parser. A validator
/// does not produce a value but only checks that the data is valid. The
/// specification ensures that when a validator accepts the input the parser
/// would succeed on the same input.
inline_for_extraction
let stateful_validator #t (p: parser t) =
  input: S.bslice ->
  HST.Stack (option (off:U32.t{U32.v off <= U32.v (S.length input)}))
    (requires (fun h0 -> S.live h0 input))
    (ensures (fun h0 r h1 -> S.live h1 input /\
                          S.modifies_none h0 h1 /\
                          (let bs = S.as_seq h1 input in
                            validation_checks_parse bs r (p bs))))

/// Same thing, but where we already know that the data is valid. (In other words, how many offsets are skipped by the data being parsed.)
inline_for_extraction
let stateful_validator_nochk #t (p: parser t) =
  input: S.bslice ->
  HST.Stack (off: U32.t { U32.v off <= U32.v (S.length input) } )
  (requires (fun h0 ->
    S.live h0 input /\ (
    let s = S.as_seq h0 input in
    Some? (p s)
  )))
  (ensures (fun h0 r h1 ->
    S.live h1 input /\
    S.modifies_none h0 h1 /\ (
    let s = S.as_seq h1 input in (
    Some? (p s) /\ (
    let (Some (_, consumed)) = p s in
    U32.v r == consumed
  )))))

#reset-options "--z3rlimit 15 --max_fuel 1 --max_ifuel 1"

(** Combinators *)
 
/// monadic return for the parser monad
unfold let parse_ret (#t:Type) (v:t) : parser t =
   fun _ -> Some (v, 0)

/// parser that always fails
let fail_parser #t : parser t = fun b -> None

[@"substitute"]
inline_for_extraction
let validate_fail : stateful_validator fail_parser =
  fun input -> None

/// monadic bind for the parser monad
val and_then : #t:Type -> #t':Type ->
                p:parser t ->
                p': parse_arrow t (fun _ -> parser t') ->
                parser t'
let and_then #t #t' p p' b =
  match p b with
  | Some (v, l) ->
    begin
      let p'v = p' v in
      match p'v (Seq.slice b l (Seq.length b)) with
      | Some (v', l') -> Some (v', l + l')
      | None -> None
    end
  | None -> None

[@"substitute"]
inline_for_extraction
let parse_then_check
  (#t1: Type0)
  (#p1: parser t1)
  (ps1: parser_st p1)
  (#t2: Type0)
  (#p2: parse_arrow t1 (fun _ -> parser t2))
  (ps2: ((x1: t1) -> Tot (stateful_validator (p2 x1))))
: Tot (stateful_validator (and_then p1 p2))
= fun input ->
  match ps1 input with
  | Some (v1, off1) ->
    let input2 = S.advance_slice input off1 in
    begin match ps2 v1 input2 with
    | Some off2 ->
      if S.u32_add_overflows off1 off2
      then None
      else Some (U32.add off1 off2)
    | _ -> None
    end
  | _ -> None

let and_then_offset (#t:Type) (p: parser t) (#t':Type) (p': parse_arrow t (fun _ ->parser t')) (bs:bytes32) :
  Lemma (requires (Some? (and_then p p' bs)))
        (ensures (Some? (p bs) /\
                  Some? (and_then p p' bs) /\
                  snd (Some?.v (p bs)) <= snd (Some?.v (and_then p p' bs)))) =
  match p bs with
  | Some (v, off) ->
    match p' v (Seq.slice bs off (Seq.length bs)) with
    | Some (v', off') -> ()
    | None -> ()
  | None -> ()

(* Special case for non-dependent parsing *)

let nondep_then
  (#t1 #t2: Type0)
  (p1: parser t1)
  (p2: parser t2)
: Tot (parser (t1 * t2))
= p1 `and_then` (fun v1 -> p2 `and_then` (fun v2 -> parse_ret (v1, v2)))

[@"substitute"]
inline_for_extraction
let validate_nondep_then
  (#t1: Type0)
  (#p1: parser t1)
  (v1: stateful_validator p1)
  (#t2: Type0)
  (#p2: parser t2)
  (v2: stateful_validator p2)
: Tot (stateful_validator (nondep_then p1 p2))
= fun input ->
  match v1 input with
  | Some off -> begin
          match v2 (S.advance_slice input off) with
          | Some off' -> (if S.u32_add_overflows off off' then None
                      else Some (U32.add off off'))
          | None -> None
    end
  | None -> None

[@"substitute"]
inline_for_extraction
let validate_nondep_then_nochk
  (#t1: Type0)
  (#p1: parser t1)
  (v1: stateful_validator_nochk p1)
  (#t2: Type0)
  (#p2: parser t2)
  (v2: stateful_validator_nochk p2)
: Tot (stateful_validator_nochk (nondep_then p1 p2))
= fun s1 ->
  let off1 = v1 s1 in
  let s2 = S.advance_slice s1 off1 in
  let off2 = v2 s2 in
  U32.add off1 off2

inline_for_extraction
val nondep_fst
  (#t1: Type0)
  (p1: parser t1)
  (#t2: Type0)
  (p2: parser t2)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    S.live h b /\ (
    let s = S.as_seq h b in (
    Some? (nondep_then p1 p2 s)
  ))))
  (ensures (fun h1 b' h2 ->
    S.modifies_none h1 h2 /\
    S.includes b b' /\
    S.live h1 b /\
    S.live h1 b' /\ (
    let s = S.as_seq h1 b in
    let v = nondep_then p1 p2 s in
    let s' = S.as_seq h1 b' in
    let v' = p1 s' in (
    Some? v /\
    Some? v' /\ (
    let (Some ((v_fst, _), _)) = v in
    let (Some (v'_, _)) = v' in
    v'_ == v_fst
  )))))

let nondep_fst #t1 p1 #t2 p2 b =
  b

inline_for_extraction
val nondep_snd
  (#t1: Type0)
  (#p1: parser t1)
  (st1: stateful_validator_nochk p1)
  (#t2: Type0)
  (p2: parser t2)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    S.live h b /\ (
    let s = S.as_seq h b in (
    Some? (nondep_then p1 p2 s)
  ))))
  (ensures (fun h1 b' h2 ->
    S.modifies_none h1 h2 /\
    S.includes b b' /\
    S.live h1 b /\
    S.live h1 b' /\ (
    let s = S.as_seq h1 b in
    let v = nondep_then p1 p2 s in
    let s' = S.as_seq h1 b' in
    let v' = p2 s' in (
    Some? v /\
    Some? v' /\ (
    let (Some ((_, v_snd), _)) = v in
    let (Some (v'_, _)) = v' in
    v'_ == v_snd
  )))))

let nondep_snd #t1 #p1 st1 #t2 p2 b =
  let off1 = st1 b in
  let b' = S.advance_slice b off1 in
  b'

#reset-options

(** Apply a total transformation on parsed data *)

let parse_synth
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser t1)
  (f2: parse_arrow t1 (fun _ -> t2))
= and_then p1 (fun v1 -> parse_ret (f2 v1))

[@"substitute"]
inline_for_extraction
let validate_synth
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser t1)
  (v1: stateful_validator p1)
  (f2: parse_arrow t1 (fun _ -> t2))
: Tot (stateful_validator (parse_synth p1 f2))
= fun b -> v1 b

[@"substitute"]
inline_for_extraction
let validate_synth_nochk
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser t1)
  (v1: stateful_validator_nochk p1)
  (f2: parse_arrow t1 (fun _ -> t2))
: Tot (stateful_validator_nochk (parse_synth p1 f2))
= fun b -> v1 b

[@"substitute"]
inline_for_extraction
let parse_nochk_then_nochk
  (#t1: Type0)
  (#p1: parser t1)
  (ps1: parser_st_nochk p1)
  (#t2: Type0)
  (#p2: parse_arrow t1 (fun _ -> parser t2))
  (ps2: ((x1: t1) -> Tot (stateful_validator_nochk (p2 x1))))
: Tot (stateful_validator_nochk (and_then p1 p2))
= fun input ->
  let (v1, off1) = ps1 input in
  let input2 = S.advance_slice input off1 in
  let off2 = ps2 v1 input2 in
  U32.add off1 off2


(** Parsing data of constant size *)

let constant_size_parser_prop
  (sz: nat)
  (t: Type0)
  (f: parser t)
: GTot Type0
= forall (s: bytes32) .
  Some? (f s) ==> (
    let (_, consumed) = Some?.v (f s) in
    sz == consumed
  )
  
let constant_size_parser
  (sz: nat)
  (t: Type0)
: Tot Type0
= (f: parser t { constant_size_parser_prop sz t f } )

inline_for_extraction
let make_constant_size_parser
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes32 {Seq.length s == sz}) -> Tot (option t)))
: Tot (constant_size_parser sz t)
= let () = () in
  fun (s: bytes32) ->
  if Seq.length s < sz
  then None
  else begin
    let s' = Seq.slice s 0 sz in
    let (sz: nat { sz <= Seq.length s } ) = sz in
    match f s' with
    | None -> None
    | Some v -> Some (v, sz)
  end

inline_for_extraction
let validate_constant_size_nochk
  (sz: U32.t)
  (#t: Type0)
  (p: constant_size_parser (U32.v sz) t)
: Tot (stateful_validator_nochk p)
= fun _ -> sz

let total_constant_size_parser
  (sz: nat)
  (t: Type0)
: Tot Type0
= (f: constant_size_parser sz t {
    forall (s: bytes32) . {:pattern (f s) }
    (Seq.length s < sz) == (None? (f s))
  })

inline_for_extraction
let make_total_constant_size_parser
  (sz: nat)
  (t: Type0)
  (f: (s: bytes32 {Seq.length s == sz}) -> Tot t)
: Tot (total_constant_size_parser sz t)
= make_constant_size_parser sz t (fun x -> Some (f x))

inline_for_extraction
let validate_total_constant_size
  (sz: U32.t)
  (#t: Type0)
  (p: total_constant_size_parser (U32.v sz) t)
: Tot (stateful_validator p)
= fun s ->
  if U32.lt s.S.len sz
  then None
  else Some sz

inline_for_extraction
let parse_total_constant_size
  (sz: U32.t)
  (#t: Type0)
  (#p: total_constant_size_parser (U32.v sz) t)
  (ps: parser_st_nochk p)
: Tot (parser_st p)
= fun s ->
  if U32.lt s.S.len sz
  then None
  else Some (ps s)


(** Refinements *)

let parse_filter
  (#t: Type0)
  (p: parser t)
  (f: parse_arrow t (fun _ -> bool))
: Tot (parser (x: t { f x == true }))
= p `and_then` (fun v ->
    if f v
    then
      let (v' : t { f v' == true } ) = v in
      parse_ret v'
    else fail_parser
  )
 
let stateful_filter_validator
  (#t: Type0)
  (p: parser t)
  (f: parse_arrow t (fun _ -> bool))
: Tot Type0
= (v2: (
    (b: S.bslice) ->
    HST.Stack bool
    (requires (fun h ->
      S.live h b /\ (
      let s = S.as_seq h b in (
      Some? (p s)
    ))))
    (ensures (fun h0 r h1 ->
      S.live h0 b /\
      S.live h1 b /\
      S.modifies_none h0 h1 /\ (
      let s = S.as_seq h0 b in
      let v' = p s in (
      Some? v' /\ (
      let (Some (w, _)) = v' in (
      r == f w
  ))))))))

inline_for_extraction
let validate_filter
  (#t: Type0)
  (#p: parser t)
  (v1: stateful_validator p)
  (#f: parse_arrow t (fun _ -> bool))
  (v2: stateful_filter_validator p f)
: Tot (stateful_validator (parse_filter p f))
= fun b ->
    let r1 = v1 b in
    if Some? r1
    then
      let r2 = v2 b in
      if r2
      then r1
      else None
    else None

inline_for_extraction
let validate_filter_nochk
  (#t: Type0)
  (#p: parser t)
  (v1: stateful_validator_nochk p)
  (f: parse_arrow t (fun _ -> bool))
: Tot (stateful_validator_nochk (parse_filter p f))
= fun b -> v1 b

inline_for_extraction
let validate_filter_st
  (#t: Type0)
  (#p: parser t)
  (ps: parser_st p)
  (f: parse_arrow t (fun _ -> bool))
  (f': ((x: t) -> Pure bool (requires True) (ensures (fun y -> y == f x)))) // checker MUST be total here (we do have a stateful parser)
: Tot (stateful_validator (parse_filter p f))
= fun input ->
  match ps input with
  | Some (v, off) ->
    if f' v
    then Some off
    else None
  | _ -> None

inline_for_extraction
let parse_filter_st
  (#t: Type0)
  (#p: parser t)
  (ps: parser_st p)
  (f: (t -> Tot bool)) // checker MUST be total here (we do have a stateful parser)
: Tot (parser_st (parse_filter p f))
= fun input ->
  match ps input with
  | Some (v, off) ->
    if f v
    then Some (v, off)
    else None
  | _ -> None

inline_for_extraction
let parse_filter_st_nochk
  (#t: Type0)
  (#p: parser t)
  (ps: parser_st_nochk p)
  (f: parse_arrow t (fun _ -> bool))
: Tot (parser_st_nochk (parse_filter p f))
= fun input ->
  let (x, off) = ps input in
  (x, off)

inline_for_extraction
let parse_filter_st'
  (#t: Type0)
  (#p: parser t)
  (ps: parser_st p)
  (f: (t -> GTot bool))
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
: Tot (parser_st (parse_filter p f))
= fun input ->
  match ps input with
  | Some (v, off) ->
    if f' v
    then Some (v, off)
    else None
  | _ -> None

(* Helpers to define `if` combinators *)

let cond_true (cond: bool) : Tot Type0 = (u: unit { cond == true } )

let cond_false (cond: bool) : Tot Type0 = (u: unit { cond == false } )

let if_combinator
  (t: Type0)
: Tot Type0
= (cond: bool) ->
  (sv_true: (cond_true cond -> Tot t)) ->
  (sv_false: (cond_false cond -> Tot t)) ->
  Tot t

inline_for_extraction
let validate_if
  (#t: Type0)
  (p: parser t)
: Tot (if_combinator (stateful_validator p))
= fun
  (cond: bool)
  (sv_true: (cond_true cond -> Tot (stateful_validator p)))
  (sv_false: (cond_false cond -> Tot (stateful_validator p)))
  input ->
  if cond
  then sv_true () input
  else sv_false () input

inline_for_extraction
let default_if
  (t: Type0)
: Tot (if_combinator t)
= fun
  (cond: bool)
  (s_true: (cond_true cond -> Tot t))
  (s_false: (cond_false cond -> Tot t))
-> if cond
  then s_true ()
  else s_false ()
