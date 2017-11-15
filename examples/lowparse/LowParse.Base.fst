module LowParse.Base

module S = LowParse.Slice
module Seq = FStar.Seq
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Ghost = FStar.Ghost

type byte = U8.t
let bytes = S.bytes
/// the abstract model of input is a sequence of bytes, with a limit on size so
/// offsets always fit in a U32.t
let bytes32 = S.bytes32

/// parse a value of type t
///
/// - the parser can fail (currently reporting an uninformative [None])
/// - it returns the parsed value as well as the number of bytes read
///   (this is intended to be the number of bytes to advance the input pointer)
///
/// note that the type now forbids lookahead; the parser cannot depend on
/// values beyond the returned offset
///
/// these parsers are used as specifications, and thus use unrepresentable types
/// such as byte sequences and natural numbers and are always pure

(* Switch to Tot if you want an OCaml executable model for parsers *)
let parse_arrow (a: Type0) (b: (a -> Type0)) : Tot Type0 = (x: a) -> GTot (b x)

[@"substitute"]
inline_for_extraction
let consumed_length (b: bytes32) : Tot Type0 = (n: nat { n <= Seq.length b } )

//unfold
let weak_parser (t:Type0) : Tot Type0 = (b: bytes32) -> GTot (option (t * consumed_length b))

let no_lookahead_on
  (t: Type0)
  (f: weak_parser t)
  (x x' : bytes32)
: GTot Type0
= Some? (f x) ==> (
  let (Some v) = f x in
  let (y, off) = v in (
  (off <= Seq.length x' /\ Seq.length x' <= Seq.length x /\ Seq.slice x' 0 off == Seq.slice x 0 off) ==>
  Some? (f x') /\ (
  let (Some v') = f x' in
  let (y', off') = v' in
  y == y' /\ (off <: nat) == (off' <: nat)
  )))

let no_lookahead
  (t: Type0)
  (f: weak_parser t)
: GTot Type0
= forall (x x' : bytes32) . no_lookahead_on t f x x'

let parser (t: Type0) : Tot Type0 = (f: weak_parser t { no_lookahead t f } )

let parse (#t: Type0) (p: parser t) (b: bytes32) : GTot (option (t * consumed_length b)) =
  p b

[@"substitute"]
inline_for_extraction
let consumed_slice_length (input: S.bslice) : Tot Type0 =
  (off:U32.t{U32.v off <= U32.v (S.length input)})

/// A stateful parser that implements the same behavior as a pure parser. This
/// includes both the output and offset. The specification parser is an erased
/// type index; erasure helps guide extraction. The type is inlined for
/// extraction to make it clear that parsers are first-order functions taking a
/// buffer as input (as opposed to higher-order implementations that return a
/// function).
inline_for_extraction
let parser_st #t (p: parser t) : Tot Type0 =
  input:S.bslice -> HST.Stack (option (t * consumed_slice_length input))
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
let parser_st_nochk #t (p: parser t) : Tot Type0 =
  input: S.bslice -> HST.Stack (t * consumed_slice_length input)
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

let validator_checks_parse
  (#t: Type0)
  (pinput: bytes32)
  (pv: option (t * consumed_length pinput))
  (sinput: S.bslice)
  (sv: option (consumed_slice_length sinput))
: GTot Type0
= Some? sv ==> (
    Some? pv /\ (
    let (Some pv') = pv in
    let (_, pconsumed) = pv' in
    let (Some sv') = sv in
    pconsumed == U32.v sv'
  ))

let validator_checks_parse_none
  (#t: Type0)
  (pinput: bytes32)
  (pv: option (t * consumed_length pinput))
  (sinput: S.bslice)
: Lemma
  (validator_checks_parse #t pinput pv sinput None)
  [SMTPat (validator_checks_parse #t pinput pv sinput None)]
= ()

/// A stateful validator is parametrized by a specification parser. A validator
/// does not produce a value but only checks that the data is valid. The
/// specification ensures that when a validator accepts the input the parser
/// would succeed on the same input.
inline_for_extraction
let stateful_validator (#t: Type0) (p: parser t) : Tot Type0 =
  input: S.bslice ->
  HST.Stack (option (consumed_slice_length input))
    (requires (fun h0 -> S.live h0 input))
    (ensures (fun h0 r h1 -> S.live h1 input /\
                          S.modifies_none h0 h1
			  /\ (
                            let bs = S.as_seq h1 input in
			    let pv = parse p bs in
			    validator_checks_parse #t bs pv input r
    )))
(*
			  (Some? pv /\ U32.v (Some?.v r) == snd (Some?.v pv)))))))
*)

/// Same thing, but where we already know that the data is valid. (In other words, how many offsets are skipped by the data being parsed.)
inline_for_extraction
let stateful_validator_nochk (#t: Type0) (p: parser t) : Tot Type0 =
  input: S.bslice ->
  HST.Stack (consumed_slice_length input)
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

#reset-options "--z3rlimit 15"

(** Combinators *)
 
/// monadic return for the parser monad
unfold let parse_ret (#t:Type) (v:t) : Tot (parser t) =
  ((fun (b: bytes32) ->
    let z : consumed_length b = 0 in
    Some (v, z)) <: parser t)

/// parser that always fails
let fail_parser (#t: Type0) : Tot (parser t) =
  (fun b -> None) <: parser t

[@"substitute"]
inline_for_extraction
val validate_fail (#t: Type0) : Tot (stateful_validator (fail_parser #t))

let validate_fail #t =
  (fun (input: S.bslice) -> (
    let h = HST.get () in
    validator_checks_parse_none #t (S.as_seq h input) ((fail_parser #t <: parser t) (S.as_seq h input)) input;
    None #(consumed_slice_length input)
  )) <: stateful_validator (fail_parser #t)

/// monadic bind for the parser monad
val and_then : #t:Type -> #t':Type ->
                p:parser t ->
                p': parse_arrow t (fun _ -> parser t') ->
                Tot (parser t')
let and_then #t #t' p p' =
  let f : weak_parser t' =
    fun (b: bytes32) ->
    match p b with
    | Some (v, l) ->
      begin
	let p'v = p' v in
	match p'v (Seq.slice b l (Seq.length b)) with
	| Some (v', l') ->
	  let res : consumed_length b = l + l' in
	  Some (v', res)
	| None -> None
      end
    | None -> None
  in
  let prf
    (x: bytes32) 
    (x' : bytes32)
  : Lemma
    (no_lookahead_on t' f x x')
  = match f x with
    | Some v -> 
      let (y, off) = v in
      let off : nat = off in
      let (off_x : consumed_length x ) = off in
      if off <= Seq.length x'
      then
	let (off_x' : consumed_length x') = off in
	let g () : Lemma
	  (requires (Seq.length x' <= Seq.length x /\ Seq.slice x' 0 off_x' == Seq.slice x 0 off_x))
	  (ensures (
	    Some? (f x') /\ (
	    let (Some v') = f x' in
	    let (y', off') = v' in
	    y == y' /\ (off <: nat) == (off' <: nat)
	  )))
	= assert (Some? (p x));
	  let (Some (y1, off1)) = p x in
	  assert (off1 <= off);
	  assert (off1 <= Seq.length x');
	  assert (Seq.slice x' 0 off1 == Seq.slice (Seq.slice x' 0 off_x') 0 off1);
	  assert (Seq.slice x' 0 off1 == Seq.slice x 0 off1);
	  assert (no_lookahead_on t p x x');
	  assert (Some? (p x'));
	  let (Some v1') = p x' in
	  let (y1', off1') = v1' in
	  assert (y1 == y1' /\ (off1 <: nat) == (off1' <: nat));
	  let x2 : bytes32 = Seq.slice x off1 (Seq.length x) in
	  let x2' : bytes32 = Seq.slice x' off1 (Seq.length x') in
	  let p2 = p' y1 in
	  assert (Some? (p2 x2));
	  let (Some (y', off2)) = p2 x2 in
	  assert (off == off1 + off2);
	  assert (off2 <= Seq.length x2);
	  assert (off2 <= Seq.length x2');
	  assert (Seq.length x2' <= Seq.length x2);
	  assert (Seq.slice x2' 0 off2 == Seq.slice (Seq.slice x' 0 off_x') off1 (off1 + off2));
	  assert (Seq.slice x2' 0 off2 == Seq.slice x2 0 off2);
	  assert (no_lookahead_on t' p2 x2 x2');
	  ()
	in
	Classical.move_requires g ()
      else ()
    | _ -> ()
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf x));  
  (f <: parser t')

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
      let off : consumed_slice_length input = U32.add off1 off2 in
      Some off
    | _ -> None
    end
  | _ -> None

val and_then_offset
  (#t:Type0)
  (p: parser t)
  (#t':Type0)
  (p': parse_arrow t (fun _ ->parser t'))
  (bs:bytes32)
: Lemma
  (requires (
    Some? (parse (and_then #t #t' p p') bs)
  ))
  (ensures (
    let x = p bs in
    Some? x /\ (
    let y = parse (and_then #t #t' p p') bs in
    Some? y /\
    snd (Some?.v x) <= snd (Some?.v y)
  )))

let and_then_offset #t p #t' p' bs =
  match p bs with
  | Some (v, off) ->
    let p'v = p' v in
    match p'v (Seq.slice bs off (Seq.length bs)) with
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
	  let s2 = S.advance_slice input off in
          match v2 s2 with
          | Some off' ->
	    Some (U32.add off off' <: consumed_slice_length input)
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
  (U32.add off1 off2 <: consumed_slice_length s1)

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
    Some? (parse (nondep_then p1 p2) s)
  ))))
  (ensures (fun h1 b' h2 ->
    S.modifies_none h1 h2 /\
    S.includes b b' /\
    S.live h1 b /\
    S.live h1 b' /\ (
    let s = S.as_seq h1 b in
    let v = parse (nondep_then p1 p2) s in
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
    Some? (parse (nondep_then p1 p2) s)
  ))))
  (ensures (fun h1 b' h2 ->
    S.modifies_none h1 h2 /\
    S.includes b b' /\
    S.live h1 b /\
    S.live h1 b' /\ (
    let s = S.as_seq h1 b in
    let v = parse (nondep_then p1 p2) s in
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
  (U32.add off1 off2 <: consumed_slice_length input)


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
    let s' : bytes32 = Seq.slice s 0 sz in
    match f s' with
    | None -> None
    | Some v ->
      let (sz: consumed_length s) = sz in
      Some (v, sz)
  end

inline_for_extraction
let validate_constant_size_nochk
  (sz: U32.t)
  (#t: Type0)
  (p: constant_size_parser (U32.v sz) t)
: Tot (stateful_validator_nochk p)
= fun input -> 
    let h = HST.get () in
    assert (let s = S.as_seq h input in Some? ((p <: parser t) s));
    (sz <: consumed_slice_length input)

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
  if U32.lt (S.length s) sz
  then None
  else begin
    let h = HST.get () in
    assert (let s' = S.as_seq h s in Some? ((p <: parser t) s'));
    Some (sz <: consumed_slice_length s)
  end

inline_for_extraction
let parse_total_constant_size_nochk
  (sz: U32.t)
  (#t: Type0)
  (#p: total_constant_size_parser (U32.v sz) t)
  (ps: (
    (input: S.bslice) ->
    HST.Stack t
    (requires (fun h ->
      U32.v (S.length input) >= U32.v sz /\
      S.live h input
    ))
    (ensures (fun h0 v h1 ->
      U32.v (S.length input) >= U32.v sz /\
      S.live h1 input /\
      S.modifies_none h0 h1 /\ (
      let x = S.as_seq h1 input in
      let y = p x in
      Some? y /\ (
      let (Some (v', _)) = y in
      v == v'
  ))))))
: Tot (parser_st_nochk p)
= fun s ->
  let sz : consumed_slice_length s = sz in
  (ps s, sz)

inline_for_extraction
let parse_total_constant_size
  (sz: U32.t)
  (#t: Type0)
  (#p: total_constant_size_parser (U32.v sz) t)
  (ps: (parser_st_nochk p))
: Tot (parser_st p)
= fun s ->
  if U32.lt (S.length s) sz
  then None
  else Some (ps s)


(** Refinements *)

let parse_filter
  (#t: Type0)
  (p: parser t)
  (f: parse_arrow t (fun _ -> bool))
: Tot (parser (x: t { f x == true }))
= p `and_then` (fun (v: t) ->
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
    then
      let (v: t { f v == true } ) = v in
      Some (v, off)
    else None
  | _ -> None

inline_for_extraction
let parse_filter_st_nochk
  (#t: Type0)
  (#p: parser t)
  (ps: parser_st_nochk p)
  (f: parse_arrow t (fun _ -> bool))
: Tot (parser_st_nochk (parse_filter p f))
= fun (input: S.bslice) ->
  let (x, off) = ps input in
  let (x: t { f x == true } ) = x in
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
    then
      let (v: t { f v == true } ) = v in
      Some (v, off)
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

(** Slices that exactly correspond to some parsed data *)

unfold
let parses
  (#t: Type0)
  (h: HS.mem)
  (p: parser t)
  (s: S.bslice)
  (k: ((t * consumed_slice_length s) -> GTot Type0))
: GTot Type0
= S.live h s /\ (
  let sq : bytes32 = S.as_seq h s in
  let y = p sq in (
  Some? y /\ (
  let (Some (v', l)) = y in
  k (v', U32.uint_to_t l)
  )))

unfold
let exactly_parses
  (#t: Type0)
  (h: HS.mem)
  (p: parser t)
  (s: S.bslice)
  (k: (t -> GTot Type0))
: GTot Type0
= S.live h s /\ (
  let sq : bytes32 = S.as_seq h s in
  let y = p sq in (
  Some? y /\ (
  let (Some (v', len)) = y in
  len == U32.v (S.length s) /\
  k v'
  )))

inline_for_extraction
val validate_and_split
  (#t: Type0)
  (#p: parser t)
  (sv: stateful_validator p)
  (s: S.bslice)
: HST.Stack (option (S.bslice * S.bslice))
  (requires (fun h ->
    S.live h s
  ))
  (ensures (fun h r h' ->
    S.modifies_none h h' /\
    S.live h s /\
    (Some? r ==> (
    let (Some (sl, sr)) = r in
    S.is_concat s sl sr /\
    parses h p s (fun (v, l) ->
    exactly_parses h p sl (fun v' ->
    S.length sl == l /\
    v == v'
  ))))))

let validate_and_split #t #p sv s =
  match sv s with
  | Some consumed ->
    let sl = S.truncate_slice s consumed in
    let sr = S.advance_slice s consumed in
    let h = HST.get () in
    assert (no_lookahead_on t p (S.as_seq h s) (S.as_seq h sl));
    Some (sl, sr)
  | _ -> None

inline_for_extraction
val split
  (#t: Type0)
  (#p: parser t)
  (sv: stateful_validator_nochk p)
  (s: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.live h s /\
    parses h p s (fun _ -> True)
  ))
  (ensures (fun h r h' ->
    S.modifies_none h h' /\
    S.live h s /\ (
    let (sl, sr) = r in
    S.is_concat s sl sr /\
    parses h p s (fun (v, l) ->
    exactly_parses h p sl (fun v' ->
    S.length sl == l /\
    v == v'
  )))))

let split #t #p sv s =
  let consumed = sv s in
  let sl = S.truncate_slice s consumed in
  let sr = S.advance_slice s consumed in
  let h = HST.get () in
  assert (no_lookahead_on t p (S.as_seq h s) (S.as_seq h sl));
  (sl, sr)
