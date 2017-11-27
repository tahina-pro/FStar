module LowParse.Impl.Combinators
include LowParse.Spec.Combinators
include LowParse.Impl.Base

module S = LowParse.Slice
module Seq = FStar.Seq
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U8 = FStar.UInt8
module U32 = FStar.UInt32


inline_for_extraction
val validate_and_split
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
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

let validate_and_split #b #t #p sv s =
  match sv s with
  | Some consumed ->
    let sl = S.truncate_slice s consumed in
    let sr = S.advance_slice s consumed in
    let h = HST.get () in
    assert (no_lookahead_weak_on t p (S.as_seq h s) (S.as_seq h sl));
    Some (sl, sr)
  | _ -> None

inline_for_extraction
val split
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
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

let split #b #t #p sv s =
  let consumed = sv s in
  let sl = S.truncate_slice s consumed in
  let sr = S.advance_slice s consumed in
  let h = HST.get () in
  assert (no_lookahead_weak_on t p (S.as_seq h s) (S.as_seq h sl));
  (sl, sr)

[@"substitute"]
inline_for_extraction
val validate_fail (#t: Type0) : Tot (stateful_validator (fail_parser #t))

let validate_fail #t =
  (fun (input: S.bslice) -> (
    let h = HST.get () in
    None #(consumed_slice_length input)
  )) <: stateful_validator (fail_parser #t)

[@"substitute"]
inline_for_extraction
val parse_then_check
  (#b: bool)
  (#t1: Type0)
  (#p1: parser' b t1)
  (ps1: parser_st p1)
  (#t2: Type0)
  (#p2: t1 -> Tot (parser' b t2) {
    and_then_cases_injective p2
  })
  (ps2: ((x1: t1) -> Tot (stateful_validator (p2 x1))))
: Tot (stateful_validator (and_then p1 p2))

let parse_then_check #b #t1 #p1 ps1 #t2 #p2 ps2 =
  fun input ->
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

[@"substitute"]
inline_for_extraction
let parse_nochk_then_nochk
  (#b: bool)
  (#t1: Type0)
  (#p1: parser' b t1)
  (ps1: parser_st_nochk p1)
  (#t2: Type0)
  (#p2: (t1 -> Tot (parser' b t2)) {
    and_then_cases_injective p2
  })
  (ps2: ((x1: t1) -> Tot (stateful_validator_nochk (p2 x1))))
: Tot (stateful_validator_nochk (and_then p1 p2))
= fun input ->
  let (v1, off1) = ps1 input in
  let input2 = S.advance_slice input off1 in
  let off2 = ps2 v1 input2 in
  (U32.add off1 off2 <: consumed_slice_length input)

#set-options "--z3rlimit 32"

[@"substitute"]
inline_for_extraction
let validate_nondep_then
  (#b: bool)
  (#t1: Type0)
  (#p1: parser' b t1)
  (v1: stateful_validator p1)
  (#t2: Type0)
  (#p2: parser' b t2)
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
  (#b: bool)
  (#t1: Type0)
  (#p1: parser' b t1)
  (v1: stateful_validator_nochk p1)
  (#t2: Type0)
  (#p2: parser' b t2)
  (v2: stateful_validator_nochk p2)
: Tot (stateful_validator_nochk (nondep_then p1 p2))
= fun s1 ->
  let off1 = v1 s1 in
  let s2 = S.advance_slice s1 off1 in
  let off2 = v2 s2 in
  (U32.add off1 off2 <: consumed_slice_length s1)

[@"substitute"]
inline_for_extraction
let parse_nondep_then_nochk
  (#b: bool)
  (#t1: Type0)
  (#p1: parser' b t1)
  (v1: parser_st_nochk p1)
  (#t2: Type0)
  (#p2: parser' b t2)
  (v2: parser_st_nochk p2)
: Tot (parser_st_nochk (nondep_then p1 p2))
= fun s1 ->
  let (x1, off1) = v1 s1 in
  let s2 = S.advance_slice s1 off1 in
  let (x2, off2) = v2 s2 in
  ((x1, x2), (U32.add off1 off2 <: consumed_slice_length s1))

#reset-options

inline_for_extraction
val nondep_destruct
  (#b: bool)
  (#t1: Type0)
  (#p1: parser' b t1)
  (st1: stateful_validator_nochk p1)
  (#t2: Type0)
  (p2: parser' b t2)
  (input: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    exactly_parses h (nondep_then p1 p2) input (fun _ -> True)
  ))
  (ensures (fun h r h' ->
    S.modifies_none h h' /\ (
    let (b1, b2) = r in
    S.is_concat_gen input [b1; b2] /\
    exactly_parses h (nondep_then p1 p2) input (fun v ->
    exactly_parses h p1 b1 (fun v1 ->
    exactly_parses h p2 b2 (fun v2 ->
    v == (v1, v2)
  ))))))

#set-options "--z3rlimit 32"

let nondep_destruct #b #t1 #p1 st1 #t2 p2 input =
  split st1 input

#reset-options

[@"substitute"]
inline_for_extraction
let validate_synth
  (#b: bool)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser' b t1)
  (v1: stateful_validator p1)
  (f2: (t1 -> Tot t2) {
    forall (x x' : t1) . f2 x == f2 x' ==> x == x'  
  })
: Tot (stateful_validator (parse_synth p1 f2))
= fun b -> v1 b

[@"substitute"]
inline_for_extraction
let validate_synth_nochk
  (#b: bool)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser' b t1)
  (v1: stateful_validator_nochk p1)
  (f2: (t1 -> Tot t2) {
    forall (x x' : t1) . f2 x == f2 x' ==> x == x'  
  })
: Tot (stateful_validator_nochk (parse_synth p1 f2))
= fun b -> v1 b

[@"substitute"]
inline_for_extraction
let parse_synth_st_nochk
  (#b: bool)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser' b t1)
  (ps1: parser_st_nochk p1)
  (f2: (t1 -> Tot t2) { // Tot necessary here
    forall (x x' : t1) . f2 x == f2 x' ==> x == x'  
  } )
: Tot (parser_st_nochk (parse_synth p1 f2))
= fun b ->
  let (v1, len) = ps1 b in
  (f2 v1, len)

inline_for_extraction
let validate_constant_size_nochk
  (#b: bool)
  (sz: U32.t)
  (#t: Type0)
  (p: constant_size_parser b (U32.v sz) t)
: Tot (stateful_validator_nochk p)
= fun input -> 
    let h = HST.get () in
    assert (let s = S.as_seq h input in Some? (p s));
    (sz <: consumed_slice_length input)

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

#set-options "--z3rlimit 32"

let stateful_filter_validator
  (#b: bool)
  (#t: Type0)
  (p: parser' b t)
  (f: (t -> Tot bool))
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
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (v1: stateful_validator p)
  (#f: (t -> Tot bool))
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

#reset-options

inline_for_extraction
let validate_filter_nochk
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (v1: stateful_validator_nochk p)
  (f: (t -> Tot bool))
: Tot (stateful_validator_nochk (parse_filter p f))
= fun b -> v1 b

inline_for_extraction
let validate_filter_st
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (ps: parser_st p)
  (f: (t -> Tot bool))
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
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
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
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (ps: parser_st_nochk p)
  (f: (t -> Tot bool))
: Tot (parser_st_nochk (parse_filter p f))
= fun (input: S.bslice) ->
  let (x, off) = ps input in
  let (x: t { f x == true } ) = x in
  (x, off)

inline_for_extraction
let parse_filter_st'
  (#b: bool)
  (#t: Type0)
  (#p: parser' b t)
  (ps: parser_st p)
  (f: (t -> Tot bool))
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

inline_for_extraction
let validate_if
  (#t: Type0)
  (p: bare_parser t)
: Tot (if_combinator (stateful_validator p))
= fun
  (cond: bool)
  (sv_true: (cond_true cond -> Tot (stateful_validator p)))
  (sv_false: (cond_false cond -> Tot (stateful_validator p)))
  input ->
  if cond
  then sv_true () input
  else sv_false () input
