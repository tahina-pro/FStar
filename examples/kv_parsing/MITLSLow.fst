module MITLSLow
// module E = Extensions
module S = Slice
module P = GhostParsing
module E = FStar.Kremlin.Endianness

let parse_u8: P.parser UInt8.t =
  fun b -> if Seq.length b < 1 then None
        else Some (Seq.index b 0, 1)

let parse_u16: P.parser UInt16.t =
  fun b -> if Seq.length b < 2 then None
        else begin
          let b' = Seq.slice b 0 2 in
          E.lemma_be_to_n_is_bounded b';
          Some (UInt16.uint_to_t (E.be_to_n b'), 2)
        end

let parse_synth
  (#t1: Type0)
  (#t2: Type0)
  (p1: P.parser t1)
  (f2: P.parse_arrow t1 (fun _ -> t2))
= P.and_then p1 (fun v1 -> P.parse_ret (f2 v1))

let validate_synth
  (#t1: Type0)
  (#t2: Type0)
  (#p1: P.parser t1)
  (v1: P.stateful_validator p1)
  (f2: P.parse_arrow t1 (fun _ -> t2))
: Tot (P.stateful_validator (parse_synth p1 f2))
= fun b -> v1 b

let validate_synth_nochk
  (#t1: Type0)
  (#t2: Type0)
  (#p1: P.parser t1)
  (v1: P.stateful_validator_nochk p1)
  (f2: P.parse_arrow t1 (fun _ -> t2))
: Tot (P.stateful_validator_nochk (parse_synth p1 f2))
= fun b -> v1 b

let parse_then_check
  (#t1: Type0)
  (#p1: P.parser t1)
  (ps1: P.parser_st p1)
  (#t2: Type0)
  (#p2: P.parse_arrow t1 (fun _ -> P.parser t2))
  (ps2: ((x1: t1) -> Tot (P.stateful_validator (p2 x1))))
: Tot (P.stateful_validator (P.and_then p1 p2))
= fun input ->
  match ps1 input with
  | Some (v1, off1) ->
    let input2 = S.advance_slice input off1 in
    begin match ps2 v1 input2 with
    | Some off2 ->
      if S.u32_add_overflows off1 off2
      then None
      else Some (UInt32.add off1 off2)
    | _ -> None
    end
  | _ -> None

let parse_nochk_then_nochk
  (#t1: Type0)
  (#p1: P.parser t1)
  (ps1: P.parser_st_nochk p1)
  (#t2: Type0)
  (#p2: P.parse_arrow t1 (fun _ -> P.parser t2))
  (ps2: ((x1: t1) -> Tot (P.stateful_validator_nochk (p2 x1))))
: Tot (P.stateful_validator_nochk (P.and_then p1 p2))
= fun input ->
  let (v1, off1) = ps1 input in
  let input2 = S.advance_slice input off1 in
  let off2 = ps2 v1 input2 in
  UInt32.add off1 off2

val validate_u8_st : P.stateful_validator parse_u8
let validate_u8_st =
  fun b ->
  if UInt32.lt b.S.len 1ul
  then None
  else Some 1ul

val validate_u16_st: P.stateful_validator parse_u16
let validate_u16_st =
  fun b ->
  if UInt32.lt b.S.len 2ul
  then None
  else Some 2ul

(* Special case for non-dependent parsing *)

let nondep_then
  (#t1 #t2: Type0)
  (p1: P.parser t1)
  (p2: P.parser t2)
: Tot (P.parser (t1 * t2))
= p1 `P.and_then` (fun v1 -> p2 `P.and_then` (fun v2 -> P.parse_ret (v1, v2)))

let validate_nondep_then
  (#t1: Type0)
  (#p1: P.parser t1)
  (v1: P.stateful_validator p1)
  (#t2: Type0)
  (#p2: P.parser t2)
  (v2: P.stateful_validator p2)
: Tot (P.stateful_validator (nondep_then p1 p2))
= P.then_check p1 v1 p2 v2 (fun x1 x2 -> (x1, x2))

let validate_nondep_then_nochk
  (#t1: Type0)
  (#p1: P.parser t1)
  (v1: P.stateful_validator_nochk p1)
  (#t2: Type0)
  (#p2: P.parser t2)
  (v2: P.stateful_validator_nochk p2)
: Tot (P.stateful_validator_nochk (nondep_then p1 p2))
= fun s1 ->
  let off1 = v1 s1 in
  let s2 = S.advance_slice s1 off1 in
  let off2 = v2 s2 in
  UInt32.add off1 off2

type example' =
| Left':
    (u1: UInt8.t) ->
    (u2: UInt8.t) ->
    example'
| Right' of UInt16.t

let parse_example' : P.parser example' =
  parse_u8 `P.and_then` (fun j ->
    let j' = Int.Cast.uint8_to_uint32 j in
    if j' = 0ul
    then parse_synth (nondep_then parse_u8 parse_u8) (fun (u1, u2) -> Left' u1 u2)
    else parse_synth parse_u16 (fun v -> Right' v)
  )

let parse_u8_st_nochk :
    P.parser_st_nochk parse_u8 = fun input ->
    let b0 = Buffer.index input.S.p 0ul in
    (b0, 1ul)

let parse_u8_st : P.parser_st parse_u8 = fun input ->
    if UInt32.lt input.S.len 1ul then None
    else (Some (parse_u8_st_nochk input))

let parse_u16_st_nochk :
  P.parser_st_nochk parse_u16 = fun input ->
  let n = C.load16_be (S.truncated_slice input 2ul).S.p in
  (n, 2ul)

let parse_u16_st : P.parser_st parse_u16 = fun input ->
  if UInt32.lt input.S.len 2ul
    then None
  else Some (parse_u16_st_nochk input)

let validate_example_st' : P.stateful_validator parse_example' =
   parse_then_check #_ #parse_u8 parse_u8_st #_ #(fun j -> (* FIXME: WHY WHY WHY do I need this F* explicit argument? *)
     let j' = Int.Cast.uint8_to_uint32 j in
     if j' = 0ul
     then parse_synth (nondep_then parse_u8 parse_u8) (fun (u1, u2) -> Left' u1 u2)
     else parse_synth parse_u16 (fun v -> Right' v)
   ) (fun j ->
     let j' = Int.Cast.uint8_to_uint32 j in
     if j' = 0ul
     then
        (validate_synth (validate_nondep_then #_ #parse_u8 validate_u8_st #_ #parse_u8 validate_u8_st) (fun (u1, u2) -> Left' u1 u2))
     else
        (validate_synth #_ #_ #parse_u16 validate_u16_st (fun v -> Right' v))
   )

let validate_u8_st_nochk : P.stateful_validator_nochk parse_u8 = fun _ -> 1ul
let validate_u16_st_nochk: P.stateful_validator_nochk parse_u16 = fun _ -> 2ul

let validate_example_st_nochk' : P.stateful_validator_nochk parse_example' =
   parse_nochk_then_nochk #_ #parse_u8 parse_u8_st_nochk #_ #(fun j -> (* FIXME: WHY WHY WHY do I need this F* explicit argument? *)
     let j' = Int.Cast.uint8_to_uint32 j in
     if j' = 0ul
     then parse_synth (nondep_then parse_u8 parse_u8) (fun (u1, u2) -> Left' u1 u2)
     else parse_synth parse_u16 (fun v -> Right' v)
   ) (fun j ->
     let j' = Int.Cast.uint8_to_uint32 j in
     if j' = 0ul
     then
        (validate_synth_nochk (validate_nondep_then_nochk #_ #parse_u8 validate_u8_st_nochk #_ #parse_u8 validate_u8_st_nochk) (fun (u1, u2) -> Left' u1 u2))
     else
        (validate_synth_nochk #_ #_ #parse_u16 validate_u16_st_nochk (fun v -> Right' v))
   )
