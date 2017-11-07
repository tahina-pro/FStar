module MITLSLow.Continued
include MITLSLow

module S = Slice
module P = GhostParsing

val parse_tagged_union
  (#tag: Type0)
  (#tu: tag -> Type0)
  (pt: P.parser tag)
//  (p: P.parse_arrow (t: tag) (fun t -> P.parser (tu t)))
  (p: (t: tag) -> Tot (P.parser (tu t))) // Tot really needed here by validator
: Tot (P.parser (t: tag & tu t))

let parse_tagged_union #tag #tu pt p =
  pt `P.and_then` (fun (v: tag) ->
    parse_synth #(tu v) #(t: tag & tu t) (p v) (fun (v': tu v) -> (| v, v' |)
  ))

val validate_tagged_union
  (#tag: Type0)
  (#tu: tag -> Type0)
  (#pt: P.parser tag)
  (pt_st: P.parser_st pt)
  (#p: (t: tag) -> Tot (P.parser (tu t)))
  (v_st: (t: tag) -> Tot (P.stateful_validator (p t)))
: Tot (P.stateful_validator (parse_tagged_union pt p))

let validate_tagged_union #tag #tu #pt pt_st #p v_st =
  parse_then_check pt_st #(t : tag & tu t) #(fun v -> parse_synth #(tu v) #(t: tag & tu t) (p v) (fun (v': tu v) -> (| v, v' |) )) (fun v -> validate_synth #(tu v) #(t: tag & tu t) #(p v) (v_st v) (fun (v': tu v) -> (| v, v' |)))

val validate_tagged_union_nochk
  (#tag: Type0)
  (#tu: tag -> Type0)
  (#pt: P.parser tag)
  (pt_st: P.parser_st_nochk pt)
  (#p: (t: tag) -> Tot (P.parser (tu t)))
  (v_st: (t: tag) -> Tot (P.stateful_validator_nochk (p t)))
: Tot (P.stateful_validator_nochk (parse_tagged_union pt p))

let validate_tagged_union_nochk #tag #tu #pt pt_st #p v_st =
  parse_nochk_then_nochk pt_st #(t : tag & tu t) #(fun v -> parse_synth #(tu v) #(t: tag & tu t) (p v) (fun (v': tu v) -> (| v, v' |) )) (fun v -> validate_synth_nochk #(tu v) #(t: tag & tu t) #(p v) (v_st v) (fun (v': tu v) -> (| v, v' |)))

val parse_sized : (#t: Type0) -> (p: P.parser t) -> (sz: nat) -> Tot (P.parser t)

let parse_sized #t p sz =
  let () = () in // Necessary to pass arity checking
  fun s ->
  if Seq.length s < sz
  then None
  else
    match p (Seq.slice s 0 sz) with
    | Some (v, consumed) ->
      if consumed = sz
      then Some (v, consumed)
      else None
    | _ -> None

let parse_sized1 (#t: Type0) (p: P.parser t) (sz: UInt8.t) : Tot (P.parser t) = parse_sized p (UInt8.v sz)

let parse_vlbytes1 (#t: Type0) (p: P.parser t) : Tot (P.parser t) =
  parse_u8 `P.and_then` (fun len -> parse_sized1 p len)

(*  Useless for now
<<
let parse_sized1_st
  (#t: Type0)
  (#p: Ghost.erased (P.parser t))
  (ps: P.parser_st p)
  (len: UInt8.t)
: P.parser_st (erased_arrow (parse_sized1_erased p) len)
= fun input ->
  let len' : UInt32.t = Int.Cast.uint8_to_uint32 len in
  assert (UInt32.v len' == UInt8.v len);
  let blen = S.BSlice?.len input in
  let test = UInt32.lt blen len' in
  assume (test = (UInt32.v blen < UInt32.v len' ));
  if test
  then begin
    assert (UInt32.v blen < UInt32.v len');
    None
  end else begin
    assert (UInt32.v len' <= UInt32.v blen);
    let input' = S.truncate_slice input len' in
    match ps input' with
    | Some (v, consumed) ->
      let test = (consumed = len') in
      assume (test == (UInt32.v consumed = UInt32.v len' ));
      if test
      then Some (v, consumed)
      else None
    | _ -> None
  end
>>

// TODO: WHY WHY WHY do I need all those unfold above? 

let and_then_st
  (#t1: Type0)
  (#p1: Ghost.erased (P.parser t1))
  (ps1: P.parser_st p1)
  (#t2: Type0)
  (#p2: Ghost.erased (t1 -> P.parser t2))
  (ps2: ((x1: t1) -> P.parser_st (erased_arrow p2 x1)))
: P.parser_st (Ghost.elift2 P.and_then p1 p2)
= fun input ->
  match ps1 input with
  | Some (v1, off1) ->
    let input2 = S.advance_slice input off1 in
    begin match ps2 v1 input2 with
    | Some (v2, off2) ->
      if S.u32_add_overflows off1 off2
      then None
      else Some (v2, UInt32.add off1 off2)
    | _ -> None
    end
  | _ -> None

let parse_vlbytes1_st
  (#t: Type0)
  (#p: Ghost.erased (P.parser t))
  (ps: P.parser_st p)
: P.parser_st (Ghost.elift1 (parse_vlbytes1 #t) p)
= let t1 = Ghost.elift1 (parse_vlbytes1 #t) p in
  let ps' : P.parser_st t1 =
    and_then_st #UInt8.t #(Ghost.hide IP.parse_u8) IP.parse_u8_st (parse_sized1_st ps)
  in
  ps'
>>
*)

let validate_sized1
  (#t: Type0)
  (#p: P.parser t)
  (ps: P.stateful_validator p)
  (len: UInt8.t)
: Tot (P.stateful_validator (parse_sized1 p len))
= fun input ->
  let len' : UInt32.t = Int.Cast.uint8_to_uint32 len in
  let blen = S.BSlice?.len input in
  if UInt32.lt blen len'
  then begin
    None
  end else begin
    let input'  = S.truncate_slice input len'  in
    match ps input' with
    | Some consumed ->
      if consumed = len'
      then Some consumed
      else None
    | _ -> None
  end

let validate_sized1_nochk
  (#t: Type0)
  (p: P.parser t)
  (len: UInt8.t)
: Tot (P.stateful_validator_nochk (parse_sized1 p len))
= fun _ -> Int.Cast.uint8_to_uint32 len

let validate_vlbytes1
  (#t: Type0)
  (#p: P.parser t)
  (ps: P.stateful_validator p)
: P.stateful_validator (parse_vlbytes1 p)
= parse_then_check #_ #parse_u8 parse_u8_st #_ #(fun n -> parse_sized1 p n) (fun n -> validate_sized1 ps n)

let validate_vlbytes1_nochk
  (#t: Type0)
  (p: P.parser t)
: Tot (P.stateful_validator_nochk (parse_vlbytes1 p))
= parse_nochk_then_nochk #_ #parse_u8 parse_u8_st_nochk #_ #(fun n -> parse_sized1 p n) (fun n -> validate_sized1_nochk p n)

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = FStar.Buffer

val point_to_vlbytes1_contents
  (#t: Type0)
  (#p: P.parser t)
  (ps: P.stateful_validator p)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    S.live h b /\ (
    let s = S.as_seq h b in (
    Some? (parse_vlbytes1 p s)
  ))))
  (ensures (fun h0 b' h1 ->
    B.modifies_none h0 h1 /\
    S.live h0 b /\
    S.live h0 b' /\ (
    let s = S.as_seq h0 b in
    let v = parse_vlbytes1 p s in (
    Some? v /\ (
    let (Some (v', consumed)) = v in (
    B.includes (S.truncated_slice b (UInt32.uint_to_t consumed)).S.p b'.S.p /\
    (
    let s' = S.as_seq h1 b' in
    let v'' = p s' in (
    Some? v'' /\ (
    let (Some (v'', len')) = v'' in (
    v'' == v' /\
    len' == UInt32.v (S.BSlice?.len b')
  ))))))))))

#set-options "--z3rlimit 16"

let point_to_vlbytes1_contents #t #p ps b =
  let h0 = HST.get () in
  let v = parse_u8_st b in
  assert (Some? v);
  let (Some (len, off1)) = v in
  let b1 = S.advance_slice b off1 in
  assert (b1.S.p == B.sub b.S.p off1 (UInt32.sub b.S.len off1));
  let len' = FStar.Int.Cast.uint8_to_uint32 len in
  assert (UInt32.v len' <= UInt32.v (S.BSlice?.len b1));
  let b' = S.truncate_slice b1 len' in
  assert (b1.S.p == B.sub b.S.p off1 (UInt32.sub b.S.len off1));
  assert (b'.S.p == B.sub b1.S.p 0ul len');
  let f () : Lemma
  (
    let s = S.as_seq h0 b in
    let (Some (_, consumed)) = parse_vlbytes1 p s in
    b'.S.p == B.sub (B.sub b.S.p 0ul (UInt32.uint_to_t consumed)) off1 len'
  )
  = let s = S.as_seq h0 b in
    let (Some (_, consumed)) = parse_vlbytes1 p s in
    B.sub_sub b.S.p 0ul (UInt32.uint_to_t consumed) off1 len';
    B.sub_sub b.S.p off1 (UInt32.sub b.S.len off1) 0ul len'
  in
  f ();
  b'

val nondep_fst
  (#t1: Type0)
  (p1: P.parser t1)
  (#t2: Type0)
  (p2: P.parser t2)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    S.live h b /\ (
    let s = S.as_seq h b in (
    Some? (nondep_then p1 p2 s)
  ))))
  (ensures (fun h1 b' h2 ->
    B.modifies_none h1 h2 /\
    B.includes b.S.p b'.S.p /\
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

val nondep_snd
  (#t1: Type0)
  (#p1: P.parser t1)
  (st1: P.stateful_validator_nochk p1)
  (#t2: Type0)
  (p2: P.parser t2)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    S.live h b /\ (
    let s = S.as_seq h b in (
    Some? (nondep_then p1 p2 s)
  ))))
  (ensures (fun h1 b' h2 ->
    B.modifies_none h1 h2 /\
    B.includes b.S.p b'.S.p /\
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

let parse_filter
  (#t: Type0)
  (p: P.parser t)
  (f: P.parse_arrow t (fun _ -> bool))
: Tot (P.parser (x: t { f x == true }))
= p `P.and_then` (fun v ->
    if f v
    then
      let (v' : t { f v' == true } ) = v in
      P.parse_ret v'
    else P.fail_parser
  )
 
let stateful_filter_validator
  (#t: Type0)
  (p: P.parser t)
  (f: P.parse_arrow t (fun _ -> bool))
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
      B.modifies_none h0 h1 /\ (
      let s = S.as_seq h0 b in
      let v' = p s in (
      Some? v' /\ (
      let (Some (w, _)) = v' in (
      r == f w
  ))))))))

inline_for_extraction
let validate_filter
  (#t: Type0)
  (#p: P.parser t)
  (v1: P.stateful_validator p)
  (#f: P.parse_arrow t (fun _ -> bool))
  (v2: stateful_filter_validator p f)
: Tot (P.stateful_validator (parse_filter p f))
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
  (#p: P.parser t)
  (v1: P.stateful_validator_nochk p)
  (f: P.parse_arrow t (fun _ -> bool))
: Tot (P.stateful_validator_nochk (parse_filter p f))
= fun b -> v1 b

inline_for_extraction
let validate_filter_st
  (#t: Type0)
  (#p: P.parser t)
  (ps: P.parser_st p)
  (f: P.parse_arrow t (fun _ -> bool))
  (f': ((x: t) -> Pure bool (requires True) (ensures (fun y -> y == f x)))) // checker MUST be total here (we do have a stateful parser)
: Tot (P.stateful_validator (parse_filter p f))
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
  (#p: P.parser t)
  (ps: P.parser_st p)
  (f: (t -> Tot bool)) // checker MUST be total here (we do have a stateful parser)
: Tot (P.parser_st (parse_filter p f))
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
  (#p: P.parser t)
  (ps: P.parser_st_nochk p)
  (f: P.parse_arrow t (fun _ -> bool))
: Tot (P.parser_st_nochk (parse_filter p f))
= fun input ->
  let (x, off) = ps input in
  (x, off)

type example_tag = | Left | Right

type example = ( t: example_tag & (
  match t with
  | Left -> (UInt8.t * UInt8.t)
  | Right -> UInt16.t
) )

let constant_size_parser
  (sz: nat)
  (t: Type0)
: Type0
= (f: P.parser t {
    forall (s: P.bytes32) .
    match f s with
    | None -> True
    | Some (_, consumed) -> consumed == sz
  })

inline_for_extraction
let validate_constant_size_nochk
  (sz: UInt32.t)
  (#t: Type0)
  (p: constant_size_parser (UInt32.v sz) t)
: Tot (P.stateful_validator_nochk p)
= fun _ -> sz

let total_constant_size_parser
  (sz: nat)
  (t: Type0)
: Type0
= (f: constant_size_parser sz t {
    forall (s: P.bytes32) .
    (Seq.length s < sz) == (None? (f s))
  })

inline_for_extraction
let validate_total_constant_size
  (sz: UInt32.t)
  (#t: Type0)
  (p: total_constant_size_parser (UInt32.v sz) t)
: Tot (P.stateful_validator p)
= fun s ->
  if UInt32.lt s.S.len sz
  then None
  else Some sz

inline_for_extraction
let parse_total_constant_size
  (sz: UInt32.t)
  (#t: Type0)
  (#p: total_constant_size_parser (UInt32.v sz) t)
  (ps: P.parser_st_nochk p)
: Tot (P.parser_st p)
= fun s ->
  if UInt32.lt s.S.len sz
  then None
  else Some (ps s)

let integer_size : Type0 = (sz: nat { 1 <= sz /\ sz <= 4 } )

inline_for_extraction
let bounded_integer
  (i: integer_size)
: Tot Type0
= (u: UInt32.t { UInt32.v u < pow2 (FStar.Mul.op_Star 8 i) } )

assume
val parse_bounded_integer
  (i: integer_size)
: Tot (total_constant_size_parser i (bounded_integer i))

val log256
  (n: UInt32.t)
: Pure nat
  (requires (UInt32.v n > 0))
  (ensures (fun l ->
    1 <= l /\
    l <= 4 /\
    pow2 (FStar.Mul.op_Star 8 (l - 1)) <= UInt32.v n /\
    UInt32.v n < pow2 (FStar.Mul.op_Star 8 l)
  ))

let log256 n =
  let z0 = 1ul in
  let z1 = UInt32.mul 256ul z0 in
  let l = 1 in
  assert_norm (pow2 (FStar.Mul.op_Star 8 l) == UInt32.v z1);
  assert_norm (pow2 (FStar.Mul.op_Star 8 (l - 1)) == UInt32.v z0);
  if UInt32.lt n z1
  then
    l
  else begin
    let z2 = UInt32.mul 256ul z1 in
    let l = l + 1 in
    assert_norm (pow2 (FStar.Mul.op_Star 8 l) == UInt32.v z2);
    if UInt32.lt n z2
    then
      l
    else begin
      let z3 = UInt32.mul 256ul z2 in
      let l = l + 1 in
      assert_norm (pow2 (FStar.Mul.op_Star 8 l) == UInt32.v z3);
      if UInt32.lt n z3
      then
        l    
      else begin
        let l = l + 1 in
        assert_norm (pow2 (FStar.Mul.op_Star 8 l) == FStar.Mul.op_Star 256 (UInt32.v z3));
        l
      end
    end
  end

inline_for_extraction
let in_bounds
  (min: UInt32.t)
  (max: UInt32.t)
  (x: UInt32.t)
: Tot bool
= not (UInt32.lt x min || UInt32.lt max x)

let parse_vlbytes'
  (min: UInt32.t)
  (max: UInt32.t { UInt32.v max > 0 } )
  (#t: Type0)
  (p: P.parser t)
  (sz: integer_size { sz == log256 max } )
: Tot (P.parser t)
= parse_filter
    (parse_bounded_integer sz)
    (in_bounds min max)
  `P.and_then`
  (fun len ->
    parse_sized p (UInt32.v len)
  )

let parse_vlbytes
  (min: UInt32.t)
  (max: UInt32.t { UInt32.v max > 0 } )
  (#t: Type0)
  (p: P.parser t)
: Tot (P.parser t)
= let sz : integer_size = log256 max in
  parse_vlbytes' min max p sz

assume
val parse_bounded_integer_st_nochk
  (i: integer_size)
: Tot (P.parser_st_nochk (parse_bounded_integer i))

inline_for_extraction
let parse_bounded_integer_st
  (i: integer_size)
: Tot (P.parser_st (parse_bounded_integer i))
= parse_total_constant_size (UInt32.uint_to_t i) (parse_bounded_integer_st_nochk i)

inline_for_extraction
let validate_sized
  (#t: Type0)
  (#p: P.parser t)
  (ps: P.stateful_validator p)
  (len': UInt32.t)
: Tot (P.stateful_validator (parse_sized p (UInt32.v len')))
= fun input ->
  let blen = S.BSlice?.len input in
  if UInt32.lt blen len'
  then begin
    None
  end else begin
    let input'  = S.truncate_slice input len'  in
    match ps input' with
    | Some consumed ->
      if consumed = len'
      then Some consumed
      else None
    | _ -> None
  end

inline_for_extraction
let validate_sized_nochk
  (#t: Type0)
  (p: P.parser t)
  (len: UInt32.t)
: Tot (P.stateful_validator_nochk (parse_sized p (UInt32.v len)))
= fun _ -> len

inline_for_extraction
let validate_vlbytes'
  (min: UInt32.t)
  (max: UInt32.t { UInt32.v max > 0 } )
  (#t: Type0)
  (#p: P.parser t)
  (pv: P.stateful_validator p)
  (sz: integer_size { sz == log256 max } )
: Tot (P.stateful_validator (parse_vlbytes' min max p sz))
= parse_then_check
    #_
    #(parse_filter (parse_bounded_integer sz) (in_bounds min max))
    (parse_filter_st (parse_bounded_integer_st sz) (in_bounds min max))
    #_
    #(fun len -> parse_sized p (UInt32.v len))
    (fun len -> validate_sized pv len)

inline_for_extraction
let validate_vlbytes
  (min: UInt32.t)
  (max: UInt32.t { UInt32.v max > 0 } )
  (#t: Type0)
  (#p: P.parser t)
  (pv: P.stateful_validator p)
: Tot (P.stateful_validator (parse_vlbytes min max p))
= let sz = log256 max in
  validate_vlbytes' min max pv sz

inline_for_extraction
let validate_vlbytes_nochk'
  (min: UInt32.t)
  (max: UInt32.t { UInt32.v max > 0 } )
  (#t: Type0)
  (p: P.parser t)
  (sz: integer_size { sz == log256 max } )
: Tot (P.stateful_validator_nochk (parse_vlbytes' min max p sz))
= parse_nochk_then_nochk
    #_
    #(parse_filter (parse_bounded_integer sz) (in_bounds min max))
    (parse_filter_st_nochk (parse_bounded_integer_st_nochk sz) (in_bounds min max))
    #_
    #(fun len -> parse_sized p (UInt32.v len))
    (fun len -> validate_sized_nochk p len)

inline_for_extraction
let validate_vlbytes_nochk
  (min: UInt32.t)
  (max: UInt32.t { UInt32.v max > 0 } )
  (#t: Type0)
  (p: P.parser t)
: Tot (P.stateful_validator_nochk (parse_vlbytes min max p))
= let sz = log256 max in
  validate_vlbytes_nochk' min max p sz

type enum (repr: eqtype) = (l: list (string * repr) {
  List.Tot.noRepeats (List.Tot.map fst l) /\
  List.Tot.noRepeats (List.Tot.map snd l)
})

type enum_key (#repr: eqtype) (e: enum repr) = (s: string { List.Tot.mem s (List.Tot.map fst e) } )

type enum_repr (#repr: eqtype) (e: enum repr) = (r: repr { List.Tot.mem r (List.Tot.map snd e) } )

(*
unfold
let enum_key_cons (#repr: eqtype) (e e': enum repr) (xy: string * repr) (k: enum_key e) : Pure (enum_key e') (requires (e' == xy :: e)) (ensures (fun _ -> True)) =
  let k' : string = k in
  k'
*)

let flip (#a #b: Type) (c: (a * b)) : Tot (b * a) = let (ca, cb) = c in (cb, ca)

let rec map_flip_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (List.Tot.map flip (List.Tot.map flip l) == l)
= match l with
  | [] -> ()
  | _ :: q -> map_flip_flip q

let rec map_fst_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (List.Tot.map fst (List.Tot.map flip l) == List.Tot.map snd l)
= match l with
  | [] -> ()
  | _ :: q -> map_fst_flip q

let rec map_snd_flip (#a #b: Type) (l: list (a * b)) : Lemma
  (List.Tot.map snd (List.Tot.map flip l) == List.Tot.map fst l)
= match l with
  | [] -> ()
  | _ :: q -> map_snd_flip q

let rec assoc_flip_elim
  (#a #b: eqtype)
  (l: list (a * b))
  (y: b)
  (x: a)
: Lemma
  (requires (
    List.Tot.noRepeats (List.Tot.map fst l) /\
    List.Tot.noRepeats (List.Tot.map snd l) /\
    List.Tot.assoc y (List.Tot.map flip l) == Some x
  ))
  (ensures (
    List.Tot.assoc x l == Some y
  ))
  (decreases l)
= let ((x', y') :: l') = l in
  if y' = y
  then ()
  else begin
    assume (x' <> x);
    assoc_flip_elim l' y x
  end

let rec assoc_flip_intro
  (#a #b: eqtype)
  (l: list (a * b))
  (y: b)
  (x: a)
: Lemma
  (requires (
    List.Tot.noRepeats (List.Tot.map fst l) /\
    List.Tot.noRepeats (List.Tot.map snd l) /\
    List.Tot.assoc x l == Some y
  ))
  (ensures (
    List.Tot.assoc y (List.Tot.map flip l) == Some x
  ))
= map_fst_flip l;
  map_snd_flip l;
  map_flip_flip l;
  assoc_flip_elim (List.Tot.map flip l) x y

let rec enum_key_of_repr
  (#repr: eqtype)
  (e: enum repr)
  (r: enum_repr e)
: Pure (enum_key e)
  (requires True)
  (ensures (fun y -> List.Tot.assoc y e == Some r))
= map_fst_flip e;
  let e' = List.Tot.map flip e in
  List.Tot.assoc_mem r e';
  let k = Some?.v (List.Tot.assoc r e') in
  assoc_flip_elim e r k;
  List.Tot.assoc_mem k e;
  (k <: enum_key e)

let rec parse_enum_key
  (#repr: eqtype)
  (p: P.parser repr)
  (e: enum repr)
: Tot (P.parser (enum_key e))
= (p
    `parse_filter`
    (fun r -> List.Tot.mem r (List.Tot.map snd e))
  )
  `parse_synth`
  (fun x -> enum_key_of_repr e x)

module T = FStar.Tactics

(*
let rec gen_check_in_enum
  (#repr: eqtype)
  (e: enum repr)
  (y: T.term (* repr *) )
: Tot (T.tactic (T.term (* b: bool { b == List.Tot.mem y (List.Tot.map snd e) } *) ))
  (decreases e)
= let mk_fv x = T.pack (T.Tv_FVar (T.pack_fv x)) in
  T.bind (T.quote repr) (fun repr' ->
    match e with
    | [] -> T.return (mk_fv T.false_qn)
    | (_, y') :: e' ->
      T.bind (T.quote y') (fun y'' ->
        let test = T.mk_app (mk_fv T.eq1_qn) [
          (repr', T.Q_Implicit);
          (y, T.Q_Explicit);
          (y'', T.Q_Explicit)
        ]
        in
        T.bind (gen_check_in_enum e' y) (fun t' ->
          let br_true = (T.Pat_Constant T.C_True, mk_fv T.true_qn) in
          let br_false = (T.Pat_Constant T.C_False, t') in
          let m = T.pack (T.Tv_Match test [ br_true; br_false ] ) in
          T.return m
  )))
*)

let mk_if (test e_true e_false: T.term) : Tot T.term =
  let br_true = (T.Pat_Constant T.C_True, e_true) in
  let br_false = (T.Pat_Constant T.C_False, e_false) in
  let m = T.pack (T.Tv_Match test [ br_true; br_false ] ) in
  m

noextract
let rec gen_enum_destr
  (#repr: eqtype)
  (e: enum repr)
  (y: T.term)
  (x: (enum_key e -> Tot (T.tactic T.term)))
  (z: T.term)
: Tot (T.tactic T.term)
  (decreases e)
= T.bind (T.quote (op_Equality #repr)) (fun eq_repr ->
    match e with
    | [] -> T.return z
    | (x', y') :: e' ->
      T.bind (T.quote y') (fun y'' ->
        let test = T.mk_app eq_repr [
          (y, T.Q_Explicit);
          (y'', T.Q_Explicit)
        ]
        in
        T.bind (gen_enum_destr e' y (fun (k: enum_key e') ->
          x ((k <: string) <: enum_key e)
        ) z) (fun t' ->
          T.bind (x x') (fun rt ->
            let m = mk_if test rt t' in
            T.return m
  ))))

noextract
let gen_filter_key_term
  (#repr: eqtype)
  (e: enum repr)
  (x' : T.term)
: Tot (T.tactic T.term)
= T.bind (T.quote false) (fun false' ->
  T.bind (T.quote true) (fun true' ->
    T.bind (
      gen_enum_destr
       e
       x'
       (fun _ -> T.return true')
       false'
    ) (fun t -> T.return t)
  ))

let exa : enum UInt32.t = [
  "K_EREF", 2ul;
  "K_HJEU", 3ul;
]

(*

noextract
let gen_filter_key
  (#repr: eqtype)
  (e: enum repr)
  (x : repr)
: Tot (T.tactic unit)
= T.bind (T.quote x) (fun x' ->
    T.bind (gen_filter_key_term e x') (fun y' ->
      T.exact_guard (T.return y')
  ))

inline_for_extraction
let check_exa_key
  (x: UInt32.t)
: Pure bool
  (requires True)
  (ensures (fun y -> y == List.Tot.mem x (List.Tot.map snd exa)))
= T.synth_by_tactic (gen_filter_key exa x)

inline_for_extraction
let check_exa_key'
  (x: UInt32.t)
: Pure bool
  (requires True)
  (ensures (fun y -> y == List.Tot.mem x (List.Tot.map snd exa)))
= normalize_term (List.Tot.mem x (List.Tot.map snd exa))
*)

// #set-options "--print_implicits"

inline_for_extraction
let coerce
  (#t1: Type)
  (u: t1)
  (t2: Type)
: Pure t2
  (requires (t1 == t2))
  (ensures (fun v -> t1 == t2 /\ u == v))
= u

inline_for_extraction
let gen_validate_key_partial
  (#repr: eqtype)
  (#p: P.parser repr)
  (ps: P.parser_st p)
  (e: enum repr)
  (f' : ((x: repr) -> Tot (b: bool { b == List.Tot.mem x (List.Tot.map snd e) } )))
: Tot (P.stateful_validator (parse_enum_key p e))
= let g =
    validate_filter_st
      #repr
      #p
      ps
      (fun x -> List.Tot.mem x (List.Tot.map snd e))
      f'
  in
  (
    validate_synth
      #(r: repr { List.Tot.mem r (List.Tot.map snd e) } )
      #(enum_key e)
      #(p `parse_filter` (fun r -> List.Tot.mem r (List.Tot.map snd e)))
      g
      (fun x -> enum_key_of_repr e x)
    `coerce`
    P.stateful_validator (parse_enum_key p e)
  )

noextract
let gen_validate_key
  (#repr: eqtype)
  (#p: P.parser repr)
  (ps: P.parser_st p)
  (e: enum repr)
: Tot (T.tactic unit)
= T.bind (T.quote repr) (fun repr' ->
    let x = T.fresh_binder repr' in
    let x' = T.pack (T.Tv_Var x) in
    T.bind (gen_filter_key_term e x') (fun check_key_body ->
      let res_1 = T.pack (T.Tv_Abs x check_key_body) in
      T.bind (T.quote (
        gen_validate_key_partial
          #repr
          #p
          ps
          e
      )) (fun res_0 ->
        let res =
          T.mk_app res_0 [res_1, T.Q_Explicit]
        in
        T.exact_guard (T.return res)
  )))

module E = FStar.Kremlin.Endianness

let parse_u32: P.parser UInt32.t =
  fun b -> if Seq.length b < 4 then None
        else begin
          let b' = Seq.slice b 0 4 in
          E.lemma_be_to_n_is_bounded b';
          Some (UInt32.uint_to_t (E.be_to_n b'), 4)
        end

inline_for_extraction
let parse_u32_st_nochk :
  P.parser_st_nochk (parse_u32) = fun input ->
  let n = C.load32_be (S.truncated_slice input 4ul).S.p in
  (n, 4ul)

inline_for_extraction
let parse_u32_st : P.parser_st (parse_u32) = fun input ->
  if UInt32.lt input.S.len 4ul
    then None
    else Some (parse_u32_st_nochk input)

inline_for_extraction
let validate_exa_key : P.stateful_validator (parse_enum_key parse_u32 exa) =
  (T.synth_by_tactic (gen_validate_key #_ #parse_u32 parse_u32_st exa))

inline_for_extraction
let validate_exa_key_1 : P.stateful_validator (parse_enum_key parse_u32 exa) =
  gen_validate_key_partial parse_u32_st exa (fun x -> normalize_term (List.Tot.mem x (List.Tot.map snd exa)))

inline_for_extraction
let validate_exa_key_2 : P.stateful_validator (parse_enum_key parse_u32 exa) =
  gen_validate_key_partial parse_u32_st exa (fun x -> (List.Tot.mem x (List.Tot.map snd exa)))

let rec enum_repr_of_key
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
: Pure (enum_repr e)
  (requires True)
  (ensures (fun r -> List.Tot.assoc k e == Some r))
= List.Tot.assoc_mem k e;
  let r = Some?.v (List.Tot.assoc k e) in
  assoc_flip_intro e r k;
  List.Tot.assoc_mem r (List.Tot.map flip e);
  map_fst_flip e;
  (r <: enum_repr e)

let enum_repr_of_key_of_repr
  (#repr: eqtype)
  (e: enum repr)
  (r: enum_repr e)
: Lemma
  (enum_repr_of_key e (enum_key_of_repr e r) == r)
= ()

let enum_key_of_repr_of_key
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
: Lemma
  (enum_key_of_repr e (enum_repr_of_key e k) == k)
= assoc_flip_intro e (enum_repr_of_key e k) k

let discr_prop
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
  (x: repr)
: Lemma
  (x == enum_repr_of_key e k <==> (List.Tot.mem x (List.Tot.map snd e) /\ enum_key_of_repr e x == k))
= enum_key_of_repr_of_key e k

inline_for_extraction
let discr
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
: Tot (
    (x: repr) ->
    Tot (y: bool { y == true <==> (List.Tot.mem x (List.Tot.map snd e) /\ enum_key_of_repr e x == k) } )
  )
= let r = enum_repr_of_key e k in
  fun x ->
    discr_prop e k x;
    x = r

inline_for_extraction
let exa_discr_K_EREF'
  (x: UInt32.t)
: Pure bool
  (requires True)
  (ensures (fun y -> y == true <==> (List.Tot.mem x (List.Tot.map snd exa) /\ enum_key_of_repr exa x == "K_EREF" )))
= let f = normalize_term (discr exa "K_EREF") in
  normalize_term (f x)

inline_for_extraction
let sum = (repr: eqtype & (e: enum repr & ((x: enum_key e) -> Tot Type0)))

let sum_key_repr (t: sum) : Tot eqtype =
  let (| repr,  _ |) = t in repr

let sum_enum (t: sum) : Tot (enum (sum_key_repr t)) =
  let (| _, (| e, _ |) |) = t in e

let sum_key (t: sum) : Tot Type0 =
  enum_key (sum_enum t)

let sum_cases (t: sum) : Tot ((x: sum_key t) -> Tot Type0) =
  let (|_, (| _, c |) |) = t in c

let sum_data (t: sum) : Tot Type0 =
  (x: sum_key t & sum_cases t x)

let parse_sum
  (t: sum)
  (p: P.parser (sum_key_repr t))
  (pc: ((x: sum_key t) -> Tot (P.parser (sum_cases t x))))
: Tot (P.parser (sum_data t))
= parse_tagged_union
    #(sum_key t)
    #(sum_cases t)
    (parse_enum_key p (sum_enum t))
    pc

let make_sum
  (#repr: eqtype)
  (e: enum repr)
  (cases: (enum_key e -> Tot Type0))
: Tot sum
= (| repr, (| e, cases |) |)

let unknown_enum_key (#repr: eqtype) (e: enum repr) : Tot Type0 =
  (r: repr { List.Tot.mem r (List.Tot.map snd e) == false } )

type maybe_unknown_key (#repr: eqtype) (e: enum repr) =
| Known of (enum_key e)
| Unknown of (unknown_enum_key e)

let maybe_unknown_key_of_repr
  (#repr: eqtype)
  (e: enum repr)
  (r: repr)
: Tot (maybe_unknown_key e)
= if List.Tot.mem r (List.Tot.map snd e)
  then Known (enum_key_of_repr e r)
  else Unknown r

val enum_univ_destr_spec_gen
  (#repr: eqtype)
  (e: enum repr)
  (t: (maybe_unknown_key e -> Tot Type0))
  (f: ((k: maybe_unknown_key e) -> Tot (t k)))
  (r: repr)
: Tot (t (maybe_unknown_key_of_repr e r))

let enum_univ_destr_spec_gen #repr e t f r =
  f (maybe_unknown_key_of_repr e r)

val enum_univ_destr_spec
  (#repr: eqtype)
  (e: enum repr)
  (t: (enum_key e -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (r: enum_repr e)
: Tot (t (enum_key_of_repr e r))

let enum_univ_destr_spec #repr e t f r =
  f (enum_key_of_repr e r)

inline_for_extraction
let id
  (t: Type0)
  (x: t)
: Tot t
= x

inline_for_extraction
let enum_key_cons_coerce
  (#repr: eqtype)
  (e: enum repr)
  (k' : string)
  (r' : repr)
  (e' : enum repr)
  (k: enum_key e')
: Pure (enum_key e)
  (requires (e == (k', r') :: e'))
  (ensures (fun _ -> True))
= (k <: string) <: enum_key e

inline_for_extraction
let enum_repr_cons_coerce_recip
  (#repr: eqtype)
  (e: enum repr)
  (k' : string)
  (r' : repr)
  (e' : enum repr)
  (k: enum_repr e)
: Pure (enum_repr e')
  (requires (e == (k', r') :: e' /\ r' <> k))
  (ensures (fun _ -> True))
= (k <: repr) <: enum_repr e'

noextract
let rec gen_enum_univ_destr_body
  (#repr: eqtype)
  (e: enum repr)
  (t: ((k: enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (r: T.term)
: Pure (T.tactic T.term)
  (requires (Cons? e))
  (ensures (fun _ -> True))
  (decreases e)
= match e with
  | ((k', r') :: e') ->
    let e' : enum repr = e' in
    let k' : enum_key e = k' in
    let fk' = f k' in
    T.bind (T.quote fk') (fun rt ->
      T.bind (T.quote id) (fun id' ->
      match e' with
      | [] -> T.return rt
      | _ ->
      T.bind (T.quote t) (fun t' ->
      T.bind (T.quote (enum_key_of_repr #repr e)) (fun myu ->
      let m_type = T.mk_app t' [T.mk_app myu [r, T.Q_Explicit], T.Q_Explicit] in
      let rt_constr = T.mk_app id' [m_type, T.Q_Explicit; rt, T.Q_Explicit] in
      T.bind (T.quote (op_Equality #repr r')) (fun eq_repr_k' ->
        let test = T.mk_app eq_repr_k' [
          (r, T.Q_Explicit);
        ]
        in
	T.bind (T.quote (enum_repr_cons_coerce_recip #repr e k' r' e')) (fun q_r_false ->
        T.bind (
          gen_enum_univ_destr_body
            e'
            (fun (k: enum_key e') ->
              t (enum_key_cons_coerce #repr e k' r' e' k)
            )
            (fun (k: enum_key e') ->
              f (enum_key_cons_coerce #repr e k' r' e' k)
            )
            (T.mk_app q_r_false [r, T.Q_Explicit])
        ) (fun t' ->
          let t'_constr = T.mk_app id' [m_type, T.Q_Explicit; t', T.Q_Explicit] in
          let m = mk_if test rt_constr t'_constr in
          T.return m
  )))))))

noextract
let rec gen_enum_univ_destr'
  (#repr: eqtype)
  (e: enum repr)
  (t: (enum_key e -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (r: enum_repr e)
: Tot (T.tactic unit)
= T.bind (T.quote r) (fun r' ->
    T.bind (
      gen_enum_univ_destr_body #repr e t f r'
    ) (fun res ->
      T.bind (T.print (T.term_to_string res)) (fun _ ->
	T.t_exact true false (T.return res)
  )))

noextract
let rec gen_enum_univ_destr
  (#repr: eqtype)
  (e: enum repr)
  (t: (enum_key e -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
: Tot (T.tactic unit)
= let open T in
  match e with
  | _ :: _ ->
    tk <-- quote (enum_repr #repr e) ;
    let x = fresh_binder tk in
    let r = T.pack (T.Tv_Var x) in
    body <-- gen_enum_univ_destr_body #repr e t f r ;
    let res = T.pack (T.Tv_Abs x body) in
    _ <-- print (term_to_string res) ;
    t_exact true false (return res)
  | _ ->
    let g (r: enum_repr #repr e) : Tot (t (enum_key_of_repr #repr e r)) =
      false_elim ()
    in
    exact_guard (quote g)

let maybe_unknown_key_or_excluded
  (#repr: eqtype)
  (e: enum repr)
  (excluded: list repr)
: Tot Type0
= (k: maybe_unknown_key e {
    match k with
    | Known _ -> True
    | Unknown r -> List.Tot.mem r excluded == false
  })

inline_for_extraction
let maybe_unknown_key_or_excluded_cons_coerce
  (#repr: eqtype)
  (e: enum repr)
  (excluded: list repr)
  (k' : string)
  (r' : repr)
  (e' : enum repr)
  (k: maybe_unknown_key_or_excluded e' (r' :: excluded))
: Pure (maybe_unknown_key_or_excluded e excluded)
  (requires (e == (k', r') :: e'))
  (ensures (fun _ -> True))
= match k with
  | Known r -> Known ((r <: string) <: enum_key e)
  | Unknown r -> Unknown ((r <: repr) <: unknown_enum_key e)

let maybe_unknown_key_or_excluded_of_repr
  (#repr: eqtype)
  (e: enum repr)
  (excluded: list repr)
  (r: repr { List.Tot.mem r excluded == false } )
: Tot (maybe_unknown_key_or_excluded e excluded)
= maybe_unknown_key_of_repr e r

noextract
let rec gen_enum_univ_destr_gen_body
  (#repr: eqtype)
  (e: enum repr)
  (excluded: list repr)
  (t: ((k: maybe_unknown_key_or_excluded e excluded) -> Tot Type0))
  (f: ((k: maybe_unknown_key_or_excluded e excluded) -> Tot (t k)))
  (r: T.term)
: Tot (T.tactic T.term)
  (decreases e)
= match e with
  | [] ->
    let g (r' : unknown_enum_key e {List.Tot.mem r' excluded == false}) : Tot (t (Unknown r')) =
      f (Unknown r')
    in
    T.bind (T.quote g) (fun g' ->
      let res = T.mk_app g' [
        (r, T.Q_Explicit)
      ]
      in
      T.return res
    )
  | ((k', r') :: e') ->
    let k' : enum_key e = k' in
    let fk' = f (Known k') in
    T.bind (T.quote fk') (fun rt ->
      T.bind (T.quote id) (fun id' ->
      T.bind (T.quote t) (fun t' ->
      T.bind (T.quote (maybe_unknown_key_or_excluded_of_repr #repr e excluded)) (fun myu ->
      let m_type = T.mk_app t' [T.mk_app myu [r, T.Q_Explicit], T.Q_Explicit] in
      T.bind (T.quote (op_Equality #repr r')) (fun eq_repr_k' ->
        let test = T.mk_app eq_repr_k' [
          (r, T.Q_Explicit);
        ]
        in
        let excluded' = r' :: excluded in
        T.bind (
          gen_enum_univ_destr_gen_body
            e'
            excluded'
            (fun (k: maybe_unknown_key_or_excluded e' excluded') ->
              t (maybe_unknown_key_or_excluded_cons_coerce e excluded k' r' e' k)
            )
            (fun (k: maybe_unknown_key_or_excluded e' excluded') ->
              f (maybe_unknown_key_or_excluded_cons_coerce e excluded k' r' e' k)
            )
            r
        ) (fun t' ->
          let rt_constr = T.mk_app id' [m_type, T.Q_Explicit; rt, T.Q_Explicit] in
          let t'_constr = T.mk_app id' [m_type, T.Q_Explicit; t', T.Q_Explicit] in
          let m = mk_if test rt_constr t'_constr in
          T.return m
  ))))))

noextract
let rec gen_enum_univ_destr_gen
  (#repr: eqtype)
  (e: enum repr)
  (t: ((k: maybe_unknown_key e) -> Tot Type0))
  (f: ((k: maybe_unknown_key e) -> Tot (t k)))
: Tot (T.tactic unit)
= let open T in (
    tk <-- quote repr ;
    let x = fresh_binder tk in
    let r = T.pack (T.Tv_Var x) in
    body <-- gen_enum_univ_destr_gen_body #repr e [] t f r ;
(*
    t' <-- quote t ;
    let body_type = mk_app t' [r, Q_Explicit] in
    let y = fresh_binder body_type in
    let y' = T.pack (T.Tv_Var y) in
    let typed_body = pack (T.Tv_Let y body y') in
    let res = T.pack (T.Tv_Abs x typed_body) in
*)
    let res = T.pack (T.Tv_Abs x body) in
    _ <-- print (term_to_string res) ;
    t_exact true false (return res)
  )

(*
inline_for_extraction
let univ_destr_exa
  (t: ((k: maybe_unknown_key exa) -> Tot Type0))
  (f: ((k: maybe_unknown_key exa) -> Tot (t k)))
: (k: UInt32.t) ->
  Tot (t (maybe_unknown_key_of_repr exa k))
//  Tot (u: t (maybe_unknown_key_of_repr exa k))
= let t' (k : maybe_unknown_key exa) : Tot Type0 = (u: t k { u == f k } ) in
  let f' (k : maybe_unknown_key exa) : Tot (t' k) = f k in
  T.synth_by_tactic (gen_enum_univ_destr_gen exa t' f')
*)

inline_for_extraction
let univ_destr_gen_exa_nondep
  (t: Type0)
  (f: ((k: maybe_unknown_key exa) -> Tot t))
: (k: UInt32.t) ->
  Tot t
= T.synth_by_tactic (gen_enum_univ_destr_gen exa (fun _ -> t) f)

inline_for_extraction
let univ_destr_gen_exa
  (t: ((k: maybe_unknown_key exa) -> Tot Type0))
  (f: ((k: maybe_unknown_key exa) -> Tot (t k)))
: (k: UInt32.t) ->
  Tot (t (maybe_unknown_key_of_repr exa k))
= T.synth_by_tactic (gen_enum_univ_destr_gen exa t f)

inline_for_extraction
let univ_destr_gen_exa_strong
  (t: ((k: maybe_unknown_key exa) -> Tot Type0))
  (f: ((k: maybe_unknown_key exa) -> Tot (t k)))
: (k: UInt32.t) ->
  Tot (y: t (maybe_unknown_key_of_repr exa k) { y == f (maybe_unknown_key_of_repr exa k) } )
= let t' (k : maybe_unknown_key exa) : Tot Type0 = (u: t k { u == f k } ) in
  let f' (k : maybe_unknown_key exa) : Tot (t' k) = f k in
  univ_destr_gen_exa t' f'

inline_for_extraction
let is_known
  (#repr: eqtype)
  (e: enum repr)
  (k: maybe_unknown_key e)
: Tot bool
= match k with
  | Known _ -> true
  | _ -> false

inline_for_extraction
let validate_exa_key_3 : P.stateful_validator (parse_enum_key parse_u32 exa) =
  let f =
    univ_destr_gen_exa
      (fun k -> (b: bool { b == Known? k } ))
      (fun k -> is_known exa k)
  in
  fun s ->
    validate_filter_st
      #UInt32.t
      #parse_u32
      parse_u32_st
      (fun r -> Known? (maybe_unknown_key_of_repr exa r))
      (fun x -> f x)
      s

inline_for_extraction
val univ_destr_exa
  (t: ((k: enum_key exa) -> Tot Type0))
  (f: ((k: enum_key exa) -> Tot (t k)))
: (r: enum_repr exa) ->
  Tot (t (enum_key_of_repr exa r))

let univ_destr_exa t f =
  T.synth_by_tactic (gen_enum_univ_destr exa t f)

inline_for_extraction
val univ_destr_exa_strong
  (t: ((k: enum_key exa) -> Tot Type0))
  (f: ((k: enum_key exa) -> Tot (t k)))
: (r: enum_repr exa) ->
  Tot (y: t (enum_key_of_repr exa r) { y == f (enum_key_of_repr exa r) } )

let univ_destr_exa_strong t f =
  let t' (k : enum_key exa) : Tot Type0 = (u: t k { u == f k } ) in
  let f' (k : enum_key exa) : Tot (t' k) = f k in
  univ_destr_exa t' f'

inline_for_extraction
let parse_filter_st'
  (#t: Type0)
  (#p: P.parser t)
  (ps: P.parser_st p)
  (f: (t -> GTot bool))
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
: Tot (P.parser_st (parse_filter p f))
= fun input ->
  match ps input with
  | Some (v, off) ->
    if f' v
    then Some (v, off)
    else None
  | _ -> None

let lift_cases
  (#repr: eqtype)
  (e: enum repr)
  (cases: (enum_key e -> Tot Type0))
  (k: maybe_unknown_key e)
: Tot Type0
= match k with
  | Known k' -> cases k'
  | _ -> False

let lift_parser_cases
  (#repr: eqtype)
  (e: enum repr)
  (cases: (enum_key e -> Tot Type0))
  (pc: ((x: enum_key e) -> Tot (P.parser (cases x))))
  (k: maybe_unknown_key e)
: Tot (P.parser (lift_cases e cases k))
= match k with
  | Known k' -> pc k'
  | _ -> P.fail_parser

inline_for_extraction
val gen_validate_sum_partial
  (t: sum)
  (p: P.parser (sum_key_repr t))
  (ps: P.parser_st p)
  (pc: ((x: sum_key t) -> Tot (P.parser (sum_cases t x))))
  (vs' : ((x: sum_key_repr t) -> Tot (P.stateful_validator (lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_unknown_key_of_repr (sum_enum t) x)))))
: Tot (P.stateful_validator (parse_sum t p pc))

let gen_validate_sum_partial t p ps pc vs' input =
  match ps input with
  | Some (v1, off1) ->
    let input2 = S.advance_slice input off1 in
    begin match vs' v1 input2 with
    | Some off2 ->
      if S.u32_add_overflows off1 off2
      then None
      else Some (UInt32.add off1 off2)
    | _ -> None
    end
  | _ -> None

inline_for_extraction
let lift_validator_cases
  (#repr: eqtype)
  (e: enum repr)
  (cases: (enum_key e -> Tot Type0))
  (pc: ((x: enum_key e) -> Tot (P.parser (cases x))))
  (vs: ((x: enum_key e) -> Tot (P.stateful_validator (pc x))))
  (k: maybe_unknown_key e)
: Tot (P.stateful_validator (lift_parser_cases e cases pc k))
= match k with
  | Known k' -> vs k'
  | _ -> P.validate_fail #False

inline_for_extraction
val repr_lift_validator_cases_exa
  (cases: (enum_key exa -> Tot Type0))
  (pc: ((x: enum_key exa) -> Tot (P.parser (cases x))))
  (vs: ((x: enum_key exa) -> Tot (P.stateful_validator (pc x))))
: Tot ((x: UInt32.t) -> Tot (P.stateful_validator (lift_parser_cases (exa) (cases) pc (maybe_unknown_key_of_repr (exa) x))))  

let repr_lift_validator_cases_exa cases pc vs x s =
  univ_destr_gen_exa
  (fun k -> P.stateful_validator (lift_parser_cases exa cases pc k))
  (lift_validator_cases exa cases pc vs)
  x
  s

let test : sum =
  make_sum exa (function
    | "K_EREF" -> UInt8.t
    | "K_HJEU" -> UInt16.t
  )

let parse_test_cases (x: sum_key test) : Tot (P.parser (sum_cases test x)) =
  match x with
    | "K_HJEU" -> parse_u16
    | "K_EREF" -> parse_u8

inline_for_extraction
val validate_test
: P.stateful_validator (parse_sum test parse_u32 parse_test_cases)

let validate_test =
  gen_validate_sum_partial
    test
    parse_u32
    parse_u32_st
    parse_test_cases
    (repr_lift_validator_cases_exa (sum_cases test) parse_test_cases
      (function
	"K_HJEU" -> validate_u16_st
      | "K_EREF" -> validate_u8_st
    ))

(*
fun input -> (ps
  `parse_then_check`
  (fun r input' ->
    if f' r
    then vs' r input' 
    else None)) input

(*

(ps
    `parse_filter_st`
    f'
  )
  `parse_then_check`
  (fun r s ->
    vs' r s
  )

  (*

(*
  univ_destr_gen_exa
    (function (Known k) -> t k | _ -> unit)
    (function (Known k) -> f k | _ -> ())
    r
    
(*
  fun __refl ->
match Prims.op_Equality (FStar.UInt32.uint_to_t 2) __refl with
   | true ->
     id (t (enum_key_of_repr exa __refl))
       (f "K_EREF")
   | false ->
     id (t (enum_key_of_repr exa __refl))
       ((fun k -> f (k <: enum_key exa)) "K_HJEU")

(*
let univ_destr_exa t f =
  let t' (k: enum_key exa) : Tot Type0 = (u: t k { u == f k } ) in
  let f' (k: enum_key exa) : Tot (t' k) = f k in
  T.synth_by_tactic (gen_enum_univ_destr exa t' f')

(*
let gen_validate_sum_partial
  (t: sum)
  (#p: P.parser (sum_key_repr t))
  (ps: P.parser_st p)
  (pc: ((x: sum_key t) -> 

noextract
let gen_validate_sum
  (t: sum)
  (#p: P.parser (sum_key_repr t))
  (ps: P.parser_st p)
  (pc: ((x: sum_key t) -> Tot (P.parser (sum_cases t x))))
  (vcs: ((x: sum_key t) -> Tot (P.stateful_validator (pc x))))
: Tot (T.tactic unit)
= T.bind (T.quote (sum_key_repr t)) (fun repr' ->
    let x = T.fresh_binder repr' in // FIXME: should be T.bind
    let x' = T.pack (T.Tv_Var x) in
    T.bind (gen_filter_key_term (sum_enum t) x') (fun check_key_body ->
      let res_1 = T.pack (T.Tv_Abs x check_key_body) in
      T.bind (T.quote (
        gen_validate_sum_partial
          t
          #p
          ps
          pc
          vcs
      )) (fun res_0 ->
        let res =
          T.mk_app res_0 [res_1, T.Q_Explicit]
        in
        T.exact_guard (T.return res)
  )))

let validate_test =
  T.synth_by_tactic (gen_validate_sum test #parse_u32 parse_u32_st parse_test_cases (function "K_EREF" -> validate_u8_st | "K_HJEU" -> validate_u16_st))
  

(*
  
  parse_tagged_union
    #(enum_key e)
    #(function "K_EREF" -> IP.parse_u
parse_enum_key IP.parse_u32 exa `parse_tagged_union` (function "K_EREF" -> IP.parse_u16 | "K_HJEU" -> IP.parse_u8))


= T.synth_by_tactic (gen_validate_sum e _ _ (function "K_EREF 


(*
let g =
    validate_filter_st
      #repr
      #p
      ps
      (fun x -> List.Tot.mem x (List.Tot.map snd e))
      f'
  in
  (
    validate_synth
      #(r: repr { List.Tot.mem r (List.Tot.map snd e) } )
      #(enum_key e)
      #(p `parse_filter` (fun r -> List.Tot.mem r (List.Tot.map snd e)))
      g
      (fun x -> enum_key_of_repr e x)
    `coerce`
    P.stateful_validator (parse_enum_key p e)
  )

noextract
let gen_validate_key
  (#repr: eqtype)
  (#p: P.parser repr)
  (ps: P.parser_st p)
  (e: enum repr)
: Tot (T.tactic unit)
= T.bind (T.quote repr) (fun repr' ->
    let x = T.fresh_binder repr' in // FIXME: should be T.bind
    let x' = T.pack (T.Tv_Var x) in
    T.bind (gen_filter_key_term e x') (fun check_key_body ->
      let res_1 = T.pack (T.Tv_Abs x check_key_body) in
      T.bind (T.quote (
        gen_validate_key_partial
          #repr
          #p
          ps
          e
      )) (fun res_0 ->
        let res =
          T.mk_app res_0 [res_1, T.Q_Explicit]
        in
        T.exact_guard (T.return res)
  )))

(*

let discr_return_type
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
  (x: repr)
: Tot Type0
= (y: bool { y == true <==> (List.Tot.mem x (List.Tot.map snd e) /\ enum_key_of_repr e x == k) } )


(*
noextract
let gen_discr_body'
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
  (x' : T.term) // (x: repr { List.Tot.mem x (List.Tot.map snd e) } )
: Tot (T.tactic T.term)
= 
  let open T in (
    true' <-- T.quote true ;
    false' <-- T.quote false ;
    r <-- gen_enum_destr #repr e x' (fun k' -> if k = k' then return true' else return false' ) false' ;
    return r
  )


(*
noextract
let gen_discr_body'
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
  (x' : T.term) // (x: repr { List.Tot.mem x (List.Tot.map snd e) } )
: Tot (T.tactic T.term)
= let open T in (
    true' <-- T.quote true ;
    false' <-- T.quote false ;
    r <-- gen_enum_destr #repr e x' (fun k' -> if k = k' then return true' else return false' ) false' ;
    return r
  )

noextract
let gen_discr_body
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
  (x: repr)
: Tot (T.tactic unit)
= let open T in (
    x' <-- T.quote x ;
    res <-- gen_discr_body' #repr e k x' ;
    exact_guard (return res)
  )

noextract
let gen_discr
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
: Tot (T.tactic unit)
= let open T in (
    ty <-- quote repr ;
    let x = fresh_binder ty in
    let x' = pack (Tv_Var x) in
    uncoerced_body <-- gen_discr_body' #repr e k x' ;
    ret_ty_0 <-- quote (discr_return_type #repr e k) ;
    let ret_ty = mk_app ret_ty_0 [x', Q_Explicit] in
    let r = fresh_binder ret_ty in
    let r' = pack (Tv_Var r) in
    let body = pack (Tv_Let r uncoerced_body r') in
    let res = pack (T.Tv_Abs x body) in
    exact_guard (return res)
  )

inline_for_extraction
let exa_discr_K_EREF'
  (x: UInt32.t)
: Pure bool
  (requires True)
  (ensures (fun y -> y == true <==> (List.Tot.mem x (List.Tot.map snd exa) /\ enum_key_of_repr exa x == "K_EREF" )))
= T.synth_by_tactic (gen_discr_body #UInt32.t exa "K_EREF" x)

inline_for_extraction
let exa_discr_K_EREF
:   (x: UInt32.t) -> Tot (discr_return_type exa "K_EREF" x) // discr_spec exa "K_EREF"
= T.synth_by_tactic (gen_discr #UInt32.t exa "K_EREF")

inline_for_extraction
let exa_discr_K_EREF
  (x: UInt32.t) -> Tot (discr_return_type exa "K_EREF" x)
= let y = 

(*

unfold
let discr_spec (#repr: eqtype) (e: enum repr) (k: enum_key e) : Tot Type0 =
  (x: repr) -> Tot (discr_return_type e k x)

inline_for_extraction
let exa_discr_K_EREF_FAIL
: discr_spec exa "K_EREF"
= T.synth_by_tactic (gen_discr #UInt32.t exa "K_EREF")

let _ : unit = T.assert_by_tactic True (let open T in u <-- quote exa_discr_K_EREF ; T.print (T.term_to_string u))

(*
(* A more general destructor *)

let destr_return_type
  (#repr: eqtype)
  (e: enum repr)
  (t: ((enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (x: repr { List.Tot.mem x (List.Tot.map snd e) } )
: Tot Type0
= (y: t (enum_key_of_repr e x) { y == f (enum_key_of_repr e x) } )

let destr_arg_type
  (#repr: eqtype)
  (e: enum repr)
  (t: ((enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
: Tot Type0
= (x: repr { List.Tot.mem x (List.Tot.map snd e) } )

let destr
  (#repr: eqtype)
  (e: enum repr)
  (t: ((enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
: Tot Type0
= (x: destr_arg_type e t f) ->
  Tot (destr_return_type e t f x)

noextract
let gen_destr_body
  (#repr: eqtype)
  (e: enum repr)
  (t: ((enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (x' : T.term) // (x: repr { List.Tot.mem x (List.Tot.map snd e) } )
: Tot (T.tactic T.term)
= let open T in (
    false_elim_0 <-- T.quote false_elim ;
    false_elim_1_0 <-- T.quote (destr_return_type #repr e t f) ;
    let false_elim_1 = T.mk_app false_elim_1_0 [x', Q_Explicit] in
    let false_elim' = T.mk_app false_elim_0 [false_elim_1, Q_Implicit] in
    u <-- T.quote () ;
    let fe = mk_app false_elim' [u, Q_Explicit] in
    r  <-- gen_enum_destr #repr e x' (fun k -> (res <-- quote (f k) ; return res)) fe ;
    return r
  )

noextract
let gen_destr
  (#repr: eqtype)
  (e: enum repr)
  (t: ((enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
: Tot (T.tactic unit)
= let open T in (
    ty <-- quote (destr_arg_type #repr e t f) ;
    let x = fresh_binder ty in
    let x' = pack (Tv_Var x) in
    body <-- gen_destr_body #repr e t f x' ;
    let res = pack (T.Tv_Abs x body) in
    exact_guard (return res)
  )

noextract
let gen_key_is
  (#repr: eqtype)
  (e: enum repr)
  (k: enum_key e)
: Tot (T.tactic unit)
= gen_destr #repr e (fun _ -> bool) (fun k' -> k' = k)

inline_for_extraction
let exa_key_is (k: enum_key exa) : ((x: UInt32.t { List.Tot.mem x (List.Tot.map snd exa) } ) -> Tot (y: bool { y == (enum_key_of_repr exa x = k) } )) =
  T.synth_by_tactic (gen_key_is #UInt32.t exa k)

#set-options "--max_ifuel 8 --max_fuel 8"

let parse_maybe_unknown_key
  (#repr: eqtype)
  (p: P.parser repr)
  (e: enum repr)
: Tot (P.parser (maybe_unknown_key e))
= p `parse_synth` (maybe_unknown_key_of_repr e)

inline_for_extraction
let validate_maybe_unknown_key
  (#repr: eqtype)
  (#p: P.parser repr)
  (vs: P.stateful_validator p)
  (e: enum repr)
: Tot (P.stateful_validator (parse_maybe_unknown_key p e))
= fun s -> vs s



(*
noextract
let gen_key_is_term
  (#repr: eqtype)
  (e: enum repr)
  (x' : T.term)
  (key: enum_key e)
: Tot (T.tactic T.term)
= T.bind (T.quote false) (fun false' ->
  T.bind (T.quote true) (fun true' ->
    T.bind (
      gen_enum_destr
       e
       x'
       (fun (key' : enum_key e) -> 
         if key = key'
         then T.return true'
         else T.return false'
       )
       false'
    ) (fun x ->
      T.return x
  )))




(*
    P.stateful_validator (parse_enum_key IP.parse_u32 exa))

(*
let validate_exa_key : P.stateful_validator (parse_enum_key IP.parse_u32 exa) =
  validate_synth
    (validate_filter_st #_ #IP.parse_u32 IP.parse_u32_st (fun x -> List.Tot.mem x (List.Tot.map snd exa)) check_exa_key)
    (enum_key_of_repr exa)


(*
    #_
    #(fun len ->
      if UInt32.lt len min || UInt32.lt max len
      then P.fail_parser
      else parse_sized p (UInt32.v len)    
    )
    (fun len ->
      if UInt32.lt len min || UInt32.lt max len
      then (P.validate_fail #t)
      else validate_sized pv len
    )

inline_for_extraction
let validate_vlbytes_nochk
  (min: UInt32.t)
  (max: UInt32.t { UInt32.v max > 0 } )
  (#t: Type0)
  (p: P.parser t)
: Tot (P.stateful_validator_nochk (parse_vlbytes min max p))
= let sz : integer_size = log256 max in
  parse_nochk_then_nochk
    #_
    #(parse_bounded_integer sz)
    (parse_bounded_integer_st_nochk sz)
    #_
    #(fun len ->
      if UInt32.lt len min || UInt32.lt max len
      then P.fail_parser
      else parse_sized p (UInt32.v len)    
    )
    (fun len s ->
      validate_sized_nochk p len s
    )


(*
  j <= UInt32.v i /\
  B.live h sl /\ (
  let b' = Seq.index (B.as_seq h sl) 0 in (
  S.live (Ghost.reveal h0) b' /\
  B.includes b.S.p b'.S.p /\ (
  let sq = S.as_seq (Ghost.reveal h0) b in
  let pl = parse_list p sq in (
  let (Some (l, _)) = pl in (
  let sq' = S.as_seq (Ghost.reveal h0) b' in
  let pb' = parse_list p sq' in (
  Some? pb' /\ (
  let (Some (lr, _)) = pb' in (
  List.Tot.length lr == List.Tot.length l - j /\
  List.Tot.index l (UInt32.v i) == List.Tot.index lr (UInt32.v i - j)
  ))))))))


val validate_list
  (#t: Type0)
  (#p: P.parser t)
  (v: P.stateful_validator p)
: P.stateful_validator (parse_list p)


(*
  HST.pop_frame ();
  res

(*





  let l : Ghost.erased (list t) =
    Ghost.elift1
      (fun () ->
	let sq = S.as_seq h1 b in
	let (Some (l, _)) = parse_list' p sq () in
	l
      )
      (Ghost.hide ())
  in
  let n : Ghost.erased nat =
    Ghost.elift1 List.Tot.length l
  in
  let inv1
    (h: HS.mem)
    (j: nat)
  : GTot Type0
  = HS.modifies_one h1.HS.tip h1 h
  in
  let inv
    (h: HS.mem)
    (j: nat)
  : GTot Type0
  = inv1 h j /\
    h.HS.tip == h1.HS.tip /\
    S.live h b /\
    B.live h sl /\ (
    let s = Seq.index (B.as_seq h sl) 0 in (
    B.includes b.S.p s.S.p /\
    S.live h s /\ (
    let sq = S.as_seq h s in
    let pl = parse_list' p sq () in (
    Some? pl /\ (
    let (Some (lr, _)) = pl in (
    j <= UInt32.v i /\
    List.Tot.length lr == Ghost.reveal n - j /\
    List.Tot.index (Ghost.reveal l) (UInt32.v i) == List.Tot.index lr (UInt32.v i - j)
    ))))))
  in
  assert (inv1 h2 0);
  assert (inv h2 0);
    (fun j ->
      let s = B.index sl 0ul in
      let s' = list_tail sv s in
      B.upd sl 0ul s';
      let h = HST.get () in
      let f () : Lemma (
	let sq' = S.as_seq h s' in
	let pl' = parse_list' p sq' () in (
	Some? pl' /\ (
	let (Some (lr', _)) = pl' in (
	List.Tot.index (Ghost.reveal l) (UInt32.v i) == List.Tot.index lr' (UInt32.v i - (UInt32.v j + 1))
      )))) =
	let sq = S.as_seq h s in
	let pl = parse_list' p sq () in
	assert (Some? pl);
	let (Some (lr, _)) = pl in
	assert (Cons? lr);
	let sq' = S.as_seq h s' in
	let pl' = parse_list' p sq' () in
	assert (Some? pl');
	let (Some (lr', _)) = pl' in
	assert (lr' == List.Tot.tl lr);
	index_tail lr (UInt32.v i - UInt32.v j)
      in
      f ()
    )
  in
  admit ()
  
  (*
  let h' = HST.get () in
  assume (inv h' (UInt32.v i));
  let res = B.index sl 0ul in
  HST.pop_frame ();
  let h = HST.get () in
  res


(*

  let correctness () : Lemma (
    let sq = S.as_seq h res in
    let (Some (v, _)) = p sq in (
    v == List.Tot.index (Ghost.reveal l) (UInt32.v i)
  )) =
    let sq = S.as_seq h res in
    let (Some (lr, _)) = parse_list' p sq () in
    list_append_index_r (Ghost.reveal ll) lr (UInt32.v i)
  in
  correctness ();
  let _ : squash (B.modifies_none h0 h) =
    assert (HS.fresh_frame h0 h1);
    assert (HS.modifies_one h1.HS.tip h1 h');
    assert (HS.popped h' h);
    modifies_tip_popped h0 h1 h' h
  in


let validate_list
  (#t: Type0)
  (#p: Ghost.erased (P.parser t))
  (v: P.stateful_validator p)
: P.stateful_validator (Ghost.elift1 (parse_list #t) p)
= fun input ->
    HST.push_frame ();
    let res = B.create 0ul 1ul in
    let valid = B.create false 1ul in
    assert (B.frameOf (S.BSlice?.p input) <> B.frameOf res);
    let h1 = HST.get () in
    let start : UInt32.t = 0ul in
    let finish : UInt32.t = S.BSlice?.len input in
    let inv
      (h: HS.mem)
      (i: nat)
      (interrupt: bool)
    : GTot Type0
    = h.HS.tip == h1.HS.tip /\
      HS.modifies h1.HS.tip h1 h /\
      
    in
    let f
      (i: UInt32.t { FStar.UInt32.(v start <= v i /\ v i < v finish) } )
    : HST.Stack bool
      (requires (fun h -> inv h (UInt32.v i) false))
      (ensures (fun h_1 b h_2 ->
	inv h_1 (UInt32.v i) false /\
	inv h_2 (UInt32.v i) b
      ))
    = let cur = B.index res 0ul in
      let s = S.advance_slice input cur in
      if S.BSlice?.len s = 0ul
      then begin
	B.upd valid 0ul true;
	true
      end else
	match v s with
	| Some off ->
	  if S.u32_add_overflows cur off
	  then true
	  else begin
	    advance_slice_advance_slice input cur off;
	    B.upd res 0ul (UInt32.add cur off);
	    false
	  end
	| _ -> true
    in
    let _ = C.Loops.interruptible_for start finish inv f in
    let final_valid = B.index valid 0ul in
    let final_result = B.index res 0ul in
    HST.pop_frame ();
    if final_valid then Some final_result else None
    


(*

let parse_sized2 (#t: Type0) (p: P.parser t) (sz: UInt16.t) = parse_sized p (UInt16.v sz)

let parse_vlbytes2 (#t: Type0) (p: P.parser t) : P.parser t =
  IP.parse_u16 `P.and_then` (parse_sized2 p)

let parse_sized4 (#t: Type0) (p: P.parser t) (sz: UInt32.t) = parse_sized p (UInt32.v sz)

let parse_vlbytes4 (#t: Type0) (p: P.parser t) : P.parser t =
  IP.parse_u32 `P.and_then` (parse_sized4 p)


let parse_vlbytes1_st
  (#t: Type0)
  (#p: Ghost.erased (P.parser t))
  (ps: P.parser_st p)
: P.parser_st (Ghost.elift1 (fun p' -> P.and_then IP.parse_u8 (parse_sized1 p')) p)
= P.


(*
let parse_vlbytes1 (#t: Type0) (p: P.parser t) : P.parser t =
  

  match IP.parse_u8 s with
  | None -> None
  | Some (len' , _) ->
    let s1 = Seq.slice s 1 (Seq.length s) in
    let len = UInt8.v len' in
    if Seq.length s1 < len
    then None
    else
      let s2 = Seq.slice s1 0 len in
      match p s2 with
      | Some (v, consumed) ->
	if consumed = len
	then Some (v, 1 + len)
	else None
      | _ -> None

(*
let pure_vlbytes_prop (n: nat) (s: nat * S.bytes) : GTot Type0 =
  let (len, pl) = s in (
    len < pow2 n /\
    Seq.length pl == len
  )

let pure_vlbytes (n: nat) : Tot Type0 = (s: (nat * S.bytes) { pure_vlbytes_prop n s } )

let parse_uint (n: nat) : 
  

let repr_psk_identifier = vlbytes
