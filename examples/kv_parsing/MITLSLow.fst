module MITLSLow
// module E = Extensions
module S = Slice
module P = Parsing
module IP = IntegerParsing

let parse_sized (#t: Type0) (p: P.parser t) (sz: nat) : P.parser t = fun s ->
  if Seq.length s < sz
  then None
  else
    match p (Seq.slice s 0 sz) with
    | Some (v, consumed) ->
      if consumed = sz
      then Some (v, consumed)
      else None
    | _ -> None

unfold
let and_then_erased
  (#t1: Type0)
  (p1: Ghost.erased (P.parser t1))
  (#t2: Type0)
  (p2: Ghost.erased (t1 -> P.parser t2))
: Ghost.erased (P.parser t2)
= Ghost.elift2 P.and_then p1 p2

let reveal_and_then_erased
  (#t1: Type0)
  (p1: Ghost.erased (P.parser t1))
  (#t2: Type0)
  (p2: Ghost.erased (t1 -> P.parser t2))
: Lemma
  (Ghost.reveal (and_then_erased p1 p2) == P.and_then (Ghost.reveal p1) (Ghost.reveal p2))
//  [SMTPat (Ghost.reveal (and_then_erased p1 p2))]
= ()

let parse_sized1 (#t: Type0) (p: P.parser t) (sz: UInt8.t) = parse_sized p (UInt8.v sz)

unfold
let parse_sized1_erased (#t: Type0) (p: Ghost.erased (P.parser t)) : Ghost.erased (UInt8.t -> P.parser t) =
  Ghost.elift1 parse_sized1 p

let reveal_parse_sized1_erased (#t: Type0) (p: Ghost.erased (P.parser t)) : Lemma
  (Ghost.reveal (parse_sized1_erased p) == parse_sized1 (Ghost.reveal p))
//  [SMTPat (Ghost.reveal (parse_sized1_erased p))]
= ()

unfold
let erased_arrow
  (#t1: Type0)
  (#t2: Type0)
  (a: Ghost.erased (t1 -> t2))
  (x: t1)
: Ghost.erased t2
= Ghost.elift1 (fun (f: (t1 -> t2)) -> f x) a

let reveal_erased_arrow
  (#t1: Type0)
  (#t2: Type0)
  (a: Ghost.erased (t1 -> t2))
  (x: t1)
: Lemma
  (Ghost.reveal (erased_arrow a x) == Ghost.reveal a x)
//  [SMTPat (Ghost.reveal (erased_arrow a x))]
= ()

let parse_vlbytes1 (#t: Type0) (p: P.parser t) : P.parser t =
  IP.parse_u8 `P.and_then` (parse_sized1 p)

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

let validate_sized1
  (#t: Type0)
  (#p: Ghost.erased (P.parser t))
  (ps: P.stateful_validator p)
  (len: UInt8.t)
: P.stateful_validator (erased_arrow (parse_sized1_erased p) len)
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
    let input'  = S.truncate_slice input len'  in
    match ps input' with
    | Some consumed ->
      let test = (consumed = len') in
      assume (test == (UInt32.v consumed = UInt32.v len' ));
      if test
      then Some consumed
      else None
    | _ -> None
  end

let parse_then_check
  (#t1: Type0)
  (#p1: Ghost.erased (P.parser t1))
  (ps1: P.parser_st p1)
  (#t2: Type0)
  (#p2: Ghost.erased (t1 -> P.parser t2))
  (ps2: ((x1: t1) -> P.stateful_validator (erased_arrow p2 x1)))
: P.stateful_validator (Ghost.elift2 P.and_then p1 p2)
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

let validate_vlbytes1
  (#t: Type0)
  (#p: Ghost.erased (P.parser t))
  (ps: P.stateful_validator p)
: P.stateful_validator (Ghost.elift1 (parse_vlbytes1 #t) p)
= let t1 = Ghost.elift1 (parse_vlbytes1 #t) p in
  let ps' : P.stateful_validator t1 =
    parse_then_check #UInt8.t #(Ghost.hide IP.parse_u8) IP.parse_u8_st (validate_sized1 ps)
  in
  ps'

module Ser = Serializing
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = FStar.Buffer

(* Parse a list, until there is nothing left to read. This parser will mostly fail EXCEPT if the whole size is known and the slice has been suitably truncated beforehand, or if the elements of the list all have a known constant size. *)

let rec parse_list_aux
  (#t: Type0)
  (p: P.parser t)
  (b: P.bytes32)
  (aux: list t)
: Tot (option (list t))
  (decreases (Seq.length b))
=
    if Seq.length b = 0
    then 
      Some aux
    else
      match p b with
      | None -> None
      | Some (v, n) ->
	if n = 0
	then None (* elements cannot be empty *)
	else
	  parse_list_aux p (Seq.slice b n (Seq.length b)) (List.Tot.append aux [v])

let parse_list
  (#t: Type0)
  (p: P.parser t)
: Tot (P.parser (list t))
= fun b ->
  match parse_list_aux p b [] with
  | Some l -> Some (l, Seq.length b)
  | _ -> None

(* No stateful parser for lists, because we do not know how to extract the resulting list -- or even the list while it is being constructed *)

let advance_slice_advance_slice
  (b: S.bslice)
  (off1: UInt32.t {UInt32.v off1 <= UInt32.v b.S.len } )
  (off2: UInt32.t {UInt32.v off2 <= UInt32.v (S.advance_slice b off1).S.len } )
: Lemma
  (requires (
    S.u32_add_overflows off1 off2 == false
  ))
  (ensures (
    S.u32_add_overflows off1 off2 == false /\
    S.advance_slice (S.advance_slice b off1) off2 == S.advance_slice b (UInt32.add off1 off2)
  ))
= let s1 = S.advance_slice b off1 in
  let s2 = S.advance_slice s1 off2 in
  B.sub_sub (S.BSlice?.p b) off1 (S.BSlice?.len s1) off2 (S.BSlice?.len s2)

(*

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
