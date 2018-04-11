module FStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = FStar.Buffer
module U32 = FStar.UInt32

noeq
type loc_aux : Type =
  | LocBuffer:
    (#t: Type) ->
    (b: B.buffer t) ->
    loc_aux
  | LocUnion:
    (l1: loc_aux) ->
    (l2: loc_aux) ->
    loc_aux

let rec loc_aux_in_addr
  (l: loc_aux)
  (r: HS.rid)
  (n: nat)
: GTot Type0
  (decreases l)
= match l with
  | LocUnion l1 l2 -> loc_aux_in_addr l1 r n /\ loc_aux_in_addr l2 r n
  | LocBuffer b ->
    B.frameOf b == r /\
    B.as_addr b == n

(* TODO: move to FStar.Set?
   Necessary to handle quantifiers *)
let set_nonempty
  (#t: eqtype)
  (s: Set.set t)
: GTot Type0
= exists (i: t) . Set.mem i s

noeq
type loc' : Type =
  | Loc:
      (whole_regions: Ghost.erased (Set.set HS.rid)) ->
      (addr_regions: Ghost.erased (Set.set HS.rid)) ->
      (addrs: (
	(r: HS.rid) ->
	Ghost (Set.set nat)
	(requires (Set.mem r (Ghost.reveal addr_regions)))
	(ensures (fun _ -> True))
      )) ->
      (aux_regions: Ghost.erased (Set.set HS.rid)) ->
      (aux_addrs: (
	(r: HS.rid) ->
	Ghost (Set.set nat)
	(requires (Set.mem r (Ghost.reveal aux_regions)))
	(ensures (fun y -> set_nonempty y))
      )) ->
      (aux: (
	(r: HS.rid) ->
	(n: nat) ->
	Ghost loc_aux
	(requires (
	  Set.mem r (Ghost.reveal aux_regions) /\
	  Set.mem n (aux_addrs r)
	))
	(ensures (fun y ->
          loc_aux_in_addr y r n
      )))) ->
      loc'

let loc = loc'

let loc_none = Loc
  (Ghost.hide (Set.empty))
  (Ghost.hide (Set.empty))
  (fun _ -> Set.empty)
  (Ghost.hide (Set.empty))
  (fun _ -> Set.empty)
  (fun _ _ -> false_elim ())

let loc_union s1 s2 =
  if StrongExcludedMiddle.strong_excluded_middle (s1 == s2)
  then s1
  else
  let addr_regions1 = Ghost.reveal (Loc?.addr_regions s1) in
  let addr_regions2 = Ghost.reveal (Loc?.addr_regions s2) in
  let addr_regions = Set.union addr_regions1 addr_regions2 in
  let addrs
    (r: HS.rid)
  : Ghost (Set.set nat)
    (requires (Set.mem r addr_regions))
    (ensures (fun _ -> True))
  = Set.union
      (if Set.mem r addr_regions1 then Loc?.addrs s1 r else Set.empty)
      (if Set.mem r addr_regions2 then Loc?.addrs s2 r else Set.empty)
  in
  let aux_regions1 = Ghost.reveal (Loc?.aux_regions s1) in
  let aux_regions2 = Ghost.reveal (Loc?.aux_regions s2) in
  let aux_regions = Set.union aux_regions1 aux_regions2 in
  let aux_addrs
    (r: HS.rid)
  : Ghost (Set.set nat)
    (requires (Set.mem r aux_regions))
    (ensures (fun y -> exists i . Set.mem i y))
  = Set.union
      (if Set.mem r aux_regions1 then Loc?.aux_addrs s1 r else Set.empty)
      (if Set.mem r aux_regions2 then Loc?.aux_addrs s2 r else Set.empty)
  in
  let aux
    (r: HS.rid)
    (n: nat)
  : Ghost loc_aux
    (requires (Set.mem r aux_regions /\ Set.mem n (aux_addrs r)))
    (ensures (fun y -> loc_aux_in_addr y r n))
  = let l1 =
      if Set.mem r aux_regions1 && Set.mem n (Loc?.aux_addrs s1 r)
      then Some (Loc?.aux s1 r n)
      else None
    in
    let l2 =
      if Set.mem r aux_regions2 && Set.mem n (Loc?.aux_addrs s2 r)
      then Some (Loc?.aux s2 r n)
      else None
    in
    match l1, l2 with
    | Some l1, Some l2 -> LocUnion l1 l2
    | Some l1, _ -> l1
    | _, Some l2 -> l2
  in
  Loc
    (Ghost.hide (Set.union (Ghost.reveal (Loc?.whole_regions s1)) (Ghost.reveal (Loc?.whole_regions s2))))
    (Ghost.hide addr_regions)
    addrs
    (Ghost.hide aux_regions)
    aux_addrs
    aux

let loc_union_idem s = ()

let loc_buffer #t b =
    Loc
      (Ghost.hide Set.empty)
      (Ghost.hide Set.empty)
      (fun _ -> Set.empty)
      (Ghost.hide (Set.singleton (B.frameOf b)))
      (fun _ -> Set.singleton (B.as_addr b))
      (fun _ _ -> LocBuffer b)

let loc_addresses r n =
  Loc
    (Ghost.hide Set.empty)
    (Ghost.hide (Set.singleton r))
    (fun _ -> n)
    (Ghost.hide Set.empty)
    (fun _ -> Set.empty)
    (fun _ _ -> false_elim ())

let loc_regions r =
  Loc
    (Ghost.hide r)
    (Ghost.hide Set.empty)
    (fun _ -> Set.empty)
    (Ghost.hide Set.empty)
    (fun _ -> Set.empty)
    (fun _ _ -> false_elim ())

let rec loc_aux_syntactically_includes
  (s1 s2: loc_aux)
: GTot Type0
  (decreases s1)
= s1 == s2 \/ (
    match s1 with
    | LocUnion sl sr -> loc_aux_syntactically_includes sl s2 \/ loc_aux_syntactically_includes sr s2
    | _ -> False
  )

let loc_aux_syntactically_includes_refl
  (s: loc_aux)
: Lemma
  (loc_aux_syntactically_includes s s)
= ()

let rec loc_aux_syntactically_includes_trans
  (s1 s2 s3: loc_aux)
: Lemma
  (requires (loc_aux_syntactically_includes s1 s2 /\ loc_aux_syntactically_includes s2 s3))
  (ensures (loc_aux_syntactically_includes s1 s3))
  (decreases s1)
= match s1 with
  | LocUnion sl sr ->
    Classical.or_elim
      #(loc_aux_syntactically_includes sl s2)
      #(loc_aux_syntactically_includes sr s2)
      #(fun _ -> loc_aux_syntactically_includes s1 s3)
      (fun _ -> loc_aux_syntactically_includes_trans sl s2 s3)
      (fun _ -> loc_aux_syntactically_includes_trans sr s2 s3)
  | _ -> ()

let loc_aux_syntactically_includes_union_r
  (s1 s2 s3: loc_aux)
: Lemma
  (requires (loc_aux_syntactically_includes s1 (LocUnion s2 s3)))
  (ensures (loc_aux_syntactically_includes s1 s2 /\ loc_aux_syntactically_includes s1 s3))
= loc_aux_syntactically_includes_trans s1 (LocUnion s2 s3) s2;
  loc_aux_syntactically_includes_trans s1 (LocUnion s2 s3) s3

(* For the sake of inclusion, we will split a buffer into its individual one-sized element buffers *)

let pointer (t: Type) = (b: B.buffer t { B.length b == 1 } )
let npointer (t: Type) = (b: B.buffer t { B.length b <= 1 } )

let gpointer_of_buffer_cell
  (#t: Type)
  (b: B.buffer t)
  (i: U32.t)
: Ghost (pointer t)
  (requires (U32.v i < B.length b))
  (ensures (fun _ -> True))
= B.sub b i 1ul

val gpointer_of_buffer_cell_gsub_buffer
  (#t: Type)
  (b: B.buffer t)
  (i1: UInt32.t)
  (len: UInt32.t)
  (i2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 + UInt32.v len <= (B.length b) /\
    UInt32.v i2 < UInt32.v len
  ))
  (ensures (
    UInt32.v i1 + UInt32.v len <= (B.length b) /\
    UInt32.v i2 < UInt32.v len /\
    gpointer_of_buffer_cell (B.sub b i1 len) i2 == gpointer_of_buffer_cell b FStar.UInt32.(i1 +^ i2)
  ))

let gpointer_of_buffer_cell_gsub_buffer #t b i1 len i2 = ()

let rec loc_aux_includes_pointer
  (s: loc_aux)
  (#t: Type)
  (p: npointer t)
: GTot Type0
= match s with
  | LocBuffer #t' b' ->
    t == t' /\ b' `B.includes` p
  | LocUnion s1 s2 -> loc_aux_includes_pointer s1 p \/ loc_aux_includes_pointer s2 p

let loc_aux_includes_buffer'
  (s: loc_aux)
  (#t: Type)
  (b: B.buffer t { B.length b > 0 } )
= (forall (i: UInt32.t) . UInt32.v i < (B.length b) ==> loc_aux_includes_pointer s (gpointer_of_buffer_cell b i))

let loc_aux_includes_buffer
  (s: loc_aux)
  (#t: Type)
  (b: B.buffer t)
: GTot Type0
= if B.length b = 0
  then loc_aux_includes_pointer s b
  else loc_aux_includes_buffer' s b

let rec loc_aux_includes_buffer_refl
  (s: loc_aux)
  (#t: Type)
  (b: B.buffer t)
: Lemma
  (requires (
    loc_aux_syntactically_includes s (LocBuffer b)
  ))
  (ensures (loc_aux_includes_buffer s b))
  (decreases s)
= match s with
  | LocUnion s1 s2 ->
    Classical.or_elim
      #(loc_aux_syntactically_includes s1 (LocBuffer b))
      #(loc_aux_syntactically_includes s2 (LocBuffer b))
      #(fun _ -> loc_aux_includes_buffer s b)
      (fun _ -> loc_aux_includes_buffer_refl s1 b)
      (fun _ -> loc_aux_includes_buffer_refl s2 b)
  | _ -> ()

let rec loc_aux_includes_pointer_trans
  (s: loc_aux)
  (#t: Type)
  (p1: npointer t)
  (p2: npointer t)
: Lemma
  (requires (loc_aux_includes_pointer s p1 /\ p1 `B.includes` p2))
  (ensures (loc_aux_includes_pointer s p2))
= match s with
  | LocUnion s1 s2 ->
    Classical.or_elim
      #(loc_aux_includes_pointer s1 p1)
      #(loc_aux_includes_pointer s2 p1)
      #(fun _ -> loc_aux_includes_pointer s p2)
      (fun _ -> loc_aux_includes_pointer_trans s1 p1 p2)
      (fun _ -> loc_aux_includes_pointer_trans s2 p1 p2)
  | LocBuffer b -> ()

let loc_aux_includes_buffer_pointer_trans
  (s: loc_aux)
  (#t: Type)
  (p1: B.buffer t)
  (p2: npointer t)
: Lemma
  (requires (loc_aux_includes_buffer s p1 /\ p1 `B.includes` p2))
  (ensures (loc_aux_includes_pointer s p2))
= if B.length p1 = 0
  then
    loc_aux_includes_pointer_trans s p1 p2
  else
    let len = B.length p1 in
    let i = B.idx p2 - B.idx p1 in
    let j = U32.uint_to_t (if i = len then len - 1 else i) in
    loc_aux_includes_pointer_trans s (gpointer_of_buffer_cell p1 j) p2

let loc_aux_includes_buffer_trans
  (s: loc_aux)
  (#t: Type)
  (p1: B.buffer t)
  (p2: B.buffer t)
: Lemma
  (requires (loc_aux_includes_buffer s p1 /\ p1 `B.includes` p2))
  (ensures (loc_aux_includes_buffer s p2))
= if B.length p2 = 0
  then loc_aux_includes_buffer_pointer_trans s p1 p2
  else
    let f
      (i: U32.t)
    : Lemma
      (requires (U32.v i < B.length p2))
      (ensures (
        U32.v i < B.length p2 /\
        loc_aux_includes_pointer s (gpointer_of_buffer_cell p2 i)
      ))
    = loc_aux_includes_buffer_pointer_trans s p1 (gpointer_of_buffer_cell p2 i)
    in
    Classical.forall_intro (Classical.move_requires f)

let rec loc_aux_includes
  (s: loc_aux)
  (s2: loc_aux)
: GTot Type0
  (decreases s2)
= match s2 with
  | LocUnion s2l s2r ->
    loc_aux_includes s s2l /\
    loc_aux_includes s s2r
  | LocBuffer b ->
    loc_aux_includes_buffer s b

let rec loc_aux_includes_refl
  (s: loc_aux)
  (s2: loc_aux)
: Lemma
  (requires (loc_aux_syntactically_includes s s2))
  (ensures (loc_aux_includes s s2))
  (decreases s2)
= match s2 with
  | LocUnion s2l s2r ->
    loc_aux_syntactically_includes_union_r s s2l s2r;
    loc_aux_includes_refl s s2l;
    loc_aux_includes_refl s s2r
  | LocBuffer b ->
    loc_aux_includes_buffer_refl s b

let loc_aux_includes_refl'
  (s: loc_aux)
: Lemma
  (loc_aux_includes s s)
= loc_aux_includes_refl s s

let rec loc_aux_includes_union_l_r
  (s s': loc_aux)
: Lemma
  (loc_aux_includes (LocUnion s s') s)
= loc_aux_includes_refl (LocUnion s s') s

let rec loc_aux_includes_union_l_l
  (s s': loc_aux)
: Lemma
  (loc_aux_includes (LocUnion s' s) s)
= loc_aux_includes_refl (LocUnion s' s) s

let rec loc_aux_includes_loc_aux_includes_pointer
  (s1: loc_aux)
  (s2: loc_aux)
  (#t: Type)
  (p: npointer t)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes_pointer s2 p))
  (ensures (loc_aux_includes_pointer s1 p))
  (decreases s2)
= match s2 with
  | LocUnion s2l s2r ->
    Classical.or_elim
      #(loc_aux_includes_pointer s2l p)
      #(loc_aux_includes_pointer s2r p)
      #(fun _ -> loc_aux_includes_pointer s1 p)
      (fun _ -> loc_aux_includes_loc_aux_includes_pointer s1 s2l p)
      (fun _ -> loc_aux_includes_loc_aux_includes_pointer s1 s2r p)
  | LocBuffer b ->
    loc_aux_includes_buffer_pointer_trans s1 b p

let loc_aux_includes_loc_aux_includes_buffer
  (s1: loc_aux)
  (s2: loc_aux)
  (#t: Type)
  (p: B.buffer t)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes_buffer s2 p))
  (ensures (loc_aux_includes_buffer s1 p))
= Classical.forall_intro (Classical.move_requires (loc_aux_includes_loc_aux_includes_pointer s1 s2 #t))

let rec loc_aux_includes_trans
  (s1 s2: loc_aux)
  (s3: loc_aux)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3))
  (ensures (loc_aux_includes s1 s3))
  (decreases s3)
= match s3 with
  | LocUnion s3l s3r ->
    loc_aux_includes_trans s1 s2 s3l;
    loc_aux_includes_trans s1 s2 s3r
  | LocBuffer b ->
    loc_aux_includes_loc_aux_includes_buffer s1 s2 b

(* the following is necessary because `decreases` messes up 2nd-order unification with `Classical.forall_intro_3` *)

let loc_aux_includes_trans'
  (s1 s2: loc_aux)
  (s3: loc_aux)
: Lemma
  ((loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3) ==> loc_aux_includes s1 s3)
= Classical.move_requires (loc_aux_includes_trans s1 s2) s3

let addrs_of_loc_weak
  (l: loc)
  (r: HS.rid)
: GTot (Set.set nat)
= if Set.mem r (Ghost.reveal (Loc?.whole_regions l))
  then Set.complement Set.empty
  else if Set.mem r (Ghost.reveal (Loc?.addr_regions l))
  then Loc?.addrs l r
  else Set.empty

let addrs_of_loc_weak_loc_union
  (l1 l2: loc)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (loc_union l1 l2) r == Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r))
  [SMTPat (addrs_of_loc_weak (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc_weak (loc_union l1 l2) r) (Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r)))

let addrs_of_loc
  (l: loc)
  (r: HS.rid)
: GTot (Set.set nat)
= Set.union
    (addrs_of_loc_weak l r)
    (if Set.mem r (Ghost.reveal (Loc?.aux_regions l)) then Loc?.aux_addrs l r else Set.empty)

let addrs_of_loc_union
  (l1 l2: loc)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (loc_union l1 l2) r == Set.union (addrs_of_loc l1 r) (addrs_of_loc l2 r))
  [SMTPat (addrs_of_loc (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc (loc_union l1 l2) r) (Set.union (addrs_of_loc l1 r) (addrs_of_loc l2 r)))

let loc_includes s1 s2 =
  let whole_regions1 = Ghost.reveal (Loc?.whole_regions s1) in
  let whole_regions2 = Ghost.reveal (Loc?.whole_regions s2) in
  let addr_regions1 = Ghost.reveal (Loc?.addr_regions s1) in
  let addr_regions2 = Ghost.reveal (Loc?.addr_regions s2) in (
    Set.subset whole_regions2 whole_regions1 /\
    Set.subset addr_regions2 (Set.union whole_regions1 addr_regions1) /\
    (
      forall (r: HS.rid) .
      (Set.mem r addr_regions2 /\ (~ (Set.mem r whole_regions1))) ==>
      Set.subset (Loc?.addrs s2 r) (Loc?.addrs s1 r)
    ) /\ (
      forall (r: HS.rid) .
      Set.subset (addrs_of_loc_weak s2 r) (addrs_of_loc_weak s1 r)
    ) /\ (
      forall (r: HS.rid) .
      Set.subset (addrs_of_loc s2 r) (addrs_of_loc s1 r)
    ) /\ (
      forall (r: HS.rid) (n: nat) .
      (Set.mem r (Ghost.reveal (Loc?.aux_regions s2)) /\ Set.mem n (Loc?.aux_addrs s2 r)) ==>
      (
        Set.mem n (addrs_of_loc_weak s1 r) \/ (
        Set.mem r (Ghost.reveal (Loc?.aux_regions s1)) /\
        Set.mem n (Loc?.aux_addrs s1 r) /\
        loc_aux_includes (Loc?.aux s1 r n) (Loc?.aux s2 r n)
  ))))

let loc_includes_refl s =
  let pre
    (r: HS.rid)
    (n: nat)
  : GTot Type0
  = Set.mem r (Ghost.reveal (Loc?.aux_regions s)) /\
    Set.mem n (Loc?.aux_addrs s r)
  in
  let post
    (r: HS.rid)
    (n: nat)
  : GTot Type0
  = pre r n /\
    loc_aux_includes (Loc?.aux s r n) (Loc?.aux s r n)
  in
  let f
    (r: HS.rid)
    (n: nat)
  : Lemma
    (requires (pre r n))
    (ensures (post r n))
  = loc_aux_includes_refl (Loc?.aux s r n) (Loc?.aux s r n)
  in
  Classical.forall_intro_2 (fun r -> Classical.move_requires (f r))

let loc_includes_trans s1 s2 s3 =
  Classical.forall_intro_3 loc_aux_includes_trans'

let loc_includes_union_r s s1 s2 = ()

let loc_includes_union_l s1 s2 s =
  let u12 = loc_union s1 s2 in
  if StrongExcludedMiddle.strong_excluded_middle (s1 == s2)
  then ()
  else begin
    Classical.forall_intro loc_aux_includes_refl';
    Classical.forall_intro_2 loc_aux_includes_union_l_l;    
    Classical.forall_intro_2 loc_aux_includes_union_l_r;
    Classical.or_elim
      #(loc_includes s1 s)
      #(loc_includes s2 s)
      #(fun _ -> loc_includes (loc_union s1 s2) s)
      (fun _ -> loc_includes_trans u12 s1 s)
      (fun _ -> loc_includes_trans u12 s2 s)
  end

let loc_includes_none s = ()

let loc_includes_gsub_buffer_r l #t b i len =
    let g = B.sub b i len in
    let f () : Lemma
      (loc_aux_includes (LocBuffer b) (LocBuffer g))
    = let pre
        (j: UInt32.t)
      : GTot Type0
      = UInt32.v j < UInt32.v len
      in
      let post
        (j: UInt32.t)
      : GTot Type0
      = pre j /\
        loc_aux_includes_pointer (LocBuffer b) (gpointer_of_buffer_cell g j)
      in
      let k
        (j: UInt32.t)
      : Lemma
        (requires (pre j))
        (ensures (post j))
      = gpointer_of_buffer_cell_gsub_buffer b i len j
      in
      Classical.forall_intro (Classical.move_requires k)
    in
    f ();
    loc_includes_trans l (loc_buffer b) (loc_buffer g)

let loc_includes_gsub_buffer_l #t b i1 len1 i2 len2 =
  let g1 = B.sub b i1 len1 in
  let g2 = B.sub b i2 len2 in
    let pre (j: UInt32.t) : GTot Type0 =
      UInt32.v j < (B.length g2)
    in
    let post (j: UInt32.t) : GTot Type0 =
      pre j /\
      g1 `B.includes` (gpointer_of_buffer_cell g2 j)
    in
    let f
      (j: UInt32.t)
    : Lemma
      (requires (pre j))
      (ensures (post j))
    = assert (gpointer_of_buffer_cell g1 (FStar.UInt32.add (FStar.UInt32.sub i2 i1) j) `B.includes` gpointer_of_buffer_cell g2 j)
    in
    Classical.forall_intro (Classical.move_requires f);
    assert (loc_aux_includes (LocBuffer g1) (LocBuffer g2))

let loc_includes_addresses_buffer #t r s p = ()

let loc_includes_region_buffer #t s b = ()

let loc_includes_region_addresses s r a = ()

let loc_includes_region_region s1 s2 = ()

let loc_includes_region_union_l l s1 s2 = ()


(** Disjointness of two buffers: we need to use this rather than
FStar.Buffer.disjoint because we want to rule out the case where a
whole buffer (entirely covering its base reference) of length n is
disjoint from its empty subbuffer at offset 0 (or n) and length 0. *)

let buffers_disjoint
  (#t1 #t2: Type)
  (b1: B.buffer t1)
  (b2: B.buffer t2)

(* Disjointness of two memory locations *)

let rec loc_aux_disjoint_buffer
  (l: loc_aux)
  (#t: Type)
  (p: B.buffer t)
: GTot Type0
  (decreases l)
= match l with
  | LocUnion ll lr ->
    loc_aux_disjoint_buffer ll p /\ loc_aux_disjoint_buffer lr p
  | LocBuffer b -> B.disjoint b p

let rec loc_aux_disjoint
  (l1 l2: loc_aux)
: GTot Type0
  (decreases l2)
= match l2 with
  | LocUnion ll lr ->
    loc_aux_disjoint l1 ll /\ loc_aux_disjoint l1 lr
  | LocBuffer b ->
    loc_aux_disjoint_buffer l1 b

let rec loc_aux_disjoint_union_l
  (ll1 lr1 l2: loc_aux)
: Lemma
  (ensures (loc_aux_disjoint (LocUnion ll1 lr1) l2 <==> (loc_aux_disjoint ll1 l2 /\ loc_aux_disjoint lr1 l2)))
  (decreases l2)
= match l2 with
  | LocUnion ll2 lr2 ->
    loc_aux_disjoint_union_l ll1 lr1 ll2;
    loc_aux_disjoint_union_l ll1 lr1 lr2
  | _ -> ()

let loc_aux_disjoint_union_r
  (l1 ll2 lr2: loc_aux)
: Lemma
  (loc_aux_disjoint l1 (LocUnion ll2 lr2) <==> (loc_aux_disjoint l1 ll2 /\ loc_aux_disjoint l1 lr2))
= ()

let rec loc_aux_size
  (l: loc_aux)
: GTot nat
= match l with
  | LocUnion l1 l2 ->
    let n1 = loc_aux_size l1 in
    let n2 = loc_aux_size l2 in
    1 + (if n1 > n2 then n1 else n2)
  | _ -> 0

let rec loc_aux_disjoint_sym
  (l1 l2: loc_aux)
: Lemma
  (ensures (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1))
  (decreases (loc_aux_size l1 + loc_aux_size l2))
= match l2 with
  | LocUnion ll lr ->
    loc_aux_disjoint_union_r l1 ll lr;
    loc_aux_disjoint_sym l1 ll;
    loc_aux_disjoint_sym l1 lr;
    loc_aux_disjoint_union_l ll lr l1
  | _ ->
    begin match l1 with
    | LocUnion ll lr ->
      loc_aux_disjoint_union_l ll lr l2;
      loc_aux_disjoint_sym ll l2;
      loc_aux_disjoint_sym lr l2;
      loc_aux_disjoint_union_r l2 ll lr
    | _ -> ()
    end

(* Same problem with decreases here *)

let loc_aux_disjoint_sym'
  (l1 l2: loc_aux)
: Lemma
  (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1)
= loc_aux_disjoint_sym l1 l2

let regions_of_loc
  (s: loc)
: GTot (Set.set HS.rid)
= Set.union
    (Ghost.reveal (Loc?.whole_regions s))
    (Set.union
      (Ghost.reveal (Loc?.addr_regions s))
      (Ghost.reveal (Loc?.aux_regions s))
    )

let regions_of_loc_loc_union
  (s1 s2: loc)
: Lemma
  (regions_of_loc (loc_union s1 s2) == regions_of_loc s1 `Set.union` regions_of_loc s2)
  [SMTPat (regions_of_loc (loc_union s1 s2))]
= assert (regions_of_loc (loc_union s1 s2) `Set.equal` (regions_of_loc s1 `Set.union` regions_of_loc s2))

let regions_of_loc_monotonic
  (s1 s2: loc)
: Lemma
  (requires (loc_includes s1 s2))
  (ensures (Set.subset (regions_of_loc s2) (regions_of_loc s1)))
= ()

let loc_disjoint'
  (l1 l2: loc)
: GTot Type0
= Set.subset (Set.intersect (regions_of_loc l1) (Ghost.reveal (Loc?.whole_regions l2))) Set.empty /\
  Set.subset (Set.intersect (regions_of_loc l2) (Ghost.reveal (Loc?.whole_regions l1))) Set.empty /\
  (forall (r: HS.rid) .
      Set.subset (Set.intersect (addrs_of_loc_weak l1 r) (addrs_of_loc l2 r)) Set.empty /\
      Set.subset (Set.intersect (addrs_of_loc l1 r) (addrs_of_loc_weak l2 r)) Set.empty
  ) /\
  (forall (r: HS.rid) (n: nat) .
    (Set.mem r (Ghost.reveal (Loc?.aux_regions l1)) /\ Set.mem n (Loc?.aux_addrs l1 r) /\
     Set.mem r (Ghost.reveal (Loc?.aux_regions l2)) /\ Set.mem n (Loc?.aux_addrs l2 r)) ==>
    loc_aux_disjoint (Loc?.aux l1 r n) (Loc?.aux l2 r n)
  )

let loc_disjoint = loc_disjoint'

let loc_disjoint_sym l1 l2 =
  Classical.forall_intro_2 loc_aux_disjoint_sym'

let loc_disjoint_none_r s = ()

let loc_disjoint_union_r s s1 s2 = ()

let rec loc_aux_disjoint_buffer_includes
  (l: loc_aux)
  (#t: Type)
  (p1: B.buffer t)
  (p2: B.buffer t)
: Lemma
  (requires (loc_aux_disjoint_buffer l p1 /\ p1 `B.includes` p2))
  (ensures (loc_aux_disjoint_buffer l p2))
  (decreases l)
= match l with
  | LocUnion ll lr ->
    loc_aux_disjoint_buffer_includes ll p1 p2;
    loc_aux_disjoint_buffer_includes lr p1 p2
  | _ -> ()

let rec loc_aux_disjoint_loc_aux_includes_pointer
  (l1 l2: loc_aux)
  (#t3: Type)
  (p3: npointer t3)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes_pointer l2 p3))
  (ensures (loc_aux_disjoint_buffer l1 p3))
  (decreases l2)
= match l2 with
  | LocUnion ll2 lr2 ->
    Classical.or_elim
      #(loc_aux_includes_pointer ll2 p3)
      #(loc_aux_includes_pointer lr2 p3)
      #(fun _ -> loc_aux_disjoint_buffer l1 p3)
      (fun _ -> loc_aux_disjoint_loc_aux_includes_pointer l1 ll2 p3)
      (fun _ -> loc_aux_disjoint_loc_aux_includes_pointer l1 lr2 p3)
  | LocBuffer b2 ->
    loc_aux_disjoint_buffer_includes l1 b2 p3

let disjoint_all_buffer_cells_disjoint_buffer
  (#t1: Type)
  (b1: B.buffer t1)
  (#t2: Type)
  (b2: B.buffer t2)
  (i: U32.t)
: Lemma
  (requires (
    0 < U32.v i /\
    U32.v i < B.length b2 /\
    B.disjoint b1 (B.sub b2 0ul i) /\
    B.disjoint b1 (B.sub b2 i (U32.sub (U32.uint_to_t (B.length b2)) i))
  ))
  (ensures (
    B.disjoint b1 b2
  ))
= ()

let loc_aux_disjoint_loc_aux_includes_buffer
  (l1 l2: loc_aux)
  (#t3: Type)
  (p3: B.buffer t3)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes_buffer l2 p3))
  (ensures (loc_aux_disjoint_buffer l1 p3))
= Classical.forall_intro (Classical.move_requires (loc_aux_disjoint_loc_aux_includes_pointer l1 l2 #t3));
  if B.length p3 = 0
  then ()
  else assume (loc_aux_disjoint_buffer l1 p3)

let rec loc_aux_disjoint_loc_aux_includes
  (l1 l2 l3: loc_aux)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes l2 l3))
  (ensures (loc_aux_disjoint l1 l3))
  (decreases l3)
= match l3 with
  | LocUnion ll3 lr3 ->
    loc_aux_disjoint_loc_aux_includes l1 l2 ll3;
    loc_aux_disjoint_loc_aux_includes l1 l2 lr3
  | LocBuffer b3 ->
    let f
      (i: UInt32.t)
    : Lemma
      (requires (
        UInt32.v i < (B.length b3)
      ))
      (ensures (
        UInt32.v i < (B.length b3) /\
        loc_aux_disjoint_pointer l1 (gpointer_of_buffer_cell b3 i)
      ))
    = loc_aux_disjoint_loc_aux_includes_pointer l1 l2 (gpointer_of_buffer_cell b3 i)
    in
    Classical.forall_intro (Classical.move_requires f)

let loc_disjoint_includes p1 p2 p1' p2' =
  regions_of_loc_monotonic p1 p1';
  regions_of_loc_monotonic p2 p2';
  let pre = //A rather brutal way to force inlining of pre and post in VC of the continuation
    (fun r n ->
      Set.mem r (Ghost.reveal (Loc?.aux_regions p1')) /\ Set.mem n (Loc?.aux_addrs p1' r) /\
      Set.mem r (Ghost.reveal (Loc?.aux_regions p2')) /\ Set.mem n (Loc?.aux_addrs p2' r))
    <: Tot ((r:HS.rid) -> (n:nat) -> GTot Type0)
  in
  let post =
    (fun r n ->
       pre r n /\
       loc_aux_disjoint (Loc?.aux p1' r n) (Loc?.aux p2' r n))
    <: Tot ((r:HS.rid) -> (n:nat) -> GTot Type0)
  in
  let f
    (r: HS.rid)
    (n: nat)
  : Lemma
    (requires (pre r n))
    (ensures (post r n))
  = let l1 = Loc?.aux p1 r n in
    let l2 = Loc?.aux p2 r n in
    let l1' = Loc?.aux p1' r n in
    let l2' = Loc?.aux p2' r n in
    loc_aux_disjoint_loc_aux_includes l1 l2 l2';
    loc_aux_disjoint_sym l1 l2';
    loc_aux_disjoint_loc_aux_includes l2' l1 l1';
    loc_aux_disjoint_sym l2' l1'
  in
  Classical.forall_intro_2 (fun r -> Classical.move_requires (f r))

let loc_disjoint_gsub_buffer #t b i1 len1 i2 len2 = ()

let loc_disjoint_addresses r1 r2 n1 n2 = ()

let loc_disjoint_buffer_addresses #t p r n = ()

let loc_disjoint_regions rs1 rs2 = ()


(** The modifies clause proper *)

(* Equality predicate on pointer contents, without quantifiers *)
let equal_values #a h (b:pointer a) h' (b':pointer a) : GTot Type0 =
  (B.live h b ==> (B.live h' b' /\ B.get h b 0 == B.get h' b' 0))

let modifies'
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= HS.modifies (regions_of_loc s) h1 h2 /\ (
    forall r . (
      HS.live_region h1 r /\
      Set.mem r (regions_of_loc s) /\
      (~ (Set.mem r (Ghost.reveal (Loc?.whole_regions s))))
    ) ==> (
      HS.live_region h2 r /\
      HS.modifies_ref r (addrs_of_loc s r) h1 h2
    )
  ) /\ (
    forall t (p: pointer t) . (
      Set.mem (B.frameOf p) (Ghost.reveal (Loc?.aux_regions s)) /\
      Set.mem (B.as_addr p) (Loc?.aux_addrs s (B.frameOf p)) /\
      (~ (Set.mem (B.as_addr p) (addrs_of_loc_weak s (B.frameOf p)))) /\
      loc_aux_disjoint_pointer (Loc?.aux s (B.frameOf p) (B.as_addr p)) p
    ) ==>
    equal_values h1 p h2 p
  )

let modifies = modifies'

let modifies_loc_regions_intro rs h1 h2 = ()

let modifies_loc_addresses_intro_weak
  (r: HS.rid)
  (s: Set.set nat)
  (l: loc)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions (Set.singleton r)) l) h1 h2 /\
    HS.modifies_ref r s h1 h2 /\
    HS.live_region h1 r /\
    loc_disjoint l (loc_regions (Set.singleton r))
  ))
  (ensures (modifies (loc_union (loc_addresses r s) l) h1 h2))
= Classical.forall_intro_2 HS.lemma_tip_top

#set-options "--z3rlimit 256"

val modifies_buffer_elim'
  (#t1: Type)
  (b: B.buffer t1)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_buffer b) p /\
    B.live h b /\
    (B.length b) > 0 /\
    modifies p h h'
  ))
  (ensures (
    B.live h' b /\
    B.as_seq h b == B.as_seq h' b
  ))

let modifies_buffer_elim' #t1 b p h h' =
  Classical.forall_intro_2 HS.lemma_tip_top;
  loc_disjoint_sym (loc_buffer b) p;
  let n = B.length b in
  begin
    assert (n > 0);
    let pre
      (i: UInt32.t)
    : GTot Type0
    = UInt32.v i < n
    in
    let post
      (i: UInt32.t)
    : GTot Type0
    = pre i /\ (
	  let q = gpointer_of_buffer_cell b i in
	  equal_values h q h' q
      )
    in
    let f
      (i: UInt32.t)
    : Lemma
      (requires (pre i))
      (ensures (post i))
    = modifies_pointer_elim p h h' (gpointer_of_buffer_cell b i)
    in
    f 0ul; // for the liveness of the whole buffer
    Classical.forall_intro (Classical.move_requires f);
    assert (buffer_readable h b ==> buffer_readable h' b);
    let g () : Lemma
      (requires (buffer_readable h b))
      (ensures (buffer_as_seq h b == buffer_as_seq h' b))
    = let s = buffer_as_seq h b in
      let s' = buffer_as_seq h' b in
      Seq.lemma_eq_intro s s';
      Seq.lemma_eq_elim s s'
    in
    Classical.move_requires g ()
  end

let modifies_buffer_elim #t1 b p h h' =
  if buffer_length b = 0ul
  then ()
  else modifies_buffer_elim' b p h h'

let modifies_reference_elim #t b p h h' =
  Classical.forall_intro_2 HS.lemma_tip_top;
  loc_disjoint_sym (loc_addresses (HS.frameOf b) (Set.singleton (HS.as_addr b))) p

let modifies_refl s h = ()

#reset-options "--z3rlimit 300 --initial_fuel 2 --initial_ifuel 2 --max_fuel 2 --max_ifuel 2"

let modifies_loc_includes s1 h h' s2 =
  admit ();
  assert_spinoff (
    forall rs r . (
      HS.modifies rs h h' /\
      HS.live_region h r /\
      (~ (Set.mem r rs))
    ) ==>
    HS.modifies_ref r Set.empty h h'
  );
  aux_addrs_nonempty s1;
  aux_addrs_nonempty s2;
  let h1 = h in
  let h2 = h' in
  assert_spinoff (HS.modifies (regions_of_loc s1) h1 h2);
  assert_spinoff (
    forall r . (
      HS.live_region h1 r /\
      Set.mem r (regions_of_loc s1) /\
      (~ (Set.mem r (Ghost.reveal (Loc?.whole_regions s1))))
    ) ==> (
      HS.live_region h2 r /\
      HS.modifies_ref r (addrs_of_loc s1 r) h1 h2
  ));
  let f
    (t: typ)
    (p: pointer t)
  : Lemma
    (requires (
      Set.mem (frameOf p) (Ghost.reveal (Loc?.aux_regions s1)) /\
      Set.mem (as_addr p) (Loc?.aux_addrs s1 (frameOf p)) /\
      (~ (Set.mem (as_addr p) (addrs_of_loc_weak s1 (frameOf p)))) /\
      loc_aux_disjoint_pointer (Loc?.aux s1 (frameOf p) (as_addr p)) p /\
      live h1 p
    ))
    (ensures (
      equal_values h1 p h2 p
    ))
  = assert_spinoff (~ (Set.mem (as_addr p) (addrs_of_loc_weak s2 (frameOf p))));
    if
      Set.mem (frameOf p) (Ghost.reveal (Loc?.aux_regions s2)) &&
      Set.mem (as_addr p) (Loc?.aux_addrs s2 (frameOf p))
    then begin
      let l1 = Loc?.aux s1 (frameOf p) (as_addr p) in
      let l2 = Loc?.aux s2 (frameOf p) (as_addr p) in
      loc_aux_disjoint_sym l1 (LocPointer p);
      loc_aux_disjoint_loc_aux_includes (LocPointer p) l1 l2;
      loc_aux_disjoint_sym (LocPointer p) l2
    end else
      ()
  in
  let g
    (t: typ)
    (p: pointer t)
  : Lemma ((Set.mem (frameOf p) (Ghost.reveal (Loc?.aux_regions s1)) /\
            Set.mem (as_addr p) (Loc?.aux_addrs s1 (frameOf p)) /\
            (~ (Set.mem (as_addr p) (addrs_of_loc_weak s1 (frameOf p)))) /\
            loc_aux_disjoint_pointer (Loc?.aux s1 (frameOf p) (as_addr p)) p /\
            live h1 p) ==> equal_values h1 p h2 p)
    = Classical.move_requires (f t) p
  in
  Classical.forall_intro_2 g  //AR: this was the same pattern as above (forall_intro_2 and move_requires, there was no g)

#set-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"
let modifies_only_live_regions_weak
  (rs: Set.set HS.rid)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions rs) l) h h' /\
    loc_disjoint (loc_regions rs) l /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))
= Classical.forall_intro_2 HS.lemma_tip_top
#set-options "--z3rlimit 40"

let modifies_regions_elim rs h h' = ()

let modifies_addresses_elim r a l h h' =
  assert (Set.equal (addrs_of_loc (loc_addresses r a) r) a);
  assert (Set.equal (addrs_of_loc l r) Set.empty)

let modifies_trans'
  (s: loc)
  (h1 h2: HS.mem)
  (h3: HS.mem)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
= ()

let modifies_trans s12 h1 h2 s23 h3 =
  let u = loc_union s12 s23 in
  modifies_loc_includes u h1 h2 s12;
  modifies_loc_includes u h2 h3 s23;
  modifies_trans' u h1 h2 h3
