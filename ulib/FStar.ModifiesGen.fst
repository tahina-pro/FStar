module FStar.ModifiesGen

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

noeq
type aloc (#al: aloc_t) (c: cls al) = | ALoc:
  (region: HS.rid) ->
  (addr: nat) ->
  (loc: option (al region addr)) ->
  aloc c

let aloc_domain (#al: aloc_t) (c: cls al) (regions: Ghost.erased (Set.set HS.rid)) (addrs: ((r: HS.rid { Set.mem r (Ghost.reveal regions) } ) -> GTot (Set.set nat))) : GTot (GSet.set (aloc c)) =
  GSet.comprehend (fun a -> Set.mem a.region (Ghost.reveal regions) && Set.mem a.addr (addrs a.region))

noeq
type loc' (#al: aloc_t u#x) (c: cls al) : Type u#x =
  | Loc:
      (regions: Ghost.erased (Set.set HS.rid)) ->
      (region_liveness_tags: Ghost.erased (Set.set HS.rid) { Ghost.reveal region_liveness_tags `Set.subset` Ghost.reveal regions } ) ->
      (addrs: (
	(r: HS.rid { Set.mem r (Ghost.reveal regions) } ) ->
	GTot (y: Set.set nat { r `Set.mem` (Ghost.reveal region_liveness_tags) ==> Set.subset (Set.complement Set.empty) y } )
      )) ->
      (aux: Ghost.erased (GSet.set (aloc c)) {
        aloc_domain c regions addrs `GSet.subset` Ghost.reveal aux /\
	Ghost.reveal aux `GSet.subset` (aloc_domain c regions (fun _ -> Set.complement Set.empty))
      } ) ->
      loc' c

let loc = loc'

let loc_none #a #c = Loc
  (Ghost.hide (Set.empty))
  (Ghost.hide (Set.empty))
  (fun _ -> Set.empty)
  (Ghost.hide GSet.empty)

let regions_of_loc
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
: GTot (Set.set HS.rid)
= Ghost.reveal (Loc?.regions s)

let addrs_of_loc_weak
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
: GTot (Set.set nat)
= if Set.mem r (regions_of_loc l)
  then Loc?.addrs l r
  else Set.empty

let addrs_of_loc_aux_pred
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
  (addr: nat)
: GTot bool
= StrongExcludedMiddle.strong_excluded_middle (exists a . GSet.mem a (Ghost.reveal (Loc?.aux l)) /\ a.region == r /\ a.addr == addr)

let addrs_of_loc_aux
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
: GTot (y: GSet.set nat { GSet.subset (GSet.intersect y (GSet.of_set (addrs_of_loc_weak l r))) GSet.empty } )
= GSet.comprehend (addrs_of_loc_aux_pred l r)
    `GSet.intersect` (GSet.of_set (Set.complement (addrs_of_loc_weak l r)))

let addrs_of_loc
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
: GTot (GSet.set nat)
= GSet.union
    (GSet.of_set (addrs_of_loc_weak l r))
    (addrs_of_loc_aux l r)

let addrs_of_loc_aux_prop
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
: Lemma
  (GSet.subset (GSet.intersect (addrs_of_loc_aux l r) (GSet.of_set (addrs_of_loc_weak l r))) GSet.empty)
  [SMTPatOr [
    [SMTPat (addrs_of_loc_aux l r)];
    [SMTPat (addrs_of_loc_weak l r)];
    [SMTPat (addrs_of_loc l r)];
  ]]
= ()

let loc_union #al #c s1 s2 =
  let regions1 = Ghost.reveal (Loc?.regions s1) in
  let regions2 = Ghost.reveal (Loc?.regions s2) in
  let regions = Set.union regions1 regions2 in
  let region_liveness_tags : Ghost.erased (Set.set HS.rid) = (Ghost.hide (Set.union (Ghost.reveal (Loc?.region_liveness_tags s1)) (Ghost.reveal (Loc?.region_liveness_tags s2)))) in
  let addrs
    (r: HS.rid { Set.mem r regions } )
  : GTot (y: Set.set nat { r `Set.mem` (Ghost.reveal region_liveness_tags) ==> Set.subset (Set.complement Set.empty) y })
  = Set.union
      (if Set.mem r regions1 then addrs_of_loc_weak s1 r else Set.empty)
      (if Set.mem r regions2 then addrs_of_loc_weak s2 r else Set.empty)
  in
  let aux = Ghost.hide
      (Ghost.reveal (Loc?.aux s1) `GSet.union` Ghost.reveal (Loc?.aux s2))
  in
  Loc
    (Ghost.hide regions)
    region_liveness_tags
    addrs
    aux

let fun_set_equal (#t: Type) (#t': eqtype) (f1 f2: (t -> GTot (Set.set t'))) : GTot Type0 =
  forall (x: t) . {:pattern (f1 x) \/ (f2 x) } f1 x `Set.equal` f2 x

let fun_set_equal_elim (#t: Type) (#t' : eqtype) (f1 f2: (t -> GTot (Set.set t'))) : Lemma
  (requires (fun_set_equal f1 f2))
  (ensures (f1 == f2))
  [SMTPat (fun_set_equal f1 f2)]
= assert (f1 `FunctionalExtensionality.gfeq` f2)

let loc_equal (#al: aloc_t) (#c: cls al) (s1 s2: loc c) : GTot Type0 =
  let Loc regions1 region_liveness_tags1 addrs1 aux1 = s1 in
  let Loc regions2 region_liveness_tags2 addrs2 aux2 = s2 in
  Ghost.reveal regions1 `Set.equal` Ghost.reveal regions2 /\
  Ghost.reveal region_liveness_tags1 `Set.equal` Ghost.reveal region_liveness_tags2 /\
  fun_set_equal (Loc?.addrs s1) (Loc?.addrs s2) /\
  Ghost.reveal (Loc?.aux s1) `GSet.equal` Ghost.reveal (Loc?.aux s2)

let loc_equal_elim (#al: aloc_t) (#c: cls al) (s1 s2: loc c) : Lemma
  (requires (loc_equal s1 s2))
  (ensures (s1 == s2))
  [SMTPat (s1 `loc_equal` s2)]
= ()

let loc_union_idem #al #c s =
  assert (loc_union s s `loc_equal` s)

let loc_union_comm #al #c s1 s2 =
  assert (loc_union s1 s2 `loc_equal` loc_union s2 s1)

let loc_union_assoc #al #c s1 s2 s3 =
  assert (loc_union s1 (loc_union s2 s3) `loc_equal` loc_union (loc_union s1 s2) s3)

let loc_union_loc_none_l #al #c s =
  assert (loc_union loc_none s `loc_equal` s)

let loc_union_loc_none_r #al #c s =
  assert (loc_union s loc_none `loc_equal` s)

let loc_of_aloc #al #c #r #n b =
    Loc
      (Ghost.hide (Set.singleton r))
      (Ghost.hide Set.empty)
      (fun _ -> Set.empty)
      (Ghost.hide (GSet.singleton (ALoc r n (Some b))))

let loc_addresses #al #c r n =
  let regions = (Ghost.hide (Set.singleton r)) in
  Loc
    regions
    (Ghost.hide Set.empty)
    (fun _ -> n)
    (Ghost.hide (aloc_domain c regions (fun _ -> n)))

let loc_regions #al #c r =
  let region_liveness_tags : Ghost.erased (Set.set HS.rid) =
    (Ghost.hide r)  
  in
  let addrs (r' : HS.rid { Set.mem r' r } ) : GTot (y: Set.set nat { r' `Set.mem` (Ghost.reveal region_liveness_tags) ==> Set.subset (Set.complement Set.empty) y } ) =
    Set.complement Set.empty
  in
  Loc
    (Ghost.hide r)
    region_liveness_tags
    addrs
    (Ghost.hide (aloc_domain c (Ghost.hide r) addrs))

let aloc_includes (#al: aloc_t) (#c: cls al) (b0 b: aloc c) : GTot Type0 =
  b0.region == b.region /\ b0.addr == b.addr /\ Some? b0.loc == Some? b.loc /\ (if Some? b0.loc && Some? b.loc then c.aloc_includes (Some?.v b0.loc) (Some?.v b.loc) else True)

let loc_aux_includes_buffer
  (#al: aloc_t) (#c: cls al)
  (s: GSet.set (aloc c))
  (b: aloc c)
: GTot Type0
  (decreases s)
= exists (b0 : aloc c) . b0 `GSet.mem` s /\ b0 `aloc_includes` b

let loc_aux_includes
  (#al: aloc_t) (#c: cls al)
  (s1 s2: GSet.set (aloc c))
: GTot Type0
  (decreases s2)
= forall (b2: aloc c) . GSet.mem b2 s2 ==> loc_aux_includes_buffer s1 b2

let loc_aux_includes_union_l
  (#al: aloc_t) (#c: cls al)
  (s1 s2 s: GSet.set (aloc c))
: Lemma
  (requires (loc_aux_includes s1 s \/ loc_aux_includes s2 s))
  (ensures (loc_aux_includes (GSet.union s1 s2) s))
  (decreases s)
= ()

let loc_aux_includes_refl
  (#al: aloc_t) (#c: cls al)
  (s: GSet.set (aloc c))
: Lemma
  (loc_aux_includes s s)
= Classical.forall_intro_3 (fun r a b -> c.aloc_includes_refl #r #a b)

let loc_aux_includes_subset
  (#al: aloc_t) (#c: cls al)
  (s1 s2: GSet.set (aloc c))
: Lemma
  (requires (s1 `GSet.subset` s2))
  (ensures (loc_aux_includes s2 s1))
= Classical.forall_intro_3 (fun r a b -> c.aloc_includes_refl #r #a b)

let loc_aux_includes_subset'
  (#al: aloc_t) (#c: cls al)
  (s1 s2: GSet.set (aloc c))
: Lemma
  (requires (s1 `GSet.subset` s2))
  (ensures (loc_aux_includes s2 s1))
  [SMTPatOr [
    [SMTPat (s1 `GSet.subset` s2)];
    [SMTPat (loc_aux_includes s2 s1)];
  ]]
= loc_aux_includes_subset s1 s2

let loc_aux_includes_union_l_r
  (#al: aloc_t) (#c: cls al)
  (s s': GSet.set (aloc c))
: Lemma
  (loc_aux_includes (GSet.union s s') s)
= loc_aux_includes_refl s;
  loc_aux_includes_union_l s s' s

let loc_aux_includes_union_l_l
  (#al: aloc_t) (#c: cls al)
  (s s': GSet.set (aloc c))
: Lemma
  (loc_aux_includes (GSet.union s' s) s)
= loc_aux_includes_refl s;
  loc_aux_includes_union_l s' s s

let loc_aux_includes_buffer_includes
  (#al: aloc_t) (#c: cls al)
  (s: GSet.set (aloc c))
  (b1 b2: aloc c)
: Lemma
  (requires (loc_aux_includes_buffer s b1 /\ b1 `aloc_includes` b2))
  (ensures (loc_aux_includes_buffer s b2))
= Classical.forall_intro_3 (fun r a b1 -> Classical.forall_intro_2 (fun b2 b3 -> Classical.move_requires (c.aloc_includes_trans #r #a b1 b2) b3))

let loc_aux_includes_loc_aux_includes_buffer
  (#al: aloc_t) (#c: cls al)
  (s1 s2: GSet.set (aloc c))
  (b: aloc c)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes_buffer s2 b))
  (ensures (loc_aux_includes_buffer s1 b))
= Classical.forall_intro_3 (fun s b1 b2 -> Classical.move_requires (loc_aux_includes_buffer_includes #al #c s b1) b2)

let loc_aux_includes_trans
  (#al: aloc_t) (#c: cls al)
  (s1 s2 s3: GSet.set (aloc c))
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3))
  (ensures (loc_aux_includes s1 s3))
= Classical.forall_intro_3 (fun r a b1 -> Classical.forall_intro_2 (fun b2 b3 -> Classical.move_requires (c.aloc_includes_trans #r #a b1 b2) b3))

let addrs_of_loc_weak_loc_union
  (#al: aloc_t) (#c: cls al)
  (l1 l2: loc c)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (loc_union l1 l2) r == Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r))
  [SMTPat (addrs_of_loc_weak (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc_weak (loc_union l1 l2) r) (Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r)))

let addrs_of_loc_union
  (#al: aloc_t) (#c: cls al)
  (l1 l2: loc c)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (loc_union l1 l2) r == GSet.union (addrs_of_loc l1 r) (addrs_of_loc l2 r))
  [SMTPat (addrs_of_loc (loc_union l1 l2) r)]
= assert (GSet.equal (addrs_of_loc (loc_union l1 l2) r) (GSet.union (addrs_of_loc l1 r) (addrs_of_loc l2 r)))

let loc_includes #al #c s1 s2 =
  let regions1 = Ghost.reveal (Loc?.regions s1) in
  let regions2 = Ghost.reveal (Loc?.regions s2) in (
    Set.subset regions2 regions1 /\
    Set.subset (Ghost.reveal (Loc?.region_liveness_tags s2)) (Ghost.reveal (Loc?.region_liveness_tags s1)) /\
    (
      forall (r: HS.rid) .
      Set.subset (addrs_of_loc_weak s2 r) (addrs_of_loc_weak s1 r)
    ) /\ (
      forall (r: HS.rid) .
      GSet.subset (addrs_of_loc s2 r) (addrs_of_loc s1 r)
    ) /\ (
      (Ghost.reveal (Loc?.aux s1)) `loc_aux_includes` (Ghost.reveal (Loc?.aux s2))
    )
  )

let loc_includes_refl #al #c s =
  loc_aux_includes_refl (Ghost.reveal (Loc?.aux s))

let loc_includes_refl'
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
: Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]
= loc_includes_refl s

let loc_includes_trans #al #c s1 s2 s3 =
  loc_aux_includes_trans (Ghost.reveal (Loc?.aux s1)) (Ghost.reveal (Loc?.aux s2)) (Ghost.reveal (Loc?.aux s3))

let loc_includes_union_r #al #c s s1 s2 = ()

let loc_includes_union_l #al #c s1 s2 s =
  let u12 = loc_union s1 s2 in
    Classical.or_elim
      #(loc_includes s1 s)
      #(loc_includes s2 s)
      #(fun _ -> loc_includes (loc_union s1 s2) s)
      (fun _ ->
        loc_aux_includes_union_l_r (Ghost.reveal (Loc?.aux s1)) (Ghost.reveal (Loc?.aux s2));
        assert (loc_includes (loc_union s1 s2) s1);
        loc_includes_trans u12 s1 s)
      (fun _ ->
        loc_aux_includes_union_l_l (Ghost.reveal (Loc?.aux s2)) (Ghost.reveal (Loc?.aux s1));
        assert (loc_includes (loc_union s1 s2) s2);
        loc_includes_trans u12 s2 s)

let loc_includes_none #al #c s = ()

let loc_includes_aloc #al #c #r #n b1 b2 = ()

let addrs_of_loc_loc_of_aloc
  (#al: aloc_t)
  (#c: cls al)
  (#r: HS.rid)
  (#a: nat)
  (p: al r a)
  (r': HS.rid)
: Lemma
  (addrs_of_loc (loc_of_aloc #_ #c p) r' `GSet.equal` (if r = r' then GSet.singleton a else GSet.empty))
  [SMTPat (addrs_of_loc (loc_of_aloc #_ #c p) r')]
= ()

let loc_includes_addresses_aloc #al #c r s #a p = ()

let loc_includes_region_aloc #al #c s #r #a b = ()

let loc_includes_region_addresses #al #c s r a = ()

let loc_includes_region_region #al #c s1 s2 = ()

let loc_includes_region_union_l #al #c l s1 s2 = ()


(* Disjointness of two memory locations *)

let aloc_disjoint (#al: aloc_t) (#c: cls al) (b1 b2: aloc c) : GTot Type0 =
  if b1.region = b2.region && b1.addr = b2.addr
  then Some? b1.loc /\ Some? b2.loc /\ c.aloc_disjoint (Some?.v b1.loc) (Some?.v b2.loc)
  else True

let aloc_disjoint_sym (#al: aloc_t) (#c: cls al) (b1 b2: aloc c) : Lemma
  (aloc_disjoint b1 b2 <==> aloc_disjoint b2 b1)
= Classical.forall_intro_2 (fun r a -> Classical.forall_intro_2 (fun b1 b2 -> c.aloc_disjoint_sym #r #a b1 b2))

let loc_aux_disjoint
  (#al: aloc_t) (#c: cls al)
  (l1 l2: GSet.set (aloc c))
: GTot Type0
= forall (b1 b2: aloc c) . (GSet.mem b1 l1 /\ GSet.mem b2 l2) ==> aloc_disjoint b1 b2

let loc_aux_disjoint_union_l
  (#al: aloc_t) (#c: cls al)
  (ll1 lr1 l2: GSet.set (aloc c))
: Lemma
  (ensures (loc_aux_disjoint (GSet.union ll1 lr1) l2 <==> (loc_aux_disjoint ll1 l2 /\ loc_aux_disjoint lr1 l2)))
= ()

let loc_aux_disjoint_union_r
  (#al: aloc_t) (#c: cls al)
  (l1 ll2 lr2: GSet.set (aloc c))
: Lemma
  (loc_aux_disjoint l1 (GSet.union ll2 lr2) <==> (loc_aux_disjoint l1 ll2 /\ loc_aux_disjoint l1 lr2))
= ()

let loc_aux_disjoint_sym
  (#al: aloc_t) (#c: cls al)
  (l1 l2: GSet.set (aloc c))
: Lemma
  (ensures (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1))
= Classical.forall_intro_2 (aloc_disjoint_sym #al #c)

let regions_of_loc_loc_union
  (#al: aloc_t) (#c: cls al)
  (s1 s2: loc c)
: Lemma
  (regions_of_loc (loc_union s1 s2) == regions_of_loc s1 `Set.union` regions_of_loc s2)
  [SMTPat (regions_of_loc (loc_union s1 s2))]
= assert (regions_of_loc (loc_union s1 s2) `Set.equal` (regions_of_loc s1 `Set.union` regions_of_loc s2))

let regions_of_loc_monotonic
  (#al: aloc_t) (#c: cls al)
  (s1 s2: loc c)
: Lemma
  (requires (loc_includes s1 s2))
  (ensures (Set.subset (regions_of_loc s2) (regions_of_loc s1)))
= ()

let loc_disjoint_region_liveness_tags (#al: aloc_t) (#c: cls al) (l1 l2: loc c) : GTot Type0 =
  Set.subset (Set.intersect (Ghost.reveal (Loc?.region_liveness_tags l1)) (Ghost.reveal (Loc?.region_liveness_tags l2))) Set.empty

let loc_disjoint_addrs (#al: aloc_t) (#c: cls al) (l1 l2: loc c) : GTot Type0 =
  (forall (r: HS.rid) .
      GSet.subset (GSet.intersect (GSet.of_set (addrs_of_loc_weak l1 r)) (addrs_of_loc l2 r)) GSet.empty /\
      GSet.subset (GSet.intersect (addrs_of_loc l1 r) (GSet.of_set (addrs_of_loc_weak l2 r))) GSet.empty
  )

let loc_disjoint_aux (#al: aloc_t) (#c: cls al) (l1 l2: loc c) : GTot Type0 =
  loc_aux_disjoint (Ghost.reveal (Loc?.aux l1)) (Ghost.reveal (Loc?.aux l2))

let loc_disjoint'
  (#al: aloc_t) (#c: cls al)
  (l1 l2: loc c)
: GTot Type0
= loc_disjoint_region_liveness_tags l1 l2 /\
  loc_disjoint_addrs l1 l2 /\
  loc_disjoint_aux l1 l2

let loc_disjoint = loc_disjoint'

let loc_disjoint_sym #al #c l1 l2 =
  Classical.forall_intro_2 (loc_aux_disjoint_sym #al #c)

let loc_disjoint_sym'
  (#al: aloc_t) (#c: cls al)
  (s1 s2: loc c)
: Lemma
  (requires (loc_disjoint s1 s2))
  (ensures (loc_disjoint s2 s1))
  [SMTPat (loc_disjoint s1 s2)]
= loc_disjoint_sym s1 s2

let loc_disjoint_none_r #al #c s = ()

let loc_disjoint_union_r #al #c s s1 s2 = ()

let aloc_disjoint_includes (#al: aloc_t) (#c: cls al) (b1 b2 b3 : aloc c) : Lemma
  (requires (aloc_disjoint b1 b2 /\ aloc_includes b2 b3))
  (ensures (aloc_disjoint b1 b3))
= if b1.region = b2.region && b1.addr = b2.addr
  then begin
    c.aloc_includes_refl (Some?.v b1.loc);
    c.aloc_disjoint_includes (Some?.v b1.loc) (Some?.v b2.loc) (Some?.v b1.loc) (Some?.v b3.loc)
  end
  else ()

let loc_aux_disjoint_loc_aux_includes
  (#al: aloc_t) (#c: cls al)
  (l1 l2 l3: GSet.set (aloc c))
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes l2 l3))
  (ensures (loc_aux_disjoint l1 l3))
= // FIXME: WHY WHY WHY do I need this assert?
  assert (forall (b1 b3: aloc c) . (GSet.mem b1 l1 /\ GSet.mem b3 l3) ==> (exists (b2: aloc c) . GSet.mem b2 l2 /\ aloc_disjoint b1 b2 /\ aloc_includes b2 b3));
  Classical.forall_intro_3 (fun b1 b2 b3 -> Classical.move_requires (aloc_disjoint_includes #al #c b1 b2) b3)

let loc_disjoint_includes #al #c p1 p2 p1' p2' =
  regions_of_loc_monotonic p1 p1';
  regions_of_loc_monotonic p2 p2';
  let l1 = Ghost.reveal (Loc?.aux p1) in
  let l2 = Ghost.reveal (Loc?.aux p2) in
  let l1' = Ghost.reveal (Loc?.aux p1') in
  let l2' = Ghost.reveal (Loc?.aux p2') in
  loc_aux_disjoint_loc_aux_includes l1 l2 l2';
  loc_aux_disjoint_sym l1 l2';
  loc_aux_disjoint_loc_aux_includes l2' l1 l1';
  loc_aux_disjoint_sym l2' l1'

let loc_disjoint_aloc_intro #al #c #r1 #a1 #r2 #b2 b1 b2 = ()

let loc_disjoint_aloc_elim #al #c #r1 #a1 #r2 #a2 b1 b2 =
  // FIXME: WHY WHY WHY this assert?
  assert (aloc_disjoint (ALoc #_ #c r1 a1 (Some b1)) (ALoc #_ #c r2 a2 (Some b2)))

let loc_disjoint_addresses_intro #al #c r1 r2 n1 n2 =
  // FIXME: WHY WHY WHY this assert?
  assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux (loc_addresses #_ #c r1 n1))) (Ghost.reveal (Loc?.aux (loc_addresses #_ #c r2 n2))))

let loc_disjoint_addresses_elim #al #c r1 r2 n1 n2 = ()

let loc_disjoint_aloc_addresses_intro #al #c #r' #a' p r n = ()

let loc_disjoint_aloc_addresses_elim #al #c #r' #a' p r n = ()

let loc_disjoint_regions #al #c rs1 rs2 =
  // FIXME: WHY WHY WHY this assert?
  assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux (loc_regions #_ #c rs1))) (Ghost.reveal (Loc?.aux (loc_regions #_ #c rs2))))

let liveness_preserved' (#al: aloc_t) (#c: cls al) (l: loc c) (h1 h2: HS.mem) : GTot Type0 =
  forall (t: Type0) (pre: Preorder.preorder t) (p: HS.mreference t pre) .
  (HS.frameOf p `Set.mem` regions_of_loc l /\ HS.as_addr p `GSet.mem` addrs_of_loc l (HS.frameOf p) /\ h1 `HS.contains` p) ==> h2 `HS.contains` p

let liveness_preserved = liveness_preserved'

let liveness_preserved_none #al #c h1 h2 = ()

let liveness_preserved_union #al #c l1 l2 h1 h2 = ()

let liveness_preserved_includes #al #c larger smaller h1 h2 = ()

let liveness_preserved_aloc #al c #r #a l h1 h2 =
  let f () : Lemma
    (requires (liveness_preserved (loc_of_aloc #_ #c l) h1 h2))
    (ensures (c.aloc_liveness_preserved l h1 h2))
  = c.aloc_liveness_preserved_intro l h1 h2 (fun _ _ _ -> ())
  in
  let g () : Lemma
    (requires (c.aloc_liveness_preserved l h1 h2))
    (ensures (liveness_preserved (loc_of_aloc #_ #c l) h1 h2))
  = Classical.forall_intro_3 (fun t pre r' -> Classical.move_requires (c.aloc_liveness_preserved_elim l h1 h2 #t #pre) r')
  in
  Classical.move_requires f ();
  Classical.move_requires g ()

let liveness_preserved_mreference #al c #t #pre b h1 h2 =
  HS.lemma_same_addr_contains ()

(** The modifies clause proper *)

let modifies_preserves_mreferences
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (t: Type) (pre: Preorder.preorder t) (p: HS.mreference t pre) .
    let r = HS.frameOf p in (
      HS.contains h1 p /\
      (Set.mem r (regions_of_loc s) ==> ~ (GSet.mem (HS.as_addr p) (addrs_of_loc s r)))
    ) ==> (
      HS.contains h2 p /\
      HS.sel h2 p == HS.sel h1 p
  ))

let modifies_preserves_mreferences_intro
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
  (f: (
    (t: Type) ->
    (pre: Preorder.preorder t) ->
    (p: HS.mreference t pre) ->
    Lemma
    (requires (
      HS.contains h1 p /\
      (Set.mem (HS.frameOf p) (regions_of_loc s) ==> ~ (GSet.mem (HS.as_addr p) (addrs_of_loc s (HS.frameOf p))))
    ))
    (ensures (HS.contains h2 p /\ HS.sel h2 p == HS.sel h1 p))
  ))
: Lemma
  (modifies_preserves_mreferences s h1 h2)
= let f'
    (t : Type)
    (pre: Preorder.preorder t)
    (p : HS.mreference t pre)
  : Lemma
    (
  (HS.contains h1 p /\ (Set.mem (HS.frameOf p) (regions_of_loc s) ==> ~ (GSet.mem (HS.as_addr p) (addrs_of_loc s (HS.frameOf p))))) ==>
    (h2 `HS.contains` p /\ h2 `HS.sel` p == h1 `HS.sel` p))
  = Classical.move_requires (f t pre) p
  in
  Classical.forall_intro_3 f'

let modifies_preserves_alocs
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (r: HS.rid) (a: nat) (b: al r a) .
    loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ALoc r a (Some b)))
    ==>
    c.aloc_preserved b h1 h2
  )

let modifies_preserves_alocs_intro
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
  (u: unit { modifies_preserves_mreferences s h1 h2 } )
  (f: (
    (r: HS.rid) ->
    (a: nat) ->
    (b: al r a) ->
    Lemma
    (requires (
      Set.mem r (regions_of_loc s) /\ 
      (~ (Set.mem a (addrs_of_loc_weak s r))) /\
      (GSet.mem a (addrs_of_loc_aux s r) /\ loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ALoc r a (Some b))))
    ))
    (ensures (c.aloc_preserved b h1 h2))
  ))
: Lemma
  (modifies_preserves_alocs s h1 h2)
= let f'
    (r: HS.rid)
    (a: nat)
    (b: al r a)
  : Lemma
    (requires (loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ALoc r a (Some b)))))
    (ensures (c.aloc_preserved b h1 h2))
  = if Set.mem r (regions_of_loc s) && (not (Set.mem a (addrs_of_loc_weak s r)))
    then begin
      if GSet.mem a (addrs_of_loc_aux s r)
      then
	Classical.move_requires (f r a) b
      else
	c.same_mreference_aloc_preserved b h1 h2 (fun a' pre' r' -> ())        
    end else if Set.mem r (regions_of_loc s)
    then begin
      assert (Set.mem a (addrs_of_loc_weak s r));
      assert (GSet.mem (ALoc r a None) (Ghost.reveal (Loc?.aux s)));
      assert (aloc_disjoint #_ #c (ALoc r a None) (ALoc r a (Some b)));
      assert False
    end
    else
      c.same_mreference_aloc_preserved b h1 h2 (fun a' pre' r' -> ())
  in
  Classical.forall_intro_3 (fun r a b -> Classical.move_requires (f' r a) b)

let modifies_preserves_regions
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= forall (r: HS.rid) . (HS.live_region h1 r /\ ~ (Set.mem r (Ghost.reveal (Loc?.region_liveness_tags s)))) ==> HS.live_region h2 r

let modifies'
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= modifies_preserves_regions s h1 h2 /\
  modifies_preserves_mreferences s h1 h2 /\
  modifies_preserves_alocs s h1 h2

let modifies = modifies'

let modifies_liveness_preserved #al #c s h1 h2 s' = ()

#reset-options "--z3rlimit 16"

let modifies_intro #al #c l h h' regions mrefs alocs =
  Classical.forall_intro (Classical.move_requires regions);
  assert (modifies_preserves_regions l h h');
  modifies_preserves_mreferences_intro l h h' (fun t pre p ->
    assert_norm (Loc?.region_liveness_tags (loc_mreference #_ #c p) == Ghost.hide Set.empty);
    assert (loc_disjoint_region_liveness_tags (loc_mreference p) l);
    // FIXME: WHY WHY WHY is this assert necessary?
    assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux (loc_mreference p))) (Ghost.reveal (Loc?.aux l)));
    mrefs t pre p
  );
  modifies_preserves_alocs_intro l h h' () (fun r a b ->
    loc_aux_disjoint_sym (Ghost.reveal (Loc?.aux l)) (Ghost.reveal (Loc?.aux (loc_of_aloc b)));
    alocs r a b
  )

#reset-options

let modifies_live_region #al #c s h1 h2 r = ()

let modifies_mreference_elim #al #c #t #pre b p h h' = ()

let modifies_aloc_elim #al #c #r #a b p h h' = ()

let modifies_refl #al #c s h =
  Classical.forall_intro_3 (fun r a b -> c.aloc_preserved_refl #r #a b h)

let modifies_loc_includes #al #c s1 h h' s2 =
  assert (modifies_preserves_mreferences s1 h h');
  Classical.forall_intro_2 (loc_aux_disjoint_sym #al #c);
  Classical.forall_intro_3 (fun l1 l2 l3 -> Classical.move_requires (loc_aux_disjoint_loc_aux_includes #al #c l1 l2) l3);
  assert (modifies_preserves_alocs s1 h h')

let modifies_trans'
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
  (h3: HS.mem)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
= Classical.forall_intro_3 (fun r a b -> Classical.move_requires (c.aloc_preserved_trans #r #a b h1 h2) h3)

let modifies_trans #al #c s12 h1 h2 s23 h3 =
  let u = loc_union s12 s23 in
  modifies_loc_includes u h1 h2 s12;
  modifies_loc_includes u h2 h3 s23;
  modifies_trans' u h1 h2 h3

let addr_unused_in_aloc_preserved
    (#al: aloc_t) (#c: cls al)
    (#r: HS.rid)
    (#a: nat)
    (b: al r a)
    (h1: HS.mem)
    (h2: HS.mem)
  : Lemma
    (requires (HS.live_region h1 r ==> a `Heap.addr_unused_in` (Map.sel h1.HS.h r)))
    (ensures (c.aloc_preserved b h1 h2))
= c.same_mreference_aloc_preserved b h1 h2 (fun a' pre r' -> assert False)

let modifies_only_live_regions_weak
  (#al: aloc_t) (#c: cls al)
  (rs: Set.set HS.rid)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions rs) l) h h' /\
    loc_disjoint (loc_regions rs) l /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))
= Classical.forall_intro_3 (fun r a b -> Classical.move_requires (addr_unused_in_aloc_preserved #al #c #r #a b h) h')

(* Restrict a set of locations along a set of regions *)

let restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
: GTot (loc c)
= let (Loc regions region_liveness_tags addrs aux) = l in
  Loc
    (Ghost.hide (Set.intersect (Ghost.reveal regions) rs))
    (Ghost.hide (Set.intersect (Ghost.reveal region_liveness_tags) rs))
    (fun r -> addrs r)
    (Ghost.hide (GSet.intersect (Ghost.reveal aux) (aloc_domain c (Ghost.hide rs) (fun r -> Set.complement Set.empty))))

let regions_of_loc_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (regions_of_loc (restrict_to_regions l rs) == Set.intersect (regions_of_loc l) rs)
  [SMTPat (regions_of_loc (restrict_to_regions l rs))]
= assert (Set.equal (regions_of_loc (restrict_to_regions l rs)) (Set.intersect (regions_of_loc l) rs))

let addrs_of_loc_weak_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))
  [SMTPat (addrs_of_loc_weak (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc_weak (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))

let addrs_of_loc_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc l r else GSet.empty))
  [SMTPat (addrs_of_loc (restrict_to_regions l rs) r)]
= assert (GSet.equal (addrs_of_loc (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc l r else GSet.empty))

let loc_includes_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes l (restrict_to_regions l rs))
= Classical.forall_intro (loc_aux_includes_refl #al #c)

let loc_includes_loc_union_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (loc_equal (loc_union (restrict_to_regions l rs) (restrict_to_regions l (Set.complement rs))) l)
= ()

let loc_includes_loc_regions_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes (loc_regions rs) (restrict_to_regions l rs))
= Classical.forall_intro (loc_aux_includes_refl #al #c)

let modifies_only_live_regions #al #c rs l h h' =
  let s = l in
  let c_rs = Set.complement rs in
  let s_rs = restrict_to_regions s rs in
  let s_c_rs = restrict_to_regions s c_rs in
  let lrs = loc_regions rs in
  loc_includes_loc_regions_restrict_to_regions s rs;
  loc_includes_union_l lrs s_c_rs s_rs;
  loc_includes_refl s_c_rs;
  loc_includes_union_l lrs s_c_rs s_c_rs;
  loc_includes_union_r (loc_union lrs s_c_rs) s_rs s_c_rs;
  loc_includes_loc_union_restrict_to_regions s rs;
  loc_includes_trans (loc_union lrs s_c_rs) (loc_union s_rs s_c_rs) s;
  modifies_loc_includes (loc_union lrs s_c_rs) h h' (loc_union lrs s);
  loc_includes_loc_regions_restrict_to_regions s c_rs;
  loc_disjoint_regions #al #c rs c_rs;
  loc_includes_refl lrs;
  loc_disjoint_includes lrs (loc_regions c_rs) lrs s_c_rs;
  modifies_only_live_regions_weak rs s_c_rs h h';
  loc_includes_restrict_to_regions s c_rs;
  modifies_loc_includes s h h' s_c_rs

let no_upd_fresh_region #al #c r l h0 h1 =
  modifies_only_live_regions (HS.mod_set (Set.singleton r)) l h0 h1

let fresh_frame_modifies #al c h0 h1 =
  modifies_intro #_ #c loc_none h0 h1
    (fun _ -> ())
    (fun _ _ _ -> ())
    (fun r a x ->
      c.same_mreference_aloc_preserved #r #a x h0 h1 (fun _ _ _ -> ()))

let modifies_fresh_frame_popped #al #c h0 h1 s h2 h3 =
  let f01 (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (c.aloc_preserved b h0 h1)
  = c.same_mreference_aloc_preserved #r #a b h0 h1 (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 f01;
  let s' = loc_union (loc_all_regions_from h1.HS.tip) s in
  modifies_loc_includes s' h0 h1 loc_none;
  let f23 (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (requires (r <> h2.HS.tip))
    (ensures (c.aloc_preserved b h2 h3))
  = c.same_mreference_aloc_preserved #r #a b h2 h3 (fun a' pre r' -> ())
  in
  let s23 = loc_region_only #al #c h2.HS.tip in
  assert (modifies_preserves_mreferences s23 h2 h3);
  modifies_preserves_alocs_intro s23 h2 h3 () (fun r a b ->
    f23 r a b
  );
  modifies_loc_includes s' h2 h3 s23;
  modifies_trans' s' h1 h2 h3;
  modifies_trans' s' h0 h1 h3;
  modifies_only_live_regions (HS.mod_set (Set.singleton h1.HS.tip)) s h0 h3

let modifies_loc_regions_intro #al #c rs h1 h2 =
  let f (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (requires (not (Set.mem r rs)))
    (ensures (c.aloc_preserved b h1 h2))
  = c.same_mreference_aloc_preserved #r #a b h1 h2 (fun a' pre r' -> ())
  in
  assert (modifies_preserves_mreferences (loc_regions #al #c rs) h1 h2);
  modifies_preserves_alocs_intro (loc_regions #_ #c rs) h1 h2 () (fun r a b ->
    f r a b
  )

let modifies_loc_addresses_intro_weak
  (#al: aloc_t) (#c: cls al)
  (r: HS.rid)
  (s: Set.set nat)
  (l: loc c)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_region_only r) l) h1 h2 /\
    HS.modifies_ref r s h1 h2 /\
    loc_disjoint l (loc_region_only r)
  ))
  (ensures (modifies (loc_union (loc_addresses r s) l) h1 h2))
= assert (forall (t: Type) (pre: Preorder.preorder t) (p: HS.mreference t pre) . ((HS.frameOf p == r /\ HS.contains h1 p /\ ~ (Set.mem (HS.as_addr p) s)) ==> (HS.contains h2 p /\ HS.sel h2 p == HS.sel h1 p))) ;
  assert (modifies_preserves_mreferences (loc_union (loc_addresses r s) l) h1 h2);
  let f (a: nat) (b: al r a) : Lemma
    (requires (not (Set.mem a s)))
    (ensures (c.aloc_preserved b h1 h2))
  = c.same_mreference_aloc_preserved #r #a b h1 h2 (fun a' pre r_ -> ())
  in
  modifies_preserves_alocs_intro (loc_union (loc_addresses r s) l) h1 h2 () (fun r' a b -> if r = r' then f a b else ()
  )

#set-options "--z3rlimit 16"

let modifies_loc_addresses_intro #al #c r s l h1 h2 =
  loc_includes_loc_regions_restrict_to_regions l (Set.singleton r);
  loc_includes_loc_union_restrict_to_regions l (Set.singleton r);
  assert (modifies (loc_union (loc_region_only r) (loc_union (restrict_to_regions l (Set.singleton r)) (restrict_to_regions l (Set.complement (Set.singleton r))))) h1 h2);
  let l' = restrict_to_regions l (Set.complement (Set.singleton r)) in
  loc_includes_refl (loc_region_only #_ #c r) ;
  loc_includes_loc_regions_restrict_to_regions l (Set.complement (Set.singleton r));
  loc_disjoint_regions #_ #c (Set.complement (Set.singleton r)) (Set.singleton r);
  loc_disjoint_includes (loc_regions #_ #c (Set.complement (Set.singleton r))) (loc_region_only r) l' (loc_region_only r);
  modifies_loc_addresses_intro_weak r s l' h1 h2;
  loc_includes_restrict_to_regions l (Set.complement (Set.singleton r))

#reset-options

let modifies_ralloc_post #al #c #a #rel i init h x h' =
  let g (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (c.aloc_preserved b h h')
  = c.same_mreference_aloc_preserved #r #a b h h' (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g

let modifies_salloc_post #al #c #a #rel init h x h' =
  let g (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (c.aloc_preserved b h h')
  = c.same_mreference_aloc_preserved #r #a b h h' (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g

let modifies_free #al #c #a #rel r m =
  let g (r': HS.rid) (a: nat) (b: al r' a) : Lemma
    (requires (r' <> HS.frameOf r \/ a <> HS.as_addr r))
    (ensures (c.aloc_preserved b m (HS.free r m)))
  = c.same_mreference_aloc_preserved #r' #a b m (HS.free r m) (fun a' pre r' -> ())
  in
  modifies_preserves_alocs_intro (loc_mreference #_ #c r) m (HS.free r m) () (fun r a b -> g r a b)

let modifies_none_modifies #al #c h1 h2
= let g (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (c.aloc_preserved b h1 h2)
  = c.same_mreference_aloc_preserved #r #a b h1 h2 (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g


let does_not_contain_addr' (h: HS.mem) (ra: HS.rid * nat) : GTot Type0 =
  forall (a: Type) (rel: Preorder.preorder a) (r: HS.mreference a rel) . {:pattern (h `HS.contains` r) } (HS.frameOf r == fst ra /\ HS.as_addr r == snd ra /\ h `HS.contains` r) ==> False

let does_not_contain_addr = does_not_contain_addr'

let not_live_region_does_not_contain_addr h ra = ()

let unused_in_does_not_contain_addr h #a #rel r = ()

let addr_unused_in_does_not_contain_addr h ra = ()

let free_does_not_contain_addr #a #rel r m x = ()

let does_not_contain_addr_elim #a #rel r m x = ()

let disjoint_addrs_of_loc_loc_disjoint
  (#al: aloc_t)
  (#c: cls al)
  (l1 l2: loc c)
: Lemma
  (requires (
    Set.subset (Set.intersect (Ghost.reveal (Loc?.region_liveness_tags l1)) (Ghost.reveal (Loc?.region_liveness_tags l2))) Set.empty /\
    (forall r . GSet.subset (GSet.intersect (addrs_of_loc l1 r) (addrs_of_loc l2 r)) GSet.empty)
  ))
  (ensures (loc_disjoint l1 l2))
= // FIXME: WHY WHY WHY do I need this assert?
  assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux l1)) (Ghost.reveal (Loc?.aux l2)))

#set-options "--z3rlimit 16"

let modifies_only_live_addresses_weak
  (#al: aloc_t) (#c: cls al)
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_addresses r a) l) h h' /\
    loc_disjoint (loc_addresses r a) l /\
    (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x))
  ))
  (ensures (modifies l h h'))
= modifies_preserves_mreferences_intro l h h' (fun t pre p ->
    if HS.frameOf p = r && not (Set.mem (HS.as_addr p) a)
    then disjoint_addrs_of_loc_loc_disjoint #_ #c (loc_mreference #_ #c p) l
    else ()
  );
  modifies_preserves_alocs_intro l h h' () (fun r' a' b' ->
    if r = r' && Set.mem a' a
    then c.same_mreference_aloc_preserved #r' #a' b' h h' (fun a_ pre_ r_ -> ())
    else ()
  )

#reset-options

(* Restrict a set of locations along a set of addresses in a given region *)

let restrict_to_addresses
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
: Ghost (loc c)
  (requires (loc_region_only r `loc_includes` l /\ Loc?.region_liveness_tags l == Ghost.hide Set.empty))
  (ensures (fun _ -> True))
= let (Loc regions _ addrs aux) = l in
  let regions' = ((Set.intersect (Ghost.reveal regions) (Set.singleton r))) in
  let addrs' (r' : HS.rid { Set.mem r' regions' } ) : GTot (Set.set nat) =
    if (* r' = r && *) Set.mem r (Ghost.reveal regions)
    then Set.intersect (addrs r) as
    else Set.empty
  in
    Loc
      (Ghost.hide regions')
      (Ghost.hide Set.empty)
      addrs'
      (Ghost.hide (GSet.intersect (Ghost.reveal aux) (aloc_domain c (Ghost.hide (Set.singleton r)) (fun _ -> as))))

let regions_of_loc_restrict_to_addresses
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l /\ Loc?.region_liveness_tags l == Ghost.hide Set.empty))
  (ensures (regions_of_loc (restrict_to_addresses l r as) == Set.intersect (regions_of_loc l) (Set.singleton r)))
  [SMTPat (regions_of_loc (restrict_to_addresses l r as))]
= assert (regions_of_loc (restrict_to_addresses l r as) `Set.equal` Set.intersect (regions_of_loc l) (Set.singleton r))

let addrs_of_loc_weak_restrict_to_addresses
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
  (r' : HS.rid)
: Lemma
  (requires (loc_region_only r `loc_includes` l /\ Loc?.region_liveness_tags l == Ghost.hide Set.empty))
  (ensures (addrs_of_loc_weak (restrict_to_addresses l r as) r' == (if r = r' then Set.intersect (addrs_of_loc_weak l r) as else Set.empty)))
  [SMTPat (addrs_of_loc_weak (restrict_to_addresses l r as) r')]
= assert (addrs_of_loc_weak (restrict_to_addresses l r as) r `Set.equal` Set.intersect (addrs_of_loc_weak l r) as)

let addrs_of_loc_restrict_to_addresses
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
  (r' : HS.rid)
: Lemma
  (requires (loc_region_only r `loc_includes` l /\ Loc?.region_liveness_tags l == Ghost.hide Set.empty))
  (ensures (addrs_of_loc (restrict_to_addresses l r as) r' == (if r = r' then GSet.intersect (addrs_of_loc l r) (GSet.of_set as) else GSet.empty)))
  [SMTPat (addrs_of_loc (restrict_to_addresses l r as) r')]
= assert (addrs_of_loc (restrict_to_addresses l r as) r `GSet.equal` GSet.intersect (addrs_of_loc l r) (GSet.of_set as));
  assert (r <> r' ==> addrs_of_loc (restrict_to_addresses l r as) r' `GSet.equal` GSet.empty)

let loc_includes_restrict_to_addresses
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l /\ Loc?.region_liveness_tags l == Ghost.hide Set.empty))
  (ensures (loc_includes l (restrict_to_addresses l r as)))
= Classical.forall_intro_2 (fun s1 s2 -> Classical.move_requires (loc_aux_includes_subset #al #c s1) s2)

#set-options "--z3rlimit 16"

let loc_includes_loc_union_restrict_to_addresses
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l /\ Loc?.region_liveness_tags l == Ghost.hide Set.empty))
  (ensures (loc_equal (loc_union (restrict_to_addresses l r as) (restrict_to_addresses l r (Set.complement as))) l))
= ()

#reset-options

let loc_includes_loc_addresses_restrict_to_addresses
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l /\ Loc?.region_liveness_tags l == Ghost.hide Set.empty))
  (ensures (loc_includes (loc_addresses r as) (restrict_to_addresses l r as)))
= Classical.forall_intro_2 (fun s1 s2 -> Classical.move_requires (loc_aux_includes_subset #al #c s1) s2)

let loc_disjoint_restrict_to_addresses
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l /\ Loc?.region_liveness_tags l == Ghost.hide Set.empty))
  (ensures (loc_addresses r as `loc_disjoint` restrict_to_addresses l r (Set.complement as)))
= disjoint_addrs_of_loc_loc_disjoint (loc_addresses r as) (restrict_to_addresses l r (Set.complement as))

val modifies_only_live_addresses_no_liveness_tag
  (#aloc: aloc_t) (#c: cls aloc)
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_addresses r a) l) h h' /\
    (~ (Set.mem r (Ghost.reveal (Loc?.region_liveness_tags l)))) /\
    (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x))
  ))
  (ensures (modifies l h h'))

let modifies_only_live_addresses_no_liveness_tag #al #c r a l h h' =
  let l_r = restrict_to_regions l (Set.singleton r) in
  assert (Ghost.reveal (Loc?.region_liveness_tags l_r) `Set.equal` Set.empty);
  let l_not_r = restrict_to_regions l (Set.complement (Set.singleton r)) in
  let l_a = restrict_to_addresses l_r r a in
  let l_r_not_a = restrict_to_addresses l_r r (Set.complement a) in
  let l_not_a = loc_union l_r_not_a l_not_r in
  let l' = loc_union (loc_addresses r a) l_not_a in
  loc_includes_loc_addresses_restrict_to_addresses l_r r a;
  loc_includes_loc_union_restrict_to_regions l (Set.singleton r);
  loc_includes_loc_union_restrict_to_addresses l_r r a;
  loc_includes_trans (loc_union (loc_union l_a l_r_not_a) l_not_r) (loc_union l_r l_not_r) l;
  loc_includes_trans (loc_union l_a l_not_a) (loc_union (loc_union l_a l_r_not_a) l_not_r) l;
  loc_includes_trans l' (loc_union l_a l_not_a) l;
  modifies_loc_includes (loc_union (loc_addresses r a) l_not_a) h h' (loc_union (loc_addresses r a) l);
  loc_disjoint_restrict_to_addresses l_r r a;
  loc_includes_loc_regions_restrict_to_regions l (Set.complement (Set.singleton r));
  loc_includes_region_addresses #al #c (Set.singleton r) r a;
  loc_disjoint_regions #al #c (Set.singleton r) (Set.complement (Set.singleton r));
  loc_disjoint_includes (loc_region_only r) (loc_regions (Set.complement (Set.singleton r))) (loc_addresses r a) l_not_r;
  loc_disjoint_union_r (loc_addresses r a) l_r_not_a l_not_r;
  modifies_only_live_addresses_weak r a l_not_a h h';
  loc_includes_restrict_to_regions l (Set.complement (Set.singleton r));
  loc_includes_restrict_to_addresses l_r r (Set.complement a);
  modifies_loc_includes l h h' l_not_a

let modifies_only_live_addresses #al #c r a l h h' =
  if Set.mem r (Ghost.reveal (Loc?.region_liveness_tags l))
  then begin
    assert (loc_includes l (loc_region_only r));
    loc_includes_region_addresses #_ #c (Set.singleton r) r a;
    loc_includes_trans l (loc_region_only r) (loc_addresses r a);
    loc_includes_refl l;
    loc_includes_union_r l (loc_addresses r a) l;
    modifies_loc_includes l h h' (loc_union (loc_addresses r a) l)
  end else modifies_only_live_addresses_no_liveness_tag r a l h h'


(* * Compositionality *)

noeq
type cls_union_aloc
  (al: (bool -> HS.rid -> nat -> Tot (Type u#x)))
  (r: HS.rid) (n: nat) : Type u#x
= | ALOC_FALSE of (al false) r n
  | ALOC_TRUE  of (al true) r n

let bool_of_cls_union_aloc
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (#r: HS.rid) (#n: nat)
  (l: cls_union_aloc al r n)
: Tot bool =
  match l with
  | ALOC_FALSE _ -> false
  | ALOC_TRUE _ -> true

let aloc_of_cls_union_aloc
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (#r: HS.rid) (#n: nat)
  (l: cls_union_aloc al r n)
: Tot ((al (bool_of_cls_union_aloc l)) r n)
= match l with
  | ALOC_FALSE x -> x
  | ALOC_TRUE x -> x

let make_cls_union_aloc
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (b: bool)
  (#r: HS.rid)
  (#n: nat)
  (l: (al b) r n)
: Tot (cls_union_aloc al r n)
= if b
  then ALOC_TRUE l
  else ALOC_FALSE l

let cls_union_aloc_includes
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (#r: HS.rid)
  (#a: nat)
  (larger smaller: cls_union_aloc al r a)
: GTot Type0 =
  bool_of_cls_union_aloc larger == bool_of_cls_union_aloc smaller /\
  (c (bool_of_cls_union_aloc larger)).aloc_includes
    (aloc_of_cls_union_aloc larger)
    (aloc_of_cls_union_aloc smaller)

let cls_union_aloc_disjoint
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (#r: HS.rid)
  (#a: nat)
  (larger smaller: cls_union_aloc al r a)
: GTot Type0 =
  bool_of_cls_union_aloc larger == bool_of_cls_union_aloc smaller /\
  (c (bool_of_cls_union_aloc larger)).aloc_disjoint
    (aloc_of_cls_union_aloc larger)
    (aloc_of_cls_union_aloc smaller)

let cls_union_aloc_preserved
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (#r: HS.rid)
  (#a: nat)
  (x: cls_union_aloc al r a)
  (h h' : HS.mem)
: GTot Type0
= (c (bool_of_cls_union_aloc x)).aloc_preserved
    (aloc_of_cls_union_aloc x)
    h
    h'

let aloc_union = cls_union_aloc

let cls_union #al c = Cls
  #(cls_union_aloc al)
  (cls_union_aloc_includes c)
  (* aloc_includes_refl *)
  (fun #r #a x ->
    (c (bool_of_cls_union_aloc x)).aloc_includes_refl (aloc_of_cls_union_aloc x))
  (* aloc_includes_trans *)
  (fun #r #a x1 x2 x3 ->
    (c (bool_of_cls_union_aloc x1)).aloc_includes_trans
      (aloc_of_cls_union_aloc x1)
      (aloc_of_cls_union_aloc x2)
      (aloc_of_cls_union_aloc x3)
  )
  (cls_union_aloc_disjoint c)
  (* aloc_disjoint_sym *)
  (fun #r #a x1 x2 ->
    if bool_of_cls_union_aloc x1 = bool_of_cls_union_aloc x2
    then
      (c (bool_of_cls_union_aloc x1)).aloc_disjoint_sym
        (aloc_of_cls_union_aloc x1)
        (aloc_of_cls_union_aloc x2)
    else ()
  )
  (* aloc_disjoint_includes *)
  (fun #r #a larger1 larger2 smaller1 smaller2 ->
    (c (bool_of_cls_union_aloc larger1)).aloc_disjoint_includes
      (aloc_of_cls_union_aloc larger1)
      (aloc_of_cls_union_aloc larger2)
      (aloc_of_cls_union_aloc smaller1)
      (aloc_of_cls_union_aloc smaller2)
  )
  (cls_union_aloc_preserved c)
  (* aloc_preserved_refl *)
  (fun #r #a x h ->
    (c (bool_of_cls_union_aloc x)).aloc_preserved_refl
      (aloc_of_cls_union_aloc x)
      h
  )
  (* aloc_preserved_trans *)
  (fun #r #a x h1 h2 h3 ->
    (c (bool_of_cls_union_aloc x)).aloc_preserved_trans
      (aloc_of_cls_union_aloc x)
      h1
      h2
      h3
  )
  (* same_mreference_aloc_preserved *)
  (fun #r #a b h1 h2 f ->
    (c (bool_of_cls_union_aloc b)).same_mreference_aloc_preserved
      (aloc_of_cls_union_aloc b)
      h1
      h2
      f
  )

let union_aux_of_aux_left_pred
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (s: GSet.set (aloc (c b)))
  (x: aloc (cls_union c))
: GTot bool
= let ALoc region addr loc = x in
  match loc with
  | None -> GSet.mem (ALoc region addr None) s
  | Some loc ->
    b = bool_of_cls_union_aloc #al #region #addr loc &&
    GSet.mem (ALoc region addr (Some (aloc_of_cls_union_aloc #al #region #addr loc))) s

let union_aux_of_aux_left
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (s: GSet.set (aloc (c b)))
: Tot (GSet.set (aloc (cls_union c)))
= GSet.comprehend (union_aux_of_aux_left_pred c b s)

let union_loc_of_loc #al c b l =
  let (Loc regions region_liveness_tags addrs aux) = l in
  let aux' : GSet.set (aloc #(cls_union_aloc al) (cls_union c)) =
    union_aux_of_aux_left c b (Ghost.reveal aux)
    `GSet.union`
    (aloc_domain (cls_union c) regions addrs)
  in
  Loc
    #(cls_union_aloc al)
    #(cls_union c)
    regions
    region_liveness_tags
    addrs
    (Ghost.hide aux')

let mem_union_aux_of_aux_left_intro
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (x: aloc (c b))
  (aux: GSet.set (aloc (c b)))
: Lemma
  (GSet.mem x aux <==> GSet.mem (ALoc x.region x.addr (if None? x.loc then None else Some (make_cls_union_aloc b (Some?.v x.loc)))) (union_aux_of_aux_left c b aux))
  [SMTPat (GSet.mem x aux)]
= ()

let mem_union_aux_of_aux_left_elim
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (x: aloc (cls_union c))
  (aux: GSet.set (aloc (c b)))
: Lemma
  (GSet.mem x (union_aux_of_aux_left c b aux) <==> (if None? x.loc then GSet.mem (ALoc x.region x.addr None) aux else (bool_of_cls_union_aloc (Some?.v x.loc) == b /\ GSet.mem (ALoc x.region x.addr (Some (aloc_of_cls_union_aloc (Some?.v x.loc)))) aux)))
  [SMTPat (GSet.mem x (union_aux_of_aux_left c b aux))]
= ()

let addrs_of_loc_union_loc_of_loc
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (l: loc (c b))
  (r: HS.rid)
: Lemma
  (addrs_of_loc (union_loc_of_loc c b l) r `GSet.equal` addrs_of_loc l r)
  [SMTPat (addrs_of_loc (union_loc_of_loc c b l) r)]
= ()

let union_loc_of_loc_none #al c b =
  assert (loc_equal #_ #(cls_union c) (union_loc_of_loc c b (loc_none #_ #(c b)))  (loc_none #_ #(cls_union c)))

let union_loc_of_loc_union #al c b l1 l2 =
  assert (loc_equal #_ #(cls_union c) (union_loc_of_loc c b (loc_union #_ #(c b) l1 l2)) (loc_union #_ #(cls_union c) (union_loc_of_loc c b l1) (union_loc_of_loc c b l2)))

let union_loc_of_loc_addresses #al c b r n =
  assert (loc_equal #_ #(cls_union c) (union_loc_of_loc c b (loc_addresses #_ #(c b) r n)) (loc_addresses #_ #(cls_union c) r n))

let union_loc_of_loc_regions #al c b r =
  assert (loc_equal #_ #(cls_union c) (union_loc_of_loc c b (loc_regions #_ #(c b) r)) (loc_regions #_ #(cls_union c) r))

#set-options "--z3rlimit 32"

let union_loc_of_loc_includes_intro
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (larger `loc_includes` smaller))
  (ensures (union_loc_of_loc c b larger `loc_includes` union_loc_of_loc c b smaller))
= let auxl = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux larger)) in
  let auxs = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux smaller)) in
  assert (forall r a . GSet.mem (ALoc r a None) auxs ==> (
    GSet.mem (ALoc r a None) (Ghost.reveal (Loc?.aux smaller)) /\
    GSet.mem (ALoc r a None) (Ghost.reveal (Loc?.aux larger)) /\
    GSet.mem (ALoc r a None) auxl
  ));
  assert (auxl `loc_aux_includes` auxs);
  let doml = aloc_domain (cls_union c) (Loc?.regions larger) (Loc?.addrs larger) in
  let doms = aloc_domain (cls_union c) (Loc?.regions smaller) (Loc?.addrs smaller) in
  assert (doml `loc_aux_includes` doms)

#set-options "--z3rlimit 16"

let union_loc_of_loc_includes_elim
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (union_loc_of_loc c b larger `loc_includes` union_loc_of_loc c b smaller))
  (ensures (larger `loc_includes` smaller))
= let auxl = Ghost.reveal (Loc?.aux larger) in
  let auxl' = union_aux_of_aux_left c b auxl in
  let auxs = Ghost.reveal (Loc?.aux smaller) in
  let auxs' = union_aux_of_aux_left c b auxs in
  let doml' = aloc_domain (cls_union c) (Loc?.regions larger) (Loc?.addrs larger) in
  let doms' = aloc_domain (cls_union c) (Loc?.regions smaller) (Loc?.addrs smaller) in
  let doml = aloc_domain (c b) (Loc?.regions larger) (Loc?.addrs larger) in
  let doms = aloc_domain (c b) (Loc?.regions smaller) (Loc?.addrs smaller) in
  let g 
    (r: HS.rid)
    (a: nat)
    (x: aloc (c b))
    (y: aloc (c b))
  : GTot Type0
  = GSet.mem y (GSet.union auxl doml) /\ y `aloc_includes` x
  in
  let g' (r: HS.rid) (a: nat) (x: aloc (c b)) : GTot Type0 =
    exists (y: aloc (c b)) . g r a x y
  in
  let f
    (r: HS.rid)
    (a: nat)
    (x: aloc (c b))
  : Lemma
    (requires (GSet.mem x auxs /\ (~ (Set.mem x.addr (addrs_of_loc_weak smaller x.region)))))
    (ensures (g' r a x))
  = let x' : aloc (cls_union c) = ALoc x.region x.addr (if None? x.loc then None else Some (make_cls_union_aloc b (Some?.v x.loc))) in
    Classical.exists_elim
      (g' r a x)
      #(aloc (cls_union c))
      #(fun y' -> GSet.mem y' (GSet.union auxl' doml') /\ y' `aloc_includes` x')
      ()
      (fun (y': aloc (cls_union c) { GSet.mem y' (GSet.union auxl' doml') /\ y' `aloc_includes` x' } ) ->
        let y : aloc (c b) = ALoc y'.region y'.addr (if None? y'.loc then None else Some (aloc_of_cls_union_aloc (Some?.v y'.loc))) in
        assert (g r a x y)
    )
  in
  let f'
    (r: HS.rid)
    (a: nat)
    (x: aloc (c b))
  : Lemma
    ((GSet.mem x auxs /\ (~ (Set.mem x.addr (addrs_of_loc_weak smaller x.region)))) ==> g' r a x)
  = Classical.move_requires (f r a) x
  in
  Classical.forall_intro_3 f';
  assert (forall (r: HS.rid) (a: nat) (x: aloc (c b)) .
    (GSet.mem x auxs /\ Set.mem x.addr (addrs_of_loc_weak smaller x.region)) ==>
    GSet.mem x (GSet.union auxl doml)
  );
  assert (larger `loc_includes` smaller)

#reset-options

let union_loc_of_loc_includes #al c b s1 s2 =
  Classical.move_requires (union_loc_of_loc_includes_elim c b s1) s2;
  Classical.move_requires (union_loc_of_loc_includes_intro c b s1) s2

#set-options "--z3rlimit 32"

let union_loc_of_loc_disjoint_intro
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (larger `loc_disjoint` smaller))
  (ensures (union_loc_of_loc c b larger `loc_disjoint` union_loc_of_loc c b smaller))
= let auxl = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux larger)) in
  let auxs = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux smaller)) in
  assert (forall (xl xs: aloc (cls_union c)) . (GSet.mem xl auxl /\ GSet.mem xs auxs) ==> (
    let xl' : aloc (c b) = ALoc xl.region xl.addr (if None? xl.loc then None else Some (aloc_of_cls_union_aloc (Some?.v xl.loc))) in
    let xs' : aloc (c b) = ALoc xs.region xs.addr (if None? xs.loc then None else Some (aloc_of_cls_union_aloc (Some?.v xs.loc))) in
    GSet.mem xl' (Ghost.reveal (Loc?.aux larger)) /\
    GSet.mem xs' (Ghost.reveal (Loc?.aux smaller)) /\
    aloc_disjoint xl' xs' /\
    aloc_disjoint xl xs
  ));
  assert (forall xl xs . (GSet.mem xl auxl /\ GSet.mem xs auxs) ==> aloc_disjoint xl xs);
  assert (auxl `loc_aux_disjoint` auxs);
  let larger' = union_loc_of_loc c b larger in
  let smaller' = union_loc_of_loc c b smaller in
  let doml = aloc_domain (cls_union c) (Loc?.regions larger) (Loc?.addrs larger) in
  let doms = aloc_domain (cls_union c) (Loc?.regions smaller) (Loc?.addrs smaller) in
  assert (forall (xl xs: aloc (cls_union c)) .
    (GSet.mem xl doml /\ GSet.mem xs auxs) ==> (
    xl.addr `Set.mem` addrs_of_loc_weak larger xl.region /\
    xs.addr `GSet.mem` addrs_of_loc smaller xs.region /\
    aloc_disjoint xl xs
  ));
  assert (doml ` loc_aux_disjoint` auxs);
  assert (forall (xl xs: aloc (cls_union c)) .
    (GSet.mem xl auxl /\ GSet.mem xs doms) ==> (
    xl.addr `GSet.mem` addrs_of_loc larger xl.region /\
    xs.addr `Set.mem` addrs_of_loc_weak smaller xs.region /\
    aloc_disjoint xl xs
  ));
  assert (auxl ` loc_aux_disjoint` doms);
  assert (loc_disjoint_aux larger' smaller')

#reset-options

let union_loc_of_loc_disjoint_elim
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (union_loc_of_loc c b larger `loc_disjoint` union_loc_of_loc c b smaller))
  (ensures (larger `loc_disjoint` smaller))
= let auxl = Ghost.reveal (Loc?.aux larger) in
  let auxl' = union_aux_of_aux_left c b auxl in
  let auxs = Ghost.reveal (Loc?.aux smaller) in
  let auxs' = union_aux_of_aux_left c b auxs in
  assert (forall (x y: aloc (c b)) . (GSet.mem x auxl /\ GSet.mem y auxs) ==> (
    let x' = ALoc x.region x.addr (if None? x.loc then None else Some (make_cls_union_aloc b (Some?.v x.loc))) in
    let y' = ALoc y.region y.addr (if None? y.loc then None else Some (make_cls_union_aloc b (Some?.v y.loc))) in
    GSet.mem x' auxl' /\ GSet.mem y' auxs' /\ (aloc_disjoint x' y' ==> aloc_disjoint x y))); 
  assert (auxl `loc_aux_disjoint` auxs)

let union_loc_of_loc_disjoint #al c b s1 s2 =
  Classical.move_requires (union_loc_of_loc_disjoint_elim c b s1) s2;
  Classical.move_requires (union_loc_of_loc_disjoint_intro c b s1) s2

#set-options "--z3rlimit 32"

let modifies_union_loc_of_loc_elim
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (l: loc (c b))
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies #_ #(cls_union c) (union_loc_of_loc c b l) h1 h2))
  (ensures (modifies #_ #(c b) l h1 h2))
= assert (modifies_preserves_regions l h1 h2);
  assert (modifies_preserves_mreferences l h1 h2);
  modifies_preserves_alocs_intro #_ #(c b) l h1 h2 () (fun r' a' b' ->
    let g
      (x: aloc (cls_union c))
    : Lemma
      (requires (
        GSet.mem a' (addrs_of_loc_aux #_ #(cls_union c) (union_loc_of_loc c b l) r') /\
        GSet.mem x (Ghost.reveal (Loc?.aux #_ #(cls_union c) (union_loc_of_loc c b l)))
      ))
      (ensures (
        aloc_disjoint #_ #(cls_union c) x (ALoc #_ #(cls_union c) r' a' (Some (make_cls_union_aloc b b')))))
    = if r' = x.region && a' = x.addr
      then begin
        let x' : aloc (c b) = ALoc #_ #(c b) r' a' (if None? x.loc then None else Some (aloc_of_cls_union_aloc (Some?.v x.loc))) in
        assert (aloc_disjoint #(al b) #(c b) x' (ALoc r' a' (Some b')))
      end else
        ()
    in
    Classical.forall_intro (Classical.move_requires g);
    assert ((cls_union c).aloc_preserved (make_cls_union_aloc b b') h1 h2)
  )

let modifies_union_loc_of_loc_intro
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (l: loc (c b))
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies #_ #(c b) l h1 h2))
  (ensures (modifies #_ #(cls_union c) (union_loc_of_loc c b l) h1 h2))
= let l' = union_loc_of_loc c b l in
  assert (modifies_preserves_regions l' h1 h2);
  assert (modifies_preserves_mreferences l' h1 h2);
  modifies_preserves_alocs_intro #_ #(cls_union c) l' h1 h2 () (fun r' a' b' ->
    let b_ = bool_of_cls_union_aloc b' in
    let a_ = aloc_of_cls_union_aloc b' in
    let ll' : aloc (cls_union c) = ALoc r' a' (Some b') in
    let ll  : aloc (c b_) = ALoc r' a' (Some a_) in
    assert (exists (x: aloc (c b)) . GSet.mem x (Ghost.reveal (Loc?.aux l)) /\
        (
        let xr = x.region in
        let xa = x.addr in
        let xl : option (al b xr xa) = x.loc in
        xr == r' /\
        xa == a' /\ (
        let xl' : option (aloc_union al r' a') = if None? xl then None else Some (make_cls_union_aloc #al b (Some?.v xl)) in
        let x' : aloc (cls_union c) = ALoc r' a' xl' in
        GSet.mem x' (Ghost.reveal (Loc?.aux l')) /\
        aloc_disjoint #_ #(cls_union c) x' ll'
    )));
    assert (b_ == b);
    assert (forall (x : aloc (c b)) . GSet.mem x (Ghost.reveal (Loc?.aux l)) ==>
        (
        let xr = x.region in
        let xa = x.addr in
        let xl : option (al b xr xa) = x.loc in
        let xl' : option (aloc_union al xr xa) = if None? xl then None else Some (make_cls_union_aloc #al b (Some?.v xl)) in
        let x' : aloc (cls_union c) = ALoc xr xa xl' in
        GSet.mem x' (Ghost.reveal (Loc?.aux l')) /\
        aloc_disjoint #_ #(cls_union c) x' ll' /\
        aloc_disjoint #_ #(c b) x ll
    ));
    assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux l)) (GSet.singleton ll))
  )

#reset-options

let modifies_union_loc_of_loc #al c b l h1 h2 =
  Classical.move_requires (modifies_union_loc_of_loc_elim c b l h1) h2;
  Classical.move_requires (modifies_union_loc_of_loc_intro c b l h1) h2

module U = FStar.Universe

let raise_aloc al r n = U.raise_t (al r n)

let raise_cls #al c = Cls #(raise_aloc u#x u#y al)
  (fun #r #a x1 x2 -> c.aloc_includes (U.downgrade_val x1) (U.downgrade_val x2))
  (fun #r #a x -> c.aloc_includes_refl (U.downgrade_val x))
  (fun #r #a x1 x2 x3 -> c.aloc_includes_trans (U.downgrade_val x1) (U.downgrade_val x2) (U.downgrade_val x3))
  (fun #r #a x1 x2 -> c.aloc_disjoint (U.downgrade_val x1) (U.downgrade_val x2))
  (fun #r #a x1 x2 -> c.aloc_disjoint_sym (U.downgrade_val x1) (U.downgrade_val x2))
  (fun #r #a larger1 larger2 smaller1 smaller2 -> c.aloc_disjoint_includes (U.downgrade_val larger1) (U.downgrade_val larger2) (U.downgrade_val smaller1) (U.downgrade_val smaller2))
  (fun #r #a x h1 h2 -> c.aloc_preserved (U.downgrade_val x) h1 h2)
  (fun #r #a x h -> c.aloc_preserved_refl (U.downgrade_val x) h)
  (fun #r #a x h1 h2 h3 -> c.aloc_preserved_trans (U.downgrade_val x) h1 h2 h3)
  (fun #r #a b h1 h2 f -> c.same_mreference_aloc_preserved (U.downgrade_val b) h1 h2 f)

let downgrade_aloc (#al: aloc_t u#a) (#c: cls al) (a: aloc (raise_cls u#a u#b c)) : Tot (aloc c) =
  let ALoc region addr x = a in
  ALoc region addr (if None? x then None else Some (U.downgrade_val (Some?.v x)))

let upgrade_aloc (#al: aloc_t u#a) (#c: cls al) (a: aloc c) : Tot (aloc (raise_cls u#a u#b c)) =
  let ALoc region addr x = a in
  ALoc region addr (if None? x then None else Some (U.raise_val (Some?.v x)))

let downgrade_aloc_upgrade_aloc (#al: aloc_t u#a) (#c: cls al) (a: aloc c) : Lemma
  (downgrade_aloc (upgrade_aloc u#a u#b a) == a)
  [SMTPat (downgrade_aloc (upgrade_aloc u#a u#b a))]
= ()

let upgrade_aloc_downgrade_aloc (#al: aloc_t u#a) (#c: cls al) (a: aloc (raise_cls u#a u#b c)) : Lemma
  (upgrade_aloc (downgrade_aloc a) == a)
  [SMTPat (upgrade_aloc u#a u#b (downgrade_aloc a))]
= ()

let raise_loc_aux_pred
  (#al: aloc_t u#a)
  (c: cls al)
  (aux: Ghost.erased (GSet.set (aloc c)))
  (a: aloc (raise_cls u#a u#b c))
: GTot bool
= GSet.mem (downgrade_aloc a) (Ghost.reveal aux)

let raise_loc #al #c l =
  let (Loc regions region_liveness_tags addrs aux) = l in
  Loc
    regions
    region_liveness_tags
    addrs
    (Ghost.hide (GSet.comprehend (raise_loc_aux_pred c aux)))

let raise_loc_none #al #c =
  assert (raise_loc u#x u#y (loc_none #_ #c) `loc_equal` loc_none)

let raise_loc_union #al #c l1 l2 =
  assert (raise_loc u#x u#y (loc_union l1 l2) `loc_equal` loc_union (raise_loc l1) (raise_loc l2))

let raise_loc_addresses #al #c r a =
  assert (raise_loc u#x u#y (loc_addresses #_ #c r a) `loc_equal` loc_addresses r a)

let raise_loc_regions #al #c r =
  assert (raise_loc u#x u#y (loc_regions #_ #c r) `loc_equal` loc_regions r)

#set-options "--z3rlimit 16"

let raise_loc_includes #al #c l1 l2 =
  let l1' = raise_loc l1 in
  let l2' = raise_loc l2 in
  assert (forall (x: aloc (raise_cls c)) . GSet.mem x (Ghost.reveal (Loc?.aux l1')) <==> GSet.mem (downgrade_aloc x) (Ghost.reveal (Loc?.aux l1)));
  assert (forall (x: aloc (raise_cls c)) . GSet.mem x (Ghost.reveal (Loc?.aux l2')) <==> GSet.mem (downgrade_aloc x) (Ghost.reveal (Loc?.aux l2)));
  assert (forall (x: aloc c) . GSet.mem x (Ghost.reveal (Loc?.aux l1)) <==> GSet.mem (upgrade_aloc x) (Ghost.reveal (Loc?.aux l1')));
  assert (forall (x: aloc c) . GSet.mem x (Ghost.reveal (Loc?.aux l2)) <==> GSet.mem (upgrade_aloc x) (Ghost.reveal (Loc?.aux l2')));
  assert (loc_aux_includes (Ghost.reveal (Loc?.aux l1')) (Ghost.reveal (Loc?.aux l2')) <==> loc_aux_includes (Ghost.reveal (Loc?.aux l1)) (Ghost.reveal (Loc?.aux l2)))

#reset-options

let raise_loc_disjoint #al #c l1 l2 =
  let l1' = raise_loc l1 in
  let l2' = raise_loc l2 in
  assert (forall (x: aloc (raise_cls c)) . GSet.mem x (Ghost.reveal (Loc?.aux l1')) <==> GSet.mem (downgrade_aloc x) (Ghost.reveal (Loc?.aux l1)));
  assert (forall (x: aloc (raise_cls c)) . GSet.mem x (Ghost.reveal (Loc?.aux l2')) <==> GSet.mem (downgrade_aloc x) (Ghost.reveal (Loc?.aux l2)));
  assert (forall (x: aloc c) . GSet.mem x (Ghost.reveal (Loc?.aux l1)) <==> GSet.mem (upgrade_aloc x) (Ghost.reveal (Loc?.aux l1')));
  assert (forall (x: aloc c) . GSet.mem x (Ghost.reveal (Loc?.aux l2)) <==> GSet.mem (upgrade_aloc x) (Ghost.reveal (Loc?.aux l2')));
  assert (forall r . addrs_of_loc l1' r `GSet.equal` addrs_of_loc l1 r);
  assert (forall r . addrs_of_loc l2' r `GSet.equal` addrs_of_loc l2 r);
  assert (forall (x1 x2: aloc (raise_cls u#x u#y c)) . aloc_disjoint x1 x2 <==> aloc_disjoint (downgrade_aloc x1) (downgrade_aloc x2));
  assert (forall (x1 x2: aloc (c)) . aloc_disjoint x1 x2 <==> aloc_disjoint (upgrade_aloc u#x u#y x1) (upgrade_aloc x2))

let modifies_raise_loc #al #c l h1 h2 =
  let l' = raise_loc l in
  assert (forall (x: aloc (raise_cls c)) . GSet.mem x (Ghost.reveal (Loc?.aux l')) <==> GSet.mem (downgrade_aloc x) (Ghost.reveal (Loc?.aux l)));
  assert (forall (x: aloc c) . GSet.mem x (Ghost.reveal (Loc?.aux l)) <==> GSet.mem (upgrade_aloc x) (Ghost.reveal (Loc?.aux l')));
  assert (forall r . addrs_of_loc l' r `GSet.equal` addrs_of_loc l r);
  assert (forall (x1 x2: aloc (raise_cls u#x u#y c)) . aloc_disjoint x1 x2 <==> aloc_disjoint (downgrade_aloc x1) (downgrade_aloc x2));
  assert (forall (r: HS.rid) (a: nat) (b: raise_aloc al r a) .
    loc_aux_disjoint (Ghost.reveal (Loc?.aux l')) (GSet.singleton (ALoc r a (Some b))) ==>
    loc_aux_disjoint (Ghost.reveal (Loc?.aux l)) (GSet.singleton (ALoc r a (Some (U.downgrade_val b)))));
  assert (modifies_preserves_alocs l h1 h2 ==> modifies_preserves_alocs l' h1 h2);
  assert (forall (r: HS.rid) (a: nat) (b: al r a) .
    loc_aux_disjoint (Ghost.reveal (Loc?.aux l)) (GSet.singleton (ALoc r a (Some b))) ==>
    loc_aux_disjoint (Ghost.reveal (Loc?.aux l')) (GSet.singleton (ALoc r a (Some (U.raise_val b)))));
  assert (modifies_preserves_alocs l' h1 h2 ==> modifies_preserves_alocs l h1 h2)
