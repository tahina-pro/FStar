module FStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = FStar.Buffer
module U32 = FStar.UInt32

type abuffer' = {
  b_region: HS.rid;
  b_addr: nat;
  b_max_length: nat;
  b_offset: nat;
  b_length: nat;
}

type abuffer = (x: abuffer' { x.b_offset + x.b_length <= x.b_max_length } )

let abuffer_of_buffer (#a: Type) (b: B.buffer a) : GTot abuffer = {
  b_region = B.frameOf b;
  b_addr = B.as_addr b;
  b_max_length = B.max_length b;
  b_offset = B.idx b;
  b_length = B.length b;
}

let aloc (r: HS.rid) (a: nat) : Tot Type0 =
  (x: abuffer { x.b_region == r /\ x.b_addr == a } )

let abuffer_includes (larger smaller: abuffer) : GTot Type0 =
  larger.b_region == smaller.b_region /\
  larger.b_addr == smaller.b_addr /\
  larger.b_max_length == smaller.b_max_length /\
  larger.b_offset <= smaller.b_offset /\
  smaller.b_offset + smaller.b_length <= larger.b_offset + larger.b_length

let abuffer_disjoint (x1 x2: abuffer) : GTot Type0 =
  (x1.b_region == x2.b_region /\ x1.b_addr == x2.b_addr) ==>
  (x1.b_max_length == x2.b_max_length /\
    (x1.b_offset + x1.b_length <= x2.b_offset \/
     x2.b_offset + x2.b_length <= x1.b_offset))

let abuffer_preserved
  (x: abuffer)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (t: Type) (b: B.buffer t) .
    (
      B.live h1 b /\
      B.length b <> 0 /\
      abuffer_of_buffer b == x
    ) ==> (
      B.live h2 b /\
      B.as_seq h2 b == B.as_seq h1 b
  ))

module MG = FStar.ModifiesGen

let cls = MG.Cls #aloc
  (fun #r #a -> abuffer_includes)
  (fun #r #a x -> ())
  (fun #r #a x1 x2 x3 -> ())
  (fun #r #a -> abuffer_disjoint)
  (fun #r #a x1 x2 -> ())
  (fun #r #a larger1 larger2 smaller1 smaller2 -> ())
  (fun #r #a -> abuffer_preserved)
  (fun #r #a x h -> ())
  (fun #r #a x h1 h2 h3 -> ())
  (fun #r #a b h1 h2 f ->
    let g (t: Type0) (b' : B.buffer t) : Lemma
      (requires (abuffer_of_buffer b' == b /\ B.live h1 b'))
      (ensures (B.live h2 b' /\ B.as_seq h2 b' == B.as_seq h1 b'))
    = f _ _ (B.content b')
    in
    let g' (t: Type0) (b' : B.buffer t) : Lemma
      ((abuffer_of_buffer b' == b /\ B.live h1 b') ==>
        (B.live h2 b' /\ B.as_seq h2 b' == B.as_seq h1 b'))
    = Classical.move_requires (g t) b'
    in
    Classical.forall_intro_2 g'
  )
  (fun #r #a b h1 h2 -> ())

let loc = MG.loc cls

let loc_none = MG.loc_none

let loc_union = MG.loc_union

let loc_union_idem = MG.loc_union_idem

let loc_buffer #t b =
  MG.loc_of_aloc #_ #cls #(B.frameOf b) #(B.as_addr b) (abuffer_of_buffer b)

let loc_addresses = MG.loc_addresses

let loc_regions = MG.loc_regions

let loc_includes = MG.loc_includes

let loc_includes_refl = MG.loc_includes_refl

let loc_includes_trans = MG.loc_includes_trans

let loc_includes_union_r = MG.loc_includes_union_r

let loc_includes_union_l = MG.loc_includes_union_l

let loc_includes_none = MG.loc_includes_none

let loc_includes_buffer #t b1 b2 =
  MG.loc_includes_aloc #_ #cls #(B.frameOf b1) #(B.as_addr b1) (abuffer_of_buffer b1) (abuffer_of_buffer b2)

let loc_includes_gsub_buffer_r l #t b i len =
  loc_includes_trans l (loc_buffer b) (loc_buffer (B.sub b i len))

let loc_includes_gsub_buffer_l #t b i1 len1 i2 len2 = ()

let loc_includes_addresses_buffer #t r s p =
  MG.loc_includes_addresses_aloc #_ #cls r s #(B.as_addr p) (abuffer_of_buffer p)

let loc_includes_region_buffer #t s b =
  MG.loc_includes_region_aloc #_ #cls s #(B.frameOf b) #(B.as_addr b) (abuffer_of_buffer b)

let loc_includes_region_addresses = MG.loc_includes_region_addresses #_ #cls

let loc_includes_region_region = MG.loc_includes_region_region #_ #cls

let loc_includes_region_union_l = MG.loc_includes_region_union_l

let loc_disjoint = MG.loc_disjoint

let loc_disjoint_sym = MG.loc_disjoint_sym

let loc_disjoint_none_r = MG.loc_disjoint_none_r

let loc_disjoint_union_r = MG.loc_disjoint_union_r

let loc_disjoint_includes = MG.loc_disjoint_includes

let loc_disjoint_buffer #t1 #t2 b1 b2 =
  MG.loc_disjoint_aloc_intro #_ #cls #(B.frameOf b1) #(B.as_addr b1) #(B.frameOf b2) #(B.as_addr b2) (abuffer_of_buffer b1) (abuffer_of_buffer b2)

let loc_disjoint_gsub_buffer #t b i1 len1 i2 len2 = ()

let loc_disjoint_addresses = MG.loc_disjoint_addresses #_ #cls

let loc_disjoint_buffer_addresses #t p r n =
  MG.loc_disjoint_aloc_addresses_intro #_ #cls #(B.frameOf p) #(B.as_addr p) (abuffer_of_buffer p) r n

let loc_disjoint_regions = MG.loc_disjoint_regions #_ #cls

let modifies = MG.modifies

let modifies_mreference_elim = MG.modifies_mreference_elim

let modifies_buffer_elim #t1 b p h h' =
  MG.modifies_aloc_elim #_ #cls #(B.frameOf b) #(B.as_addr b) (abuffer_of_buffer b) p h h'

let modifies_refl = MG.modifies_refl

let modifies_loc_includes = MG.modifies_loc_includes

let modifies_trans = MG.modifies_trans

let modifies_only_live_regions = MG.modifies_only_live_regions

let no_upd_fresh_region = MG.no_upd_fresh_region

let modifies_fresh_frame_popped = MG.modifies_fresh_frame_popped

let modifies_loc_regions_intro = MG.modifies_loc_regions_intro #_ #cls

let modifies_loc_addresses_intro = MG.modifies_loc_addresses_intro

let modifies_ralloc_post = MG.modifies_ralloc_post #_ #cls

let modifies_salloc_post = MG.modifies_salloc_post #_ #cls

let modifies_free = MG.modifies_free #_ #cls

let modifies_none_modifies = MG.modifies_none_modifies #_ #cls

let modifies_buffer_none_modifies h1 h2 =
  MG.modifies_intro loc_none h1 h2
    (fun _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ _ -> ())

let modifies_0_modifies h1 h2 =
  B.lemma_reveal_modifies_0 h1 h2;
  MG.modifies_intro loc_none h1 h2
    (fun _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ _ -> ())

(* Two live buffers at the same region and the same address have the
same type.  Anyway this is a transitional library, and a new
implementation is underway (see LowStar.Buffer) so don't give a sh*t,
anyway this is F* code. *)

#set-options "--z3rlimit 16"

let modifies_1_modifies #a b h1 h2 =
  B.lemma_reveal_modifies_1 b h1 h2;
  MG.modifies_intro (loc_buffer b) h1 h2
    (fun _ -> ())
    (fun t' pre' b' ->
      MG.loc_disjoint_sym (loc_mreference b') (loc_buffer b);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(B.frameOf b) #(B.as_addr b) (abuffer_of_buffer b) (HS.frameOf b') (Set.singleton (HS.as_addr b'))
    )
    (fun r' a' b' ->
      assert (HS.modifies_ref (B.frameOf b) (Set.singleton (B.as_addr b)) h1 h2);
      assert (B.live h1 b);
      MG.loc_disjoint_aloc_elim #_ #cls #r' #a' #(B.frameOf b) #(B.as_addr b) b' (abuffer_of_buffer b)
    )
    

(** The modifies clause proper *)

let modifies_preserves_mreferences
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (t: Type) (pre: Preorder.preorder t) (p: HS.mreference t pre) .
    let r = HS.frameOf p in (
      HS.contains h1 p /\
      (Set.mem r (regions_of_loc s) ==> ~ (Set.mem (HS.as_addr p) (addrs_of_loc s r)))
    ) ==> (
      HS.contains h2 p /\
      HS.sel h2 p == HS.sel h1 p
  ))

let modifies_preserves_buffers
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (t: Type) (b: B.buffer t) .
    let s' = Ghost.reveal s in  
    let r = B.frameOf b in
    let a = B.as_addr b in (
      B.live h1 b /\
      B.length b <> 0 /\
      (Set.mem r (regions_of_loc s) ==> ~ (Set.mem a (addrs_of_loc_weak s r))) /\
      ((Set.mem r (Ghost.reveal (Loc?.aux_regions s')) /\ Set.mem a (Loc?.aux_addrs s' r)) ==> loc_aux_disjoint_buffer (Loc?.aux s' r a) (abuffer_of_buffer b))
    ) ==> (
      B.live h2 b /\
      B.as_seq h2 b == B.as_seq h1 b
  ))

let modifies'
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= modifies_preserves_mreferences s h1 h2 /\
  modifies_preserves_buffers s h1 h2

let modifies = modifies'

let modifies_mreference_elim #t #pre b p h h' = ()

#set-options "--z3rlimit 16"

let modifies_buffer_elim #t1 b p h h' = ()

#reset-options

let modifies_refl s h = ()

let loc_aux_disjoint_buffer_loc_aux_includes
  (l1: loc_aux)
: Lemma
  (forall (l2: loc_aux)
    (b3: abuffer) .
  (loc_aux_disjoint_buffer l1 b3 /\ loc_aux_includes l1 l2) ==> loc_aux_disjoint_buffer l2 b3)
= let f
  (l2: loc_aux)
  (b3: abuffer)
  : Lemma
    (requires (loc_aux_disjoint_buffer l1 b3 /\ loc_aux_includes l1 l2))
    (ensures (loc_aux_disjoint_buffer l2 b3))
  = loc_aux_disjoint_sym (LocBuffer b3) l1;
    loc_aux_disjoint_loc_aux_includes (LocBuffer b3) l1 l2;
    loc_aux_disjoint_sym (LocBuffer b3) l2
  in
  Classical.forall_intro_2 (fun (l2: loc_aux) (b3: abuffer) -> Classical.move_requires (f l2) b3)

#set-options "--z3rlimit 32"

let modifies_loc_includes s1 h h' s2 =
  assert (modifies_preserves_mreferences s1 h h');
  Classical.forall_intro loc_aux_disjoint_buffer_loc_aux_includes;
  assert (modifies_preserves_buffers s1 h h')

#reset-options

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

// #set-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1"

#set-options "--z3rlimit 32"

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
= ()

#reset-options

(* Restrict a set of locations along a set of regions *)

let restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: GTot loc
= let (Loc whole_regions addr_regions addrs aux_regions aux_addrs aux) = Ghost.reveal l in
  Ghost.hide (Loc
    (Ghost.hide (Set.intersect (Ghost.reveal whole_regions) rs))
    (Ghost.hide (Set.intersect (Ghost.reveal addr_regions) rs))
    (fun r -> addrs r)
    (Ghost.hide (Set.intersect (Ghost.reveal aux_regions) rs))
    (fun r -> aux_addrs r)
    (fun r n -> aux r n)
  )

let regions_of_loc_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (regions_of_loc (restrict_to_regions l rs) == Set.intersect (regions_of_loc l) rs)
  [SMTPat (regions_of_loc (restrict_to_regions l rs))]
= assert (Set.equal (regions_of_loc (restrict_to_regions l rs)) (Set.intersect (regions_of_loc l) rs))

let addrs_of_loc_weak_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))
  [SMTPat (addrs_of_loc_weak (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc_weak (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))

let addrs_of_loc_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc l r else Set.empty))
  [SMTPat (addrs_of_loc (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc l r else Set.empty))

let loc_includes_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes l (restrict_to_regions l rs))
= Classical.forall_intro loc_aux_includes_refl

#set-options "--z3rlimit 32"

let loc_includes_loc_union_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes (loc_union (restrict_to_regions l rs) (restrict_to_regions l (Set.complement rs))) l)
= Classical.forall_intro loc_aux_includes_refl

#reset-options

let loc_includes_loc_regions_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes (loc_regions rs) (restrict_to_regions l rs))
= Classical.forall_intro loc_aux_includes_refl

let modifies_only_live_regions rs l h h' =
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
  loc_disjoint_regions rs c_rs;
  loc_includes_refl lrs;
  loc_disjoint_includes lrs (loc_regions c_rs) lrs s_c_rs;
  modifies_only_live_regions_weak rs s_c_rs h h';
  loc_includes_restrict_to_regions s c_rs;
  modifies_loc_includes s h h' s_c_rs

let no_upd_fresh_region r l h0 h1 =
  modifies_only_live_regions (HS.mod_set (Set.singleton r)) l h0 h1

let modifies_fresh_frame_popped h0 h1 s h2 h3 =
  modifies_loc_includes s h0 h1 loc_none;
  let s' = loc_union (loc_all_regions_from h1.HS.tip) s in
  modifies_loc_includes s' h2 h3 (loc_region_only h2.HS.tip);
  modifies_trans' s' h1 h2 h3;
  modifies_only_live_regions (HS.mod_set (Set.singleton h1.HS.tip)) s h0 h3

let modifies_loc_regions_intro rs h1 h2 = ()

#set-options "--z3rlimit 16"

let modifies_loc_addresses_intro_weak
  (r: HS.rid)
  (s: Set.set nat)
  (l: loc)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_region_only r) l) h1 h2 /\
    HS.modifies_ref r s h1 h2 /\
    loc_disjoint l (loc_region_only r)
  ))
  (ensures (modifies (loc_union (loc_addresses r s) l) h1 h2))
= assert (forall (t: Type) (pre: Preorder.preorder t) (p: HS.mreference t pre) . (HS.frameOf p == r /\ HS.contains h1 p /\ ~ (Set.mem (HS.as_addr p) s)) ==> (HS.contains h2 p /\ HS.sel h2 p == HS.sel h1 p));
  assert (modifies_preserves_mreferences (loc_union (loc_addresses r s) l) h1 h2);
  assert (modifies_preserves_buffers (loc_union (loc_addresses r s) l) h1 h2)

#reset-options

#set-options "--z3rlimit 32"

let modifies_loc_addresses_intro r s l h1 h2 =
  loc_includes_loc_regions_restrict_to_regions l (Set.singleton r);
  loc_includes_loc_union_restrict_to_regions l (Set.singleton r);
  assert (modifies (loc_union (loc_region_only r) (loc_union (restrict_to_regions l (Set.singleton r)) (restrict_to_regions l (Set.complement (Set.singleton r))))) h1 h2);
  modifies_loc_addresses_intro_weak r s (restrict_to_regions l (Set.complement (Set.singleton r))) h1 h2;
  loc_includes_restrict_to_regions l (Set.complement (Set.singleton r))

#reset-options

let modifies_ralloc_post #a #rel i init h x h' = ()

let modifies_salloc_post #a #rel init h x h' = ()

let modifies_free #a #rel r m = ()

let modifies_none_modifies h1 h2 = ()

let modifies_buffer_none_modifies h1 h2 = ()

let modifies_0_modifies h1 h2 =
  B.lemma_reveal_modifies_0 h1 h2

#set-options "--z3rlimit 16"

let modifies_1_modifies #a b h1 h2 =
  B.lemma_reveal_modifies_1 b h1 h2

let modifies_2_modifies #a1 #a2 b1 b2 h1 h2 =
  B.lemma_reveal_modifies_2 b1 b2 h1 h2

#set-options "--z3rlimit 64"

let modifies_3_modifies #a1 #a2 #a3 b1 b2 b3 h1 h2 =
  B.lemma_reveal_modifies_3 b1 b2 b3 h1 h2

#reset-options

let modifies_buffer_rcreate_post_common #a r init len b h0 h1 = ()

let mreference_live_buffer_unused_in_disjoint #t1 #pre #t2 h b1 b2 = ()

let buffer_live_mreference_unused_in_disjoint #t1 #t2 #pre h b1 b2 = ()
