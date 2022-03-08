(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.V.Effect.Common
module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
open Steel.Semantics.Instantiate
module FExt = FStar.FunctionalExtensionality

let h_exists #a f = VUnit ({hp = Mem.h_exists (fun x -> hp_of (f x)); t = unit; sel = fun _ -> ()})

let value_is_valid v x =
  exists (h: hmem v) . sel_of v h == x

let value_is_valid_complete v h = ()

let intro_valid_value (v: vprop) (x: t_of v) (h: Ghost.erased (hmem v)) : Pure (valid_value v)
  (requires (sel_of v h == x))
  (ensures (fun y -> (y <: t_of v) == x))
= x

let value_selector (v1 v2: vprop) : Tot Type0 =
  (f: FStar.FunctionalExtensionality.restricted_g_t (valid_value v1) (fun _ -> t_of v2) {
    forall (h: hmem v1) . interp (hp_of v2) h /\ sel_of v2 h == f (sel_of v1 h)
  })

let vsel_intro
  (v1 v2: vprop)
  (f: (valid_value v1) -> GTot (t_of v2))
  (prf: (h: hmem v1) ->
    Lemma
    (interp (hp_of v2) h /\ sel_of v2 h == f (sel_of v1 h))
  )
: Tot (value_selector v1 v2)
=
  let res =
    FStar.FunctionalExtensionality.on_domain_g (valid_value v1) f
  in
  Classical.forall_intro prf;
  res

let restricted_g_ext
  (a: Type)
  (b: a -> Type)
  (f1 f2: FStar.FunctionalExtensionality.restricted_g_t a b)
: Lemma
  (requires (f1 `FStar.FunctionalExtensionality.feq_g` f2))
  (ensures (f1 == f2))
= ()

let value_selector_unique
  (v1 v2: vprop)
  (s s': value_selector v1 v2)
: Lemma
  (s == s')
=
  restricted_g_ext (valid_value v1) (fun _ -> t_of v2) s s'

let sel_id (v: vprop) : Tot (value_selector v v) =
  FStar.FunctionalExtensionality.on_domain_g (valid_value v) (fun x -> (x <: t_of v))

let sel_fst (v1 v2: vprop) : Tot (value_selector (v1 `star` v2) v1) =
  FStar.FunctionalExtensionality.on_domain_g (valid_value (v1 `star` v2)) (fun x ->
    let h = FStar.IndefiniteDescription.indefinite_description_ghost (hmem (v1 `star` v2)) (fun h -> sel_of (v1 `star` v2) h == x) in
    affine_star (hp_of v1) (hp_of v2) h;
    (fst (x <: t_of (v1 `star` v2)))
  )

let sel_snd (v1 v2: vprop) : Tot (value_selector (v1 `star` v2) v2) =
  FStar.FunctionalExtensionality.on_domain_g (valid_value (v1 `star` v2)) (fun x ->
    let h = FStar.IndefiniteDescription.indefinite_description_ghost (hmem (v1 `star` v2)) (fun h -> sel_of (v1 `star` v2) h == x) in
    affine_star (hp_of v1) (hp_of v2) h;
    (snd (x <: t_of (v1 `star` v2)))
  )

let sel_compose
  (#v1 #v2 #v3: vprop)
  (s12: value_selector v1 v2)
  (s23: value_selector v2 v3)
: Tot (value_selector v1 v3)
=
  FStar.FunctionalExtensionality.on_domain_g (valid_value v1) (fun x ->
    let h = FStar.IndefiniteDescription.indefinite_description_ghost (hmem v1) (fun h -> sel_of v1 h == x) in
    (s23 (s12 x))
  )

let sel_star_f
  (#large1 #large2 #small1 #small2: vprop)
  (s1: large1 `value_selector` small1)
  (s2: large2 `value_selector` small2)
  (v: valid_value (large1 `star` large2))
: GTot (t_of (small1 `star` small2))
=
  (s1 (sel_fst large1 large2 v), s2 (sel_snd large1 large2 v))

let sel_star'
  (#large1 #large2 #small1 #small2: vprop)
  (s1: large1 `value_selector` small1)
  (s2: large2 `value_selector` small2)
  (v: t_of (large1 `star` large2))
  (h: hmem (large1 `star` large2))
: Lemma
  (requires (
    sel_of (large1 `star` large2) h == v
  ))
  (ensures (
    sel_of (large1 `star` large2) h == v /\ (
    let v' = sel_star_f s1 s2 v in
    interp (hp_of (small1 `star` small2)) h /\
    sel_of (small1 `star` small2) h == v'
  )))
=
    let x = v in
    elim_star (hp_of large1) (hp_of large2) h;
    let h1 = FStar.IndefiniteDescription.indefinite_description_ghost mem (fun h1 ->
      exists h2 . disjoint h1 h2 /\ h == join h1 h2 /\ interp (hp_of large1) h1 /\ interp (hp_of large2) h2
    )
    in
    let h2 = FStar.IndefiniteDescription.indefinite_description_ghost mem (fun h2 ->
      disjoint h1 h2 /\ h == join h1 h2 /\ interp (hp_of large1) h1 /\ interp (hp_of large2) h2
    )
    in
    let x' : t_of (large1 `star` large2) = x in
    assert (sel_of (large1 `star` large2) h == x');
    assert (sel_of large1 h == fst x');
    assert (sel_of large1 h1 == fst x');
    assert (sel_of large2 h == snd x');
    join_commutative h1 h2;
    assert (sel_of large2 h2 == snd x');
    let y' : t_of (small1 `star` small2) =
      (s1 (fst x'), s2 (snd x'))
    in
    intro_star (hp_of small1) (hp_of small2) h1 h2;
    assert (sel_of small1 h1 == fst y');
    assert (sel_of small2 h2 == snd y')

let sel_star''
  (#large1 #large2 #small1 #small2: vprop)
  (s1: large1 `value_selector` small1)
  (s2: large2 `value_selector` small2)
  (v: t_of (large1 `star` large2))
  (h: hmem (large1 `star` large2))
: Lemma
  (ensures (
    sel_of (large1 `star` large2) h == v ==> (
    let v' = sel_star_f s1 s2 v in
    interp (hp_of (small1 `star` small2)) h /\
    sel_of (small1 `star` small2) h == v'
  )))
= Classical.move_requires (sel_star' s1 s2 v) h

let sel_star
  (#large1 #large2 #small1 #small2: vprop)
  (s1: large1 `value_selector` small1)
  (s2: large2 `value_selector` small2)
: Tot ((large1 `star` large2) `value_selector` (small1 `star` small2))
=
  vsel_intro (large1 `star` large2) (small1 `star` small2) (fun v ->
    sel_star_f s1 s2 v
  ) (fun h -> sel_star' s1 s2 (sel_of (large1 `star` large2) h) h)

let can_be_split (p q:vprop) : prop =
  exists (s: value_selector p q) . True

let can_be_split_interp r r' h = ()

let can_be_split_trans v1 v2 v3 =
  let s12 = FStar.IndefiniteDescription.indefinite_description_ghost (value_selector v1 v2) (fun _ -> True) in
  let s23 = FStar.IndefiniteDescription.indefinite_description_ghost (value_selector v2 v3) (fun _ -> True) in
  FStar.Classical.exists_intro (fun _ -> True) (sel_compose s12 s23)

let can_be_split_star_l v1 v2 =
  FStar.Classical.exists_intro (fun _ -> True) (sel_fst v1 v2)

let can_be_split_star_r v1 v2 =
  FStar.Classical.exists_intro (fun _ -> True) (sel_snd v1 v2)

let can_be_split_refl p =
  FStar.Classical.exists_intro (fun _ -> True) (sel_id p)

let equiv (p q:vprop) : prop =
  p `can_be_split` q /\ q `can_be_split` p
let reveal_equiv p q = ()

let intro_can_be_split
  (p q: vprop)
  (f: (valid_value p -> GTot (t_of q)))
: Lemma
  (requires (
    hp_of p `Mem.slimp` hp_of q /\
    (forall h . sel_of q h == f (sel_of p h))
  ))
  (ensures (p `can_be_split` q))
= 
  FStar.Classical.exists_intro (fun _ -> True) (vsel_intro p q f (fun _ -> ()))

let can_be_split_star
  (large1 large2 small1 small2: vprop)
: Lemma
  (requires (
    large1 `can_be_split` small1 /\
    large2 `can_be_split` small2
  ))
  (ensures (
    (large1 `star` large2) `can_be_split` (small1 `star` small2)
  ))
= 
  let s1 = FStar.IndefiniteDescription.indefinite_description_ghost (value_selector large1 small1) (fun _ -> True) in
  let s2 = FStar.IndefiniteDescription.indefinite_description_ghost (value_selector large2 small2) (fun _ -> True) in
  FStar.Classical.exists_intro (fun _ -> True) (sel_star s1 s2)

let get_value_selector
  (a: vprop)
  (b: vprop { a `can_be_split` b })
: Tot (value_selector a b)
= FStar.IndefiniteDescription.indefinite_description_ghost (value_selector a b) (fun _ -> True)

let vselect #p x q =
  get_value_selector p q x

let vselect_id _ = ()
let vselect_fst _ = ()
let vselect_snd _ = ()
let vselect_compose _ _ _ = ()
let vselect_pair _ _ _ = ()

let vselect_correct _ _ _ = ()

let emp':vprop' =
  { hp = emp;
    t = unit;
    sel = fun _ -> ()}
let emp = VUnit emp'

let reveal_emp () = ()

let elim_conjunction p1 p1' p2 p2' = ()

let equiv_can_be_split p1 p2 = ()
let intro_can_be_split_frame p q frame = ()
let can_be_split_post_elim t1 t2 = ()
let equiv_forall_refl t = ()
let equiv_forall_elim t1 t2 = ()

let equiv_refl x = ()
let equiv_sym x y = ()
let equiv_trans x y z = ()

let cm_identity x =
  Mem.emp_unit (hp_of x);
  Mem.star_commutative (hp_of x) Mem.emp;
  intro_can_be_split x (emp `star` x) (fun v -> ((), v))

let star_commutative p1 p2 =
  Mem.star_commutative (hp_of p1) (hp_of p2);
  intro_can_be_split (p1 `star` p2) (p2 `star` p1) (fun (v1, v2) -> (v2, v1));
  let (p1, p2) = (p2, p1) in
  intro_can_be_split (p1 `star` p2) (p2 `star` p1) (fun (v1, v2) -> (v2, v1))

let star_associative p1 p2 p3 =
  Mem.star_associative (hp_of p1) (hp_of p2) (hp_of p3);
  intro_can_be_split (p1 `star` (p2 `star` p3)) ((p1 `star` p2) `star` p3) (fun (v1, (v2, v3)) -> ((v1, v2), v3));
  intro_can_be_split ((p1 `star` p2) `star` p3) (p1 `star` (p2 `star` p3)) (fun ((v1, v2), v3) -> (v1, (v2, v3)))

let star_congruence p1 p2 p3 p4 =
  can_be_split_star p1 p2 p3 p4;
  can_be_split_star p3 p4 p1 p2

let vrefine_am (v: vprop) (p: (t_of v -> Tot prop)) : Tot (a_mem_prop (hp_of v)) =
  fun h -> p (sel_of v h)

let vrefine_hp
  v p
= refine_slprop (hp_of v) (vrefine_am v p)

let interp_vrefine_hp
  v p m
= ()

let vrefine_sel' (v: vprop) (p: (t_of v -> Tot prop)) : Tot (selector' (vrefine_t v p) (vrefine_hp v p))
=
  fun (h: Mem.hmem (vrefine_hp v p)) ->
    interp_refine_slprop (hp_of v) (vrefine_am v p) h;
    sel_of v h

let vrefine_sel
  v p
= assert (sel_depends_only_on (vrefine_sel' v p));
  assert (sel_depends_only_on_core (vrefine_sel' v p));
  vrefine_sel' v p

let vrefine_sel_eq
  v p m
= ()

let vdep_hp_payload
  (v: vprop)
  (p: (t_of v -> Tot vprop))
  (h: Mem.hmem (hp_of v))
: Tot slprop
= hp_of (p (sel_of v h))

let vdep_hp
  v p
=
  sdep (hp_of v) (vdep_hp_payload v p)

let interp_vdep_hp
  v p m
=
  interp_sdep (hp_of v) (vdep_hp_payload v p) m;
  let left = interp (vdep_hp v p) m in
  let right = interp (hp_of v) m /\ interp (hp_of v `Mem.star` hp_of (p (sel_of v m))) m in
  let f ()
  : Lemma
    (requires left)
    (ensures right)
  = interp_star (hp_of v) (hp_of (p (sel_of v m))) m
  in
  let g ()
  : Lemma
    (requires right)
    (ensures left)
  = interp_star (hp_of v) (hp_of (p (sel_of v m))) m
  in
  Classical.move_requires f ();
  Classical.move_requires g ()

let vdep_sel'
  (v: vprop)
  (p: t_of v -> Tot vprop)
: Tot (selector' (vdep_t v p) (vdep_hp v p))
=
  fun (m: Mem.hmem (vdep_hp v p)) ->
    interp_vdep_hp v p m;
    let x = sel_of v m in
    let y = sel_of (p (sel_of v m)) m in
    (| x, y |)

let vdep_sel
  v p
= Classical.forall_intro_2 (Classical.move_requires_2 (fun (m0 m1: mem) -> (join_commutative m0) m1));
  vdep_sel' v p

let vdep_sel_eq
  v p m
= Classical.forall_intro_2 (Classical.move_requires_2 (fun (m0 m1: mem) -> (join_commutative m0) m1));
  ()

let vrewrite_sel
  v #t f
=
  (fun (h: Mem.hmem (normal (hp_of v))) -> f ((normal (sel_of v) <: selector' _ _) h))

let vrewrite_sel_eq
  v #t f h
= ()

let emp_unit_variant p =
  star_commutative p emp;
  cm_identity p
