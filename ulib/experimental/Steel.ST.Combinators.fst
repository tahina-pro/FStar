module Steel.ST.Combinators
include Steel.ST.Util
module C = Steel.ST.Coercions
module Ghost = FStar.Ghost
module SA = Steel.Effect.Atomic

#set-options "--ide_id_info_off"

let vrefine_elim'
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
: SA.SteelGhostT unit inames
    (s `vrefine` p)
    (fun _ -> s)
= SA.elim_vrefine s p

let vrefine_elim
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
: STGhostT unit inames
    (s `vrefine` p)
    (fun _ -> s)
= C.coerce_ghost (fun _ -> vrefine_elim' s p)

let vrefine_equals_intro'
  (#inames: _)
  (s: vprop)
: SA.SteelGhostT (Ghost.erased (t_of s)) inames
    s
    (fun res -> s `vrefine` equals (Ghost.reveal res))
=
  let res = SA.gget s in
  SA.intro_vrefine s (equals (Ghost.reveal res));
  res

let vrefine_equals_intro
  (#inames: _)
  (s: vprop)
: STGhostT (Ghost.erased (t_of s)) inames
    s
    (fun res -> s `vrefine` equals (Ghost.reveal res))
=
  C.coerce_ghost (fun _ -> vrefine_equals_intro' s)

let vrefine_vrefine_equals_elim'
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: t_of (vrefine s p))
: SA.SteelGhostT unit
    inames
    (s `vrefine` p `vrefine` equals x)
    (fun _ -> s `vrefine` equals #(t_of s) (elim_t_of_vrefine s p x))
=
  SA.elim_vrefine (s `vrefine` p) (equals x);
  SA.elim_vrefine s p;
  SA.intro_vrefine s (equals (elim_t_of_vrefine s p x))

let vunit_intro'
  (#inames: _)
  (s: vprop)
  (t: Type { t_of s == t })
  (x: t)
: SA.SteelGhostT unit inames
    (s `vrefine` equals #(t_of s) x)
    (fun _ -> vunit s t `vrefine` equals #t x)
=
  SA.elim_vrefine s (equals #(t_of s) x);
  SA.change_slprop
    s
    (vunit s t)
    x
    x
    (fun m -> ());
  SA.intro_vrefine (vunit s t) (equals #t x)

let vunit_intro
  s t x
=
  C.coerce_ghost (fun _ -> vunit_intro' s t x)

let vunit_elim'
  (#inames: _)
  (s: vprop)
  (t: Type { t_of s == t })
  (x: t)
: SA.SteelGhostT unit inames
    (vunit s t `vrefine` equals #t x)
    (fun _ -> s `vrefine` equals #(t_of s) x)
=
  SA.elim_vrefine (vunit s t) (equals #t x);
  SA.change_slprop
    (vunit s t)
    s
    x
    x
    (fun m -> ());
  SA.intro_vrefine s (equals #(t_of s) x)

let vunit_elim
  s t x
= C.coerce_ghost (fun _ -> vunit_elim' s t x)

let vrefine_vrefine_equals_elim
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: t_of (vrefine s p))
: STGhostT unit
    inames
    (s `vrefine` p `vrefine` equals x)
    (fun _ -> s `vrefine` equals #(t_of s) (elim_t_of_vrefine s p x))
= C.coerce_ghost (fun _ -> vrefine_vrefine_equals_elim' s p x)

let vrefine_vrefine_equals_intro'
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: t_of s)
: SA.SteelGhost (Ghost.erased (t_of (s `vrefine` p)))
    inames
    (s `vrefine` equals x)
    (fun res -> s `vrefine` p `vrefine` equals (Ghost.reveal res <: t_of (s `vrefine` p)))
    (fun _ -> p x)
    (fun _ res _ -> ((Ghost.reveal res <: normal (t_of (s `vrefine` p))) <: normal (t_of s)) == x)
=
  SA.elim_vrefine s (equals x);
  SA.intro_vrefine s p;
  let res : Ghost.erased (t_of (s `vrefine` p)) = (x <: normal (t_of (s `vrefine` p))) in
  SA.intro_vrefine (s `vrefine` p) (equals (Ghost.reveal res <: t_of (s `vrefine` p)));
  res

let vrefine_vrefine_equals_intro
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: t_of s)
= C.coerce_ghost (fun _ -> vrefine_vrefine_equals_intro' s p x)

let vrefine_equals_star_intro'
  (#inames: _)
  (s1 s2: vprop)
  (x1: t_of s1)
  (x2: t_of s2)
: SA.SteelGhostT unit
    inames
    ((s1 `vrefine` equals x1) `star` (s2 `vrefine` equals x2))
    (fun _ -> (s1 `star` s2) `vrefine` equals (x1, x2))
= SA.elim_vrefine s1 (equals x1);
  SA.elim_vrefine s2 (equals x2);
  SA.intro_vrefine (s1 `star` s2) (equals (x1, x2))

let vrefine_equals_star_intro
  (#inames: _)
  (s1 s2: vprop)
  (x1: t_of s1)
  (x2: t_of s2)
: STGhostT unit
    inames
    ((s1 `vrefine` equals x1) `star` (s2 `vrefine` equals x2))
    (fun _ -> (s1 `star` s2) `vrefine` equals (x1, x2))
= C.coerce_ghost (fun _ -> vrefine_equals_star_intro' s1 s2 x1 x2)

let vrefine_equals_star_elim'
  (#inames: _)
  (s1 s2: vprop)
  (x: t_of (s1 `star` s2))
: SA.SteelGhostT unit
    inames
    ((s1 `star` s2) `vrefine` equals x)
    (fun _ -> (s1 `vrefine` equals (fst x)) `star` (s2 `vrefine` equals (snd x)))
=
  SA.elim_vrefine (s1 `star` s2) (equals x);
  SA.intro_vrefine s1 (equals (fst x));
  SA.intro_vrefine s2 (equals (snd x))

let vrefine_equals_star_elim
  (#inames: _)
  (s1 s2: vprop)
  (x: t_of (s1 `star` s2))
: STGhostT unit
    inames
    ((s1 `star` s2) `vrefine` equals x)
    (fun _ -> (s1 `vrefine` equals (fst x)) `star` (s2 `vrefine` equals (snd x)))
= C.coerce_ghost (fun _ -> vrefine_equals_star_elim' s1 s2 x)

let vrewrite_vrefine_equals_intro'
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: t_of s)
: SA.SteelGhost (Ghost.erased t) inames
    (s `vrefine` equals x)
    (fun res -> s `vrewrite` f `vrefine` equals (Ghost.reveal res))
    (fun _ -> True)
    (fun _ res _ -> Ghost.reveal res == f x)
=
  SA.elim_vrefine s (equals x);
  SA.intro_vrewrite s f;
  let res : Ghost.erased t = Ghost.hide (f x) in
  SA.intro_vrefine (s `vrewrite` f) (equals (Ghost.reveal res));
  res

let vrewrite_vrefine_equals_intro0
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: t_of s)
: STGhost (Ghost.erased t) inames
    (s `vrefine` equals x)
    (fun res -> s `vrewrite` f `vrefine` equals (Ghost.reveal res))
    True
    (fun res -> Ghost.reveal res == f x)
= C.coerce_ghost (fun _ -> vrewrite_vrefine_equals_intro' s f x)

let vrewrite_vrefine_equals_elim'
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: t)
: SA.SteelGhost (Ghost.erased (t_of s)) inames
    (s `vrewrite` f `vrefine` equals x)
    (fun res -> s `vrefine` equals (Ghost.reveal res))
    (fun _ -> True)
    (fun _ res _ -> f (Ghost.reveal res) == x)
=
  SA.elim_vrefine (s `vrewrite` f) (equals x);
  SA.elim_vrewrite s f;
  let res : Ghost.erased (t_of s) = SA.gget s in
  SA.intro_vrefine s (equals (Ghost.reveal res));
  res

let vrewrite_vrefine_equals_elim
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: t)
: STGhost (Ghost.erased (t_of s)) inames
    (s `vrewrite` f `vrefine` equals x)
    (fun res -> s `vrefine` equals (Ghost.reveal res))
    True
    (fun res -> f (Ghost.reveal res) == x)
= C.coerce_ghost (fun _ -> vrewrite_vrefine_equals_elim' s f x)

let vdep_intro'
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (tag: t_of vtag)
  (vpl0: vprop)
  (pl: t_of vpl0)
: SA.SteelGhost (Ghost.erased (normal (t_of (vtag `vdep` vpl)))) inames
    ((vtag `vrefine` equals tag) `star` (vpl0 `vrefine` equals pl))
    (fun res -> (vtag `vdep` vpl) `vrefine` equals (Ghost.reveal res))
    (fun _ -> vpl0 == vpl tag)
    (fun _ res _ ->
      vpl0 == vpl tag /\
      dfst (Ghost.reveal res) == tag /\
      dsnd (Ghost.reveal res) == pl
    )
= SA.elim_vrefine vtag (equals tag);
  SA.elim_vrefine vpl0 (equals pl);
  SA.intro_vdep vtag vpl0 vpl;
  let res : Ghost.erased (normal (t_of (vtag `vdep` vpl))) = (| tag, pl |) in
  SA.intro_vrefine (vtag `vdep` vpl) (equals (Ghost.reveal res));
  res

let vdep_intro
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (tag: t_of vtag)
  (vpl0: vprop)
  (pl: t_of vpl0)
= C.coerce_ghost (fun _ -> vdep_intro' vtag vpl tag vpl0 pl)

let vdep_elim'
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (x: normal (t_of (vtag `vdep` vpl)))
: SA.SteelGhostT unit inames
    ((vtag `vdep` vpl) `vrefine` equals x)
    (fun _ -> (vtag `vrefine` equals (dfst x)) `star` (vpl (dfst x) `vrefine` equals (dsnd x)))
= SA.elim_vrefine (vtag `vdep` vpl) (equals x);
  let tag = SA.elim_vdep vtag vpl in
  SA.intro_vrefine vtag (equals (dfst x));
  SA.change_equal_slprop
    (vpl tag)
    (vpl (dfst x));
  SA.intro_vrefine (vpl (dfst x)) (equals (dsnd x))

let vdep_elim
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (x: normal (t_of (vtag `vdep` vpl)))
: STGhostT unit inames
    ((vtag `vdep` vpl) `vrefine` equals x)
    (fun _ -> (vtag `vrefine` equals (dfst x)) `star` (vpl (dfst x) `vrefine` equals (dsnd x)))
= C.coerce_ghost (fun _ -> vdep_elim' vtag vpl x)

let vrefine_equals_injective
  (v: vprop)
  (x1 x2: t_of v)
  (m: mem)
: Lemma
  (requires (
    interp (hp_of (v `vrefine` equals x1)) m /\
    interp (hp_of (v `vrefine` equals x2)) m
  ))
  (ensures (x1 == x2))
= interp_vrefine_hp v (equals x1) m;
  interp_vrefine_hp v (equals x2) m
