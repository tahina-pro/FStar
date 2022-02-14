module Steel.ST.Combinators
module C = Steel.ST.Coercions
module Ghost = FStar.Ghost
module SA = Steel.Effect.Atomic

#set-options "--ide_id_info_off"

let _equals (#a: Type) (x: a) (y: a) : Tot prop =
  x == y

let vselect v x = vrefine v (_equals (Ghost.reveal x))

let vrefine_drop'
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
: SA.SteelGhostT unit inames
    (s `vrefine` p)
    (fun _ -> s)
= SA.elim_vrefine s p

let vrefine_drop
  s p
= C.coerce_ghost (fun _ -> vrefine_drop' s p)

let vselect_intro'
  (#inames: _)
  (s: vprop)
: SA.SteelGhostT (Ghost.erased (t_of s)) inames
    s
    (fun res -> s `vselect` res)
=
  let res = SA.gget s in
  SA.intro_vrefine s (_equals (Ghost.reveal res));
  res

let vselect_intro
  s
=
  C.coerce_ghost (fun _ -> vselect_intro' s)

let vselect_elim
  (#inames: _)
  (s: vprop)
  (x: Ghost.erased (t_of s))
: STGhostT unit inames
    (s `vselect` x)
    (fun _ -> s)
= vrefine_drop _ _

#set-options "--print_implicits"

let vunit_intro'
  (#inames: _)
  (s: vprop)
  (t: Type { t_of s == t })
  (x: Ghost.erased (t_of s))
: SA.SteelGhost (Ghost.erased t) inames
    (s `vselect` x)
    (fun res -> vunit s t `vselect` res)
    (fun _ -> True)
    (fun _ res _ -> Ghost.reveal res == (Ghost.reveal x <: t))
=
  SA.elim_vrefine s (_equals (Ghost.reveal #(t_of s) x));
  SA.change_slprop
    s
    (vunit s t)
    (Ghost.reveal #(t_of s) x)
    (Ghost.reveal #t x)
    (fun m -> ());
  let res : Ghost.erased t = x in
  SA.intro_vrefine (vunit s t) (_equals #t res);
  res

let vunit_intro
  s t x
=
  C.coerce_ghost (fun _ -> vunit_intro' s t x)

let vunit_elim'
  (#inames: _)
  (s: vprop)
  (t: Type { t_of s == t })
  (x: Ghost.erased t)
: SA.SteelGhost (Ghost.erased (t_of s)) inames
    (vunit s t `vselect` x)
    (fun res -> s `vselect` res)
    (fun _ -> True)
    (fun _ res _ -> (Ghost.reveal res <: t) == Ghost.reveal x)
=
  SA.elim_vrefine (vunit s t) (_equals (Ghost.reveal #t x));
  SA.change_slprop
    (vunit s t)
    s
    (Ghost.reveal #t x)
    (Ghost.reveal #(t_of s) x)
    (fun m -> ());
  let res : Ghost.erased (t_of s) = x in
  SA.intro_vrefine s (_equals (Ghost.reveal #(t_of s) res));
  res

let vunit_elim
  s t x
= C.coerce_ghost (fun _ -> vunit_elim' s t x)

let vrefine_elim'
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: Ghost.erased (t_of (vrefine s p)))
: SA.SteelGhostT unit
    inames
    (s `vrefine` p `vselect` x)
    (fun _ -> s `vselect` elim_t_of_vrefine s p x)
= SA.sladmit ()

let vrefine_elim
  s p x
= C.coerce_ghost (fun _ -> vrefine_elim' s p x)

let vrefine_intro'
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: Ghost.erased (t_of s))
: SA.SteelGhost (Ghost.erased (t_of (s `vrefine` p)))
    inames
    (s `vselect` x)
    (fun res -> s `vrefine` p `vselect` res)
    (fun _ -> p x)
    (fun _ res _ -> elim_t_of_vrefine s p res == Ghost.reveal x)
=
  SA.elim_vrefine s (_equals (Ghost.reveal #(t_of s) x));
  SA.intro_vrefine s p;
  let res : Ghost.erased (t_of (s `vrefine` p)) = (x <: normal (t_of (s `vrefine` p))) in
  SA.intro_vrefine (s `vrefine` p) (_equals (Ghost.reveal res <: t_of (s `vrefine` p)));
  res

let vrefine_intro
  s p x
= C.coerce_ghost (fun _ -> vrefine_intro' s p x)

let vselect_star_intro'
  (#inames: _)
  (s1 s2: vprop)
  (x1: Ghost.erased (t_of s1))
  (x2: Ghost.erased (t_of s2))
: SA.SteelGhostT unit
    inames
    ((s1 `vselect` x1) `star` (s2 `vselect` x2))
    (fun _ -> (s1 `star` s2) `vselect` vselect_star_intro_res s1 s2 x1 x2)
= SA.elim_vrefine s1 (_equals (Ghost.reveal x1));
  SA.elim_vrefine s2 (_equals (Ghost.reveal x2));
  SA.intro_vrefine (s1 `star` s2) (_equals #(t_of (s1 `star` s2)) (vselect_star_intro_res s1 s2 x1 x2))

let vselect_star_intro
  s1 s2 x1 x2
= C.coerce_ghost (fun _ -> vselect_star_intro' s1 s2 x1 x2)

let vselect_star_elim'
  (#inames: _)
  (s1 s2: vprop)
  (x: Ghost.erased (t_of (s1 `star` s2)))
: SA.SteelGhostT unit
    inames
    ((s1 `star` s2) `vselect` x)
    (fun _ -> (s1 `vselect` fst x) `star` (s2 `vselect` snd x))
=
  SA.elim_vrefine (s1 `star` s2) (_equals (Ghost.reveal x));
  SA.intro_vrefine s1 (_equals #(t_of s1) (vselect_star_elim_fst s1 s2 x));
  SA.intro_vrefine s2 (_equals #(t_of s2) (vselect_star_elim_snd s1 s2 x))

let vselect_star_elim
  s1 s2 x
= C.coerce_ghost (fun _ -> vselect_star_elim' s1 s2 x)

let vrewrite_intro'
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: Ghost.erased (t_of s))
: SA.SteelGhostT unit inames
    (s `vselect` x)
    (fun res -> s `vrewrite` f `vselect` vrewrite_intro_res s f x)
=
  SA.elim_vrefine s (_equals (Ghost.reveal #(t_of s) x));
  SA.intro_vrewrite s f;
  SA.intro_vrefine (s `vrewrite` f) (_equals #t (vrewrite_intro_res s f x))

let vrewrite_intro
  s f x
= C.coerce_ghost (fun _ -> vrewrite_intro' s f x)

let vrewrite_elim'
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: Ghost.erased t)
: SA.SteelGhost (Ghost.erased (t_of s)) inames
    (s `vrewrite` f `vselect` x)
    (fun res -> s `vselect` res)
    (fun _ -> True)
    (fun _ res _ -> f (Ghost.reveal res) == Ghost.reveal x)
= SA.elim_vrefine (s `vrewrite` f) (_equals (Ghost.reveal x));
  SA.elim_vrewrite s f;
  let res : Ghost.erased (t_of s) = SA.gget s in
  SA.intro_vrefine s (_equals (Ghost.reveal res));
  res

let vrewrite_elim
  s f x
= C.coerce_ghost (fun _ -> vrewrite_elim' s f x)

let vdep_intro0'
  (inames: _)
  (vtag: vprop)
  (tag: Ghost.erased (t_of vtag))
  (vpl0: vprop)
  (pl: Ghost.erased (t_of vpl0))
  (vpl: (t_of vtag -> Tot vprop))
  (sq: squash (vpl0 == vpl tag))
  (_: unit)
: SA.SteelGhostT unit inames
    ((vtag `vselect` tag) `star` (vpl0 `vselect` pl))
    (fun _ -> (vtag `vdep` vpl) `vselect` vdep_intro_res vtag tag vpl0 pl vpl sq)
= SA.elim_vrefine vtag (_equals (Ghost.reveal tag));
  SA.elim_vrefine vpl0 (_equals (Ghost.reveal pl));
  SA.intro_vdep vtag vpl0 vpl;
  SA.intro_vrefine (vtag `vdep` vpl) (_equals (Ghost.reveal (vdep_intro_res vtag tag vpl0 pl vpl sq)))

let vdep_intro0
  #inames vtag tag vpl0 pl vpl sq
= C.coerce_ghost
    (vdep_intro0' inames vtag tag vpl0 pl vpl sq)

let vdep_elim'
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (x: Ghost.erased (t_of (vtag `vdep` vpl)))
: SA.SteelGhostT unit inames
    ((vtag `vdep` vpl) `vselect` x)
    (fun _ -> (vtag `vselect` (vdep_dfst vtag vpl x)) `star` (vpl (vdep_dfst vtag vpl x) `vselect` (vdep_dsnd vtag vpl x)))
= SA.elim_vrefine (vtag `vdep` vpl) (_equals (Ghost.reveal x));
  let tag = SA.elim_vdep vtag vpl in
  SA.intro_vrefine vtag (_equals (vdep_dfst vtag vpl x));
  SA.change_equal_slprop
    (vpl tag)
    (vpl (vdep_dfst vtag vpl x));
  SA.intro_vrefine (vpl (vdep_dfst vtag vpl x)) (_equals (vdep_dsnd vtag vpl x))

let vdep_elim
  vtag vpl x
= C.coerce_ghost (fun _ -> vdep_elim' vtag vpl x)

let vselect_injective
  v x1 x2 m
= interp_vrefine_hp v (_equals (Ghost.reveal x1)) m;
  interp_vrefine_hp v (_equals (Ghost.reveal x2)) m
