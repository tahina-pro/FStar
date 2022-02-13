module Steel.ST.Combinators
include Steel.ST.Util
module Ghost = FStar.Ghost

#set-options "--ide_id_info_off"

(* This module is basically saying that, for any vprop s, there is a
   generic way to derive its "explicit pts_to" version, namely "s
   `vrefine` equals x".  Thus, we offer vprop combinators and
   corresponding rules based on that pattern, all of which we claim
   can eliminate the need for selector predicates in practice.  *)

let equals (#a: Type) (x: a) (y: a) : Tot prop =
  x == y

[@@__steel_reduce__]
let vrefine (v: vprop) (p: (t_of v -> Tot prop)) = vrefine v p

let rewrite_eq_l (#opened:inames)
            (p q: vprop)
            (#l: t_of p)
            (_: squash (p == q))
  : STGhostT unit opened (p `vrefine` equals (l <: t_of p)) (fun _ -> q `vrefine` equals (l <: t_of q))
= rewrite (p `vrefine` equals (l <: t_of p)) (q `vrefine` equals (l <: t_of q))

let rewrite_eq_r (#opened:inames)
            (p: vprop)
            (#l: t_of p)
            (l': t_of p)
  : STGhost unit opened (p `vrefine` equals l) (fun _ -> p `vrefine` equals l') (requires (l == l')) (ensures (fun _ -> True))
= rewrite (p `vrefine` equals l) (p `vrefine` equals l')

val vrefine_elim
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
: STGhostT unit inames
    (s `vrefine` p)
    (fun _ -> s)

val vrefine_equals_intro
  (#inames: _)
  (s: vprop)
: STGhostT (Ghost.erased (t_of s)) inames
    s
    (fun res -> s `vrefine` equals (Ghost.reveal res))

let vrefine_equals_gget
  (#inames: _)
  (s: vprop)
  (#x: t_of s)
  (_: unit)
: STGhost (Ghost.erased (t_of s)) inames
    (s `vrefine` equals x)
    (fun res -> s `vrefine` equals (Ghost.reveal res))
    (True)
    (fun res -> Ghost.reveal res == x)
= let res = Ghost.hide x in
  rewrite
    (s `vrefine` equals x)
    _;
  res

let elim_t_of_vrefine
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: t_of (vrefine s p))
: Tot (t_of s)
= norm_spec normal_steps (t_of (s `vrefine` p));
  (x <: normal (t_of (s `vrefine` p)))

[@@__steel_reduce__]
let vunit
  (s: vprop)
  (t: Type { t_of s == t })
: Tot vprop
= VUnit ({
  hp = hp_of s;
  t = t;
  sel = sel_of s;
})

val vunit_intro
  (#inames: _)
  (s: vprop)
  (t: Type { t_of s == t })
  (x: t)
: STGhostT unit inames
    (s `vrefine` equals #(t_of s) x)
    (fun _ -> vunit s t `vrefine` equals #t x)

val vunit_elim
  (#inames: _)
  (s: vprop)
  (t: Type { t_of s == t })
  (x: t)
: STGhostT unit inames
    (vunit s t `vrefine` equals #t x)
    (fun _ -> s `vrefine` equals #(t_of s) x)

val vrefine_vrefine_equals_elim
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: t_of (vrefine s p))
: STGhostT unit
    inames
    (s `vrefine` p `vrefine` equals x)
    (fun _ -> s `vrefine` equals #(t_of s) (elim_t_of_vrefine s p x))

val vrefine_vrefine_equals_intro
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: t_of s)
: STGhost (Ghost.erased (t_of (s `vrefine` p)))
    inames
    (s `vrefine` equals x)
    (fun res -> s `vrefine` p `vrefine` equals (Ghost.reveal res))
    (p x)
    (fun res -> elim_t_of_vrefine s p res == x)

let vrefine_intro
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: t_of s)
: STGhost unit
    inames
    (s `vrefine` equals x)
    (fun res -> s `vrefine` p)
    (p x)
    (fun _ -> True)
=
  let _ = vrefine_vrefine_equals_intro s p x in
  vrefine_elim _ _

val vrefine_equals_star_intro
  (#inames: _)
  (s1 s2: vprop)
  (x1: t_of s1)
  (x2: t_of s2)
: STGhostT unit
    inames
    ((s1 `vrefine` equals x1) `star` (s2 `vrefine` equals x2))
    (fun _ -> (s1 `star` s2) `vrefine` equals (x1, x2))

let vrefine_intro_2
  (#inames: _)
  (s1 s2: vprop)
  (p: (t_of s1 & t_of s2) -> Tot prop)
  (x1: t_of s1)
  (x2: t_of s2)
//  (sq: squash (p (x1, x2)))
: STGhostT unit inames
  ((s1 `vrefine` equals x1) `star` (s2 `vrefine` equals x2))
  (fun _ -> (s1 `star` s2) `vrefine` p)
=
  admit_ ();
  vrefine_equals_star_intro s1 s2 x1 x2;
  vrefine_intro (s1 `star` s2) p _

val vrefine_equals_star_elim
  (#inames: _)
  (s1 s2: vprop)
  (x: t_of (s1 `star` s2))
: STGhostT unit
    inames
    ((s1 `star` s2) `vrefine` equals x)
    (fun _ -> (s1 `vrefine` equals (fst x)) `star` (s2 `vrefine` equals (snd x)))

[@@__steel_reduce__]
let vrewrite (v: vprop) (#t: Type) (f: ((t_of v) -> GTot t)) : Tot vprop =
  vrewrite v f

val vrewrite_vrefine_equals_intro0
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

let vrewrite_vrefine_equals_intro
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: t_of s)
: STGhostT unit inames
    (s `vrefine` equals x)
    (fun res -> s `vrewrite` f `vrefine` equals (f x))
= let res = vrewrite_vrefine_equals_intro0 s f x in
  rewrite
    (s `vrewrite` f `vrefine` equals (Ghost.reveal res))
    (s `vrewrite` f `vrefine` equals (f x))

val vrewrite_vrefine_equals_elim
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

let vdep_dfst
  (v: vprop)
  (p: (t_of v -> Tot vprop))
  (x: t_of (v `vdep` p))
: Tot (t_of v)
= dfst (x <: vdep_t v p)

let vdep_dsnd
  (v: vprop)
  (p: (t_of v -> Tot vprop))
  (x: t_of (v `vdep` p))
: Tot (t_of (p (vdep_dfst v p x)))
= dsnd (x <: vdep_t v p)

val vdep_intro
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (tag: t_of vtag)
  (vpl0: vprop)
  (pl: t_of vpl0)
: STGhost (Ghost.erased (t_of (vtag `vdep` vpl))) inames
    ((vtag `vrefine` equals tag) `star` (vpl0 `vrefine` equals pl))
    (fun res -> (vtag `vdep` vpl) `vrefine` equals (Ghost.reveal res))
    (vpl0 == vpl tag)
    (fun res ->
      vpl0 == vpl tag /\
      vdep_dfst vtag vpl res == tag /\
      vdep_dsnd vtag vpl res == pl
    )

val vdep_elim
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (x: t_of (vtag `vdep` vpl))
: STGhostT unit inames
    ((vtag `vdep` vpl) `vrefine` equals x)
    (fun _ -> (vtag `vrefine` equals (vdep_dfst vtag vpl x)) `star` (vpl (vdep_dfst vtag vpl x) `vrefine` equals (vdep_dsnd vtag vpl x)))

val vrefine_equals_injective
  (v: vprop)
  (x1 x2: t_of v)
  (m: mem)
: Lemma
  (requires (
    interp (hp_of (v `vrefine` equals x1)) m /\
    interp (hp_of (v `vrefine` equals x2)) m
  ))
  (ensures (x1 == x2))
