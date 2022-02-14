module Steel.ST.Combinators
open Steel.ST.Util
module Ghost = FStar.Ghost

#set-options "--ide_id_info_off"

(* This module is basically saying that, for any vprop s, there is a
   generic way to derive its "explicit pts_to" version, namely "s
   `vrefine` equals x".  Thus, we offer vprop combinators and
   corresponding rules based on that pattern, all of which we claim
   can eliminate the need for selector predicates in practice.  *)

[@@__steel_reduce__]
let vrefine (v: vprop) (p: (t_of v -> Tot prop)) = vrefine v p

let vrefine0 (v: vprop) (p: Ghost.erased (t_of v -> Tot prop)) = vrefine v (Ghost.reveal p)

val vselect (v: vprop) ([@@@smt_fallback] x: Ghost.erased (t_of v)) : Tot vprop 

let rewrite_eq_l (#opened:inames)
            (p q: vprop)
            (#l: Ghost.erased (t_of p))
            (_: squash (p == q))
  : STGhostT unit opened (p `vselect` l) (fun _ -> q `vselect` l)
= rewrite (p `vselect` l) (q `vselect` l)

let rewrite_eq_l_gen (#opened:inames)
            (p q: vprop)
            (#l: Ghost.erased (t_of p))
            (_: squash (p == q))
  : STGhost (Ghost.erased (t_of q)) opened (p `vselect` l) (fun l' -> q `vselect` l')
      True (fun l' -> (l == l'))
= let l' : Ghost.erased (t_of q) = l in
  rewrite (p `vselect` l) (q `vselect` l');
  l'

let rewrite_eq_r (#opened:inames)
            (p: vprop)
            (#l: Ghost.erased (t_of p))
            (l': Ghost.erased (t_of p))
  : STGhost unit opened (p `vselect` l) (fun _ -> p `vselect` l') (requires (l == l')) (ensures (fun _ -> True))
= rewrite (p `vselect` l) (p `vselect` l')

val vrefine_drop
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
: STGhostT unit inames
    (s `vrefine` p)
    (fun _ -> s)

val vselect_intro
  (#inames: _)
  (s: vprop)
: STGhostT (Ghost.erased (t_of s)) inames
    s
    (fun res -> s `vselect` res)

let vselect_get
  (#inames: _)
  (s: vprop)
  (#x: Ghost.erased (t_of s))
  (_: unit)
: STGhost (Ghost.erased (t_of s)) inames
    (s `vselect` x)
    (fun res -> s `vselect` res)
    (True)
    (fun res -> res == x)
= noop ();
  x

let vselect_get_unchanged
  (#inames: _)
  (s: vprop)
  (#x: Ghost.erased (t_of s))
  (_: unit)
: STGhost (Ghost.erased (t_of s)) inames
    (s `vselect` x)
    (fun res -> s `vselect` x)
    (True)
    (fun res -> res == x)
= noop ();
  x

let vselect_assert
  (#inames: _)
  (s: vprop)
  (#x: Ghost.erased (t_of s))
  (y: Ghost.erased (t_of s))
: STGhost unit inames
    (s `vselect` x)
    (fun _ -> s `vselect` x)
    (Ghost.reveal y == Ghost.reveal x)
    (fun _ -> True)
= noop ()

val vselect_elim
  (#inames: _)
  (s: vprop)
  (x: Ghost.erased (t_of s))
: STGhostT unit inames
    (s `vselect` x)
    (fun _ -> s)

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
  (x: Ghost.erased (t_of s))
: STGhost (Ghost.erased t) inames
    (s `vselect` x)
    (fun res -> vunit s t `vselect` res)
    True
    (fun res -> Ghost.reveal res == (Ghost.reveal x <: t))

val vunit_elim
  (#inames: _)
  (s: vprop)
  (t: Type { t_of s == t })
  (x: Ghost.erased t)
: STGhost (Ghost.erased (t_of s)) inames
    (vunit s t `vselect` x)
    (fun res -> s `vselect` res)
    (True)
    (fun res -> (Ghost.reveal res <: t) == Ghost.reveal x)

val vrefine_elim
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: Ghost.erased (t_of (vrefine s p)))
: STGhostT unit
    inames
    (s `vrefine` p `vselect` x)
    (fun _ -> s `vselect` elim_t_of_vrefine s p x)

val vrefine_intro
  (#inames: _)
  (s: vprop)
  (p: t_of s -> Tot prop)
  (x: Ghost.erased (t_of s))
: STGhost (Ghost.erased (t_of (s `vrefine` p)))
    inames
    (s `vselect` x)
    (fun res -> s `vrefine` p `vselect` res)
    (p x)
    (fun res -> elim_t_of_vrefine s p res == Ghost.reveal x)

let vselect_to_vrefine
  (#inames: _)
  (s: vprop)
  (p: Ghost.erased (t_of s -> Tot prop))
  (x: Ghost.erased (t_of s))
  (sq: squash (Ghost.reveal p x))
: STGhostT unit
    inames
    (s `vselect` x)
    (fun res -> s `vrefine0` p)
=
  let _ = vrefine_intro s p x in
  vselect_elim _ _

let vselect_to_vrefine'
  (#inames: _)
  (s: vprop)
  (p: Ghost.erased (t_of s -> Tot prop))
  (x: Ghost.erased (t_of s))
: STGhost unit
    inames
    (s `vselect` x)
    (fun res -> s `vrefine0` p)
    (Ghost.reveal p x)
    (fun _ -> True)
= vselect_to_vrefine s p x ()

let vrefine_to_vselect
  (#inames: _)
  (s: vprop)
  (p: Ghost.erased (t_of s -> Tot prop))
: STGhost (Ghost.erased (t_of s))
    inames
    (s `vrefine0` p)
    (fun res -> s `vselect` res)
    True
    (fun res -> Ghost.reveal p res)
=
  let x = vselect_intro (s `vrefine0` p) in
  let y = rewrite_eq_l_gen (s `vrefine0` p) (s `vrefine` p) #x () in
  vrefine_elim s p y;
  let res = vselect_get s () in
  res

let vselect_star_intro_res
  (s1 s2: vprop)
  (x1: Ghost.erased (t_of s1))
  (x2: Ghost.erased (t_of s2))
: Tot (Ghost.erased (t_of (s1 `star` s2)))
= (Ghost.reveal x1, Ghost.reveal x2)

val vselect_star_intro
  (#inames: _)
  (s1 s2: vprop)
  (x1: Ghost.erased (t_of s1))
  (x2: Ghost.erased (t_of s2))
: STGhostT unit
    inames
    ((s1 `vselect` x1) `star` (s2 `vselect` x2))
    (fun _ -> (s1 `star` s2) `vselect` vselect_star_intro_res s1 s2 x1 x2)

let vselect_to_vrefine_2
  (#inames: _)
  (s1 s2: vprop)
  (p: Ghost.erased ((t_of (s1 `star` s2) -> Tot prop)))
  (x1: Ghost.erased (t_of s1))
  (x2: Ghost.erased (t_of s2))
  (sq: squash (Ghost.reveal p (vselect_star_intro_res s1 s2 x1 x2)))
: STGhostT unit inames
  ((s1 `vselect` x1) `star` (s2 `vselect` x2))
  (fun _ -> (s1 `star` s2) `vrefine0` p)
=
  vselect_star_intro s1 s2 x1 x2;
  vselect_to_vrefine (s1 `star` s2) p (vselect_star_intro_res s1 s2 x1 x2) sq

let vselect_star_elim_fst
  (s1 s2: vprop)
  (x: Ghost.erased (t_of (s1 `star` s2)))
: Tot (Ghost.erased (t_of s1))
= fst x

let vselect_star_elim_snd
  (s1 s2: vprop)
  (x: Ghost.erased (t_of (s1 `star` s2)))
: Tot (Ghost.erased (t_of s2))
= snd x

val vselect_star_elim
  (#inames: _)
  (s1 s2: vprop)
  (x: Ghost.erased (t_of (s1 `star` s2)))
: STGhostT unit
    inames
    ((s1 `star` s2) `vselect` x)
    (fun _ -> (s1 `vselect` vselect_star_elim_fst s1 s2 x) `star` (s2 `vselect` vselect_star_elim_snd s1 s2 x))

[@@__steel_reduce__]
let vrewrite (v: vprop) (#t: Type) (f: ((t_of v) -> GTot t)) : Tot vprop =
  vrewrite v f

let vrewrite_intro_res
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: Ghost.erased (t_of s))
: Tot (Ghost.erased t)
= f x

val vrewrite_intro
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: Ghost.erased (t_of s))
: STGhostT unit inames
    (s `vselect` x)
    (fun res -> s `vrewrite` f `vselect` vrewrite_intro_res s f x)

val vrewrite_elim
  (#inames: _)
  (#t: Type)
  (s: vprop)
  (f: t_of s -> GTot t)
  (x: Ghost.erased t)
: STGhost (Ghost.erased (t_of s)) inames
    (s `vrewrite` f `vselect` x)
    (fun res -> s `vselect` res)
    True
    (fun res -> f (Ghost.reveal res) == Ghost.reveal x)

let vdep_intro_res
  (vtag: vprop)
  (tag: Ghost.erased (t_of vtag))
  (vpl0: vprop)
  (pl: Ghost.erased (t_of vpl0))
  (vpl: (t_of vtag -> Tot vprop))
  (sq: squash (vpl0 == vpl tag))
: Tot (Ghost.erased (t_of (vtag `vdep` vpl)))
= Mkdtuple2 #(t_of vtag) #(vdep_payload vtag vpl) (Ghost.reveal tag) (Ghost.reveal pl)

val vdep_intro0
  (#inames: _)
  (vtag: vprop)
  (tag: Ghost.erased (t_of vtag))
  (vpl0: vprop)
  (pl: Ghost.erased (t_of vpl0))
  (vpl: (t_of vtag -> Tot vprop))
  (sq: squash (vpl0 == vpl tag))
: STGhostT unit inames
    ((vtag `vselect` tag) `star` (vpl0 `vselect` pl))
    (fun _ -> (vtag `vdep` vpl) `vselect` vdep_intro_res vtag tag vpl0 pl vpl sq)

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

let vdep_intro
  (#inames: _)
  (vtag: vprop)
  (tag: Ghost.erased (t_of vtag))
  (vpl0: vprop)
  (pl: Ghost.erased (t_of vpl0))
  (vpl: (t_of vtag -> Tot vprop))
: STGhost (Ghost.erased (t_of (vtag `vdep` vpl))) inames
    ((vtag `vselect` tag) `star` (vpl0 `vselect` pl))
    (fun res -> (vtag `vdep` vpl) `vselect` res)
    (vpl0 == vpl tag)
    (fun res ->
      vpl0 == vpl tag /\
      vdep_dfst vtag vpl res == Ghost.reveal tag /\
      vdep_dsnd vtag vpl res == Ghost.reveal pl
    )
=
  let res : Ghost.erased (t_of (vtag `vdep` vpl)) = vdep_intro_res vtag tag vpl0 pl vpl () in
  vdep_intro0 vtag tag vpl0 pl vpl ();
  res

val vdep_elim
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (x: Ghost.erased (t_of (vtag `vdep` vpl)))
: STGhostT unit inames
    ((vtag `vdep` vpl) `vselect` x)
    (fun _ -> (vtag `vselect` (vdep_dfst vtag vpl x)) `star` (vpl (vdep_dfst vtag vpl x) `vselect` (vdep_dsnd vtag vpl x)))

let vdep_elim2_post
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (x: Ghost.erased (t_of (vtag `vdep` vpl)))
  (res: Ghost.erased (t_of vtag))
  (pl: t_of (vpl (Ghost.reveal res)))
: Tot prop
= 
        vdep_dfst vtag vpl x == Ghost.reveal res /\
        (vdep_dsnd vtag vpl x <: t_of (vpl (Ghost.reveal res))) == pl

let vdep_elim2
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (x: Ghost.erased (t_of (vtag `vdep` vpl)))
: STGhostT (Ghost.erased (t_of vtag)) inames
    ((vtag `vdep` vpl) `vselect` x)
    (fun res ->
      (vpl (Ghost.reveal res) `vrefine0` (vdep_elim2_post vtag vpl x res)) `star` 
        (vtag `vselect` res)
    )
=
  vdep_elim vtag vpl x;
  let res = vselect_get vtag () in
  let _ = rewrite_eq_l_gen
    (vpl _)
    (vpl (Ghost.reveal res))
    ()
  in
  vselect_to_vrefine' (vpl _) _ _;
  res

val vselect_injective
  (v: vprop)
  (x1 x2: Ghost.erased (t_of v))
  (m: mem)
: Lemma
  (requires (
    interp (hp_of (v `vselect` x1)) m /\
    interp (hp_of (v `vselect` x2)) m
  ))
  (ensures (x1 == x2))
