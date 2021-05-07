module Selectors.Loops

open Steel.SelEffect
open Steel.SelEffect.Atomic
open Steel.SelLoops
open Steel.SelReference
open FStar.Mul

(* Specification *)
let rec fact
  (n: nat)
: GTot nat
= if n = 0
  then 1
  else n * fact (n - 1)

(* Steel implementation *)

let fact_test_vpre_refine
  (n: nat)
  (i: ref nat)
  (res: ref nat)
  (dist: Ghost.erased nat)
  (x: (nat & nat))
: Tot prop
= let vi = fst x in
  let vres = snd x in
  vres == fact vi /\ vi + Ghost.reveal dist == n

let fact_test_vpre
  (n: nat)
  (i: ref nat)
  (res: ref nat)
  (dist: Ghost.erased nat)
: Tot vprop
= (vptr i `star` vptr res) `vrefine` (fact_test_vpre_refine n i res dist)

let fact_test_vpost_refine
  (dist: Ghost.erased nat)
  (b: bool)
  (_: t_of emp)
: Tot prop
= b == (Ghost.reveal dist > 0)

let fact_test_vpost
  (n: nat)
  (i: ref nat)
  (res: ref nat)
  (b: bool)
  (dist: Ghost.erased nat)
: Tot vprop
= fact_test_vpre n i res dist `star` (emp `vrefine` fact_test_vpost_refine dist b)

let fact_test
  (n: nat)
  (i: ref nat)
  (res: ref nat)
  (dist: Ghost.erased nat)
: SteelSelT bool
    (fact_test_vpre n i res dist)
    (fun b -> fact_test_vpost n i res b dist)
= change_equal_slprop
    (fact_test_vpre n i res dist)
    ((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist);
  elim_vrefine
    (vptr i `star` vptr res)
    (fact_test_vpre_refine n i res dist);
  reveal_star (vptr i) (vptr res);
  let vi = read i in
  let b = (vi < n) in
  reveal_star (vptr i) (vptr res);
  intro_vrefine
    (vptr i `star` vptr res)
    (fact_test_vpre_refine n i res dist);
  intro_vrefine
    emp
    (fact_test_vpost_refine dist b);
  assert_norm (
    ((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist) `star` (emp `vrefine` fact_test_vpost_refine dist b) ==
    fact_test_vpost n i res b dist
  );
  change_equal_slprop
    (((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist) `star` (emp `vrefine` fact_test_vpost_refine dist b))
    (fact_test_vpost n i res b dist);
  return b

let change_equal_slprop_with_squash (#opened:_) (p q: vprop)
  (sq: squash (p == q))
  : SteelSelGhost unit opened p (fun _ -> q) (fun _ -> True) (fun h0 _ h1 -> p == q /\ h1 q == h0 p)
=
  change_equal_slprop p q

let fact_body
  (n: nat)
  (i: ref nat)
  (res: ref nat)
  (dist: Ghost.erased nat)
: SteelSel (Ghost.erased nat)
    (fact_test_vpost n i res true dist)
    (fun dist -> fact_test_vpre n i res dist)
    (fun _ -> True)
    (fun _ dist' _ -> Ghost.reveal dist' << Ghost.reveal dist)
=
  let sq : squash (
    ((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist) `star` (emp `vrefine` fact_test_vpost_refine dist true) ==
    fact_test_vpost n i res true dist
  ) = () in
  change_equal_slprop_with_squash
    (fact_test_vpost n i res true dist)
    (((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist) `star` (emp `vrefine` fact_test_vpost_refine dist true))
    sq;
  elim_vrefine
    emp
    (fact_test_vpost_refine dist true);
  elim_vrefine
    (vptr i `star` vptr res)
    (fact_test_vpre_refine n i res dist);
  reveal_star (vptr i) (vptr res);
  let vi = read i in
  let vj = vi + 1 in
  let vres = read res in
  write res (vj * vres);
  write i vj;
  reveal_star (vptr i) (vptr res);
  let dist' = Ghost.hide (Ghost.reveal dist - 1) in
  intro_vrefine
    (vptr i `star` vptr res)
    (fact_test_vpre_refine n i res dist');
  let sq : squash (
    ((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist')
      == fact_test_vpre n i res dist'
  ) = _ by (FStar.Tactics.trefl ()) in
  change_equal_slprop_with_squash
    ((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist')
    (fact_test_vpre n i res dist')
    ();
  return dist'

(* this is necessary, otherwise verification of steel_fact fails to show fact_test_pre *)
let alloc (#t: Type0) (x: t) : SteelSel (ref t)
  emp
  (fun res -> vptr res)
  (fun _ -> True)
  (fun _ res h' -> h' (vptr res) == x /\ not (is_null res))
= alloc x

let steel_fact
  (n: nat)
: SteelSel nat
    emp
    (fun _ -> emp)
    (fun _ -> True)
    (fun _ res _ -> res == fact n)
=
  let i = alloc 0 in 
  let res = alloc 1 in
  let dist = Ghost.hide n in
  reveal_star (vptr i) (vptr res);
  intro_vrefine
    (vptr i `star` vptr res)
    (fact_test_vpre_refine n i res dist);
  assert_norm
    ((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist ==
    fact_test_vpre n i res dist);
  change_equal_slprop
    ((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist)
    (fact_test_vpre n i res dist);
  let dist' = while _ (fact_test_vpre n i res) (fact_test_vpost n i res) (fact_test n i res) (fact_body n i res) dist in
  assert_norm
    (fact_test_vpost n i res false dist' ==
    ((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist') `star` (emp `vrefine` fact_test_vpost_refine dist' false));
  change_equal_slprop
    (fact_test_vpost n i res false dist')
    (((vptr i `star` vptr res) `vrefine` fact_test_vpre_refine n i res dist') `star` (emp `vrefine` fact_test_vpost_refine dist' false));
  elim_vrefine
    emp
    (fact_test_vpost_refine dist' false);
  elim_vrefine
    (vptr i `star` vptr res)
    (fact_test_vpre_refine n i res dist');
  reveal_star (vptr i) (vptr res);
  let gi = gget (vptr i) in // necessary to tell Z3 to show that i == n
  let vres = read res in
  free res;
  free i;
  return vres
