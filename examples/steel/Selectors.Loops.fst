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

let fact_test_pre
  (n: nat)
  (dist: Ghost.erased nat)
  (x: (nat & nat))
: Tot prop
= let vi = fst x in
  let vres = snd x in
  vres == fact vi /\ vi + Ghost.reveal dist == n

[@@ __steel_reduce__; __reduce__ ] // necessary for t_of
let fact_test_vprop
  (i: ref nat)
  (res: ref nat)
  (dist: Ghost.erased nat)
: Tot vprop
= (vptr i `star` vptr res)

let fact_test_post
  (n: nat)
  (b: bool)
  (dist: Ghost.erased nat)
  (x: (nat & nat))
: Tot prop
= fact_test_pre n dist x /\
  b == (Ghost.reveal dist > 0)

let fact_test
  (n: nat)
  (i: ref nat)
  (res: ref nat)
  (dist: Ghost.erased nat)
: SteelSel bool
    (fact_test_vprop i res dist)
    (fun b -> fact_test_vprop i res dist)
    (fun h -> fact_test_pre n dist (h (fact_test_vprop i res dist)))
    (fun _ b h' -> fact_test_post n b dist (h' (fact_test_vprop i res dist)))
=
  change_equal_slprop
    (fact_test_vprop i res dist)
    (vptr i `star` vptr res);
  reveal_star (vptr i) (vptr res);
  let gres = gget (vptr res) in
  let vi = read i in
  assert (Ghost.reveal gres == fact vi);
  assert (vi + Ghost.reveal dist == n);
  let b = (vi < n) in
  reveal_star (vptr i) (vptr res);
  change_equal_slprop
    (vptr i `star` vptr res)
    (fact_test_vprop i res dist);
  return b

let fact_body
  (n: nat)
  (i: ref nat)
  (res: ref nat)
  (dist: Ghost.erased nat)
: SteelSel (Ghost.erased nat)
    (fact_test_vprop i res dist)
    (fun dist -> fact_test_vprop i res dist)
    (fun h -> fact_test_post n true dist (h (fact_test_vprop i res dist)))
    (fun _ dist' h' -> fact_test_pre n dist' (h' (fact_test_vprop i res dist')) /\ Ghost.reveal dist' << Ghost.reveal dist)
=
  change_equal_slprop
    (fact_test_vprop i res dist)
    (vptr i `star` vptr res);
  reveal_star (vptr i) (vptr res);
  let vi = read i in
  let vj = vi + 1 in
  let vres = read res in
  write res (vj * vres);
  write i vj;
  let dist' = Ghost.hide (Ghost.reveal dist - 1) in
  let gres = gget (vptr res) in
  let gi = gget (vptr i) in
  assert (Ghost.reveal gres == fact (Ghost.reveal gi));
  assert (Ghost.reveal gi + Ghost.reveal dist' == n);
  reveal_star (vptr i) (vptr res);
  change_equal_slprop
    (vptr i `star` vptr res)
    (fact_test_vprop i res dist');
  return dist'

// (* this is necessary, otherwise verification of steel_fact fails to show fact_test_pre
//      without the call to get *)
// let alloc (#t: Type0) (x: t) : SteelSel (ref t)
//   emp
//   (fun res -> vptr res)
//   (fun _ -> True)
//   (fun _ res h' -> h' (vptr res) == x /\ not (is_null res))
// = alloc x

let steel_fact
  (n: nat)
: SteelSel nat
    emp
    (fun _ -> emp)
    (fun _ -> True)
    (fun _ res _ -> res == fact n)
= let _ = get() in
  let i = alloc 0 in
  let res = alloc 1 in
  let dist = Ghost.hide n in
  reveal_star (vptr i) (vptr res);
  // change_equal_slprop
  //   (vptr i `star` vptr res)
  //   (fact_test_vprop i res dist);
  let dist' = while _ (fact_test_vprop i res) (fact_test_pre n) (fun _ -> fact_test_vprop i res) (fact_test_post n) (fact_test n i res) (fact_body n i res) dist in
  // change_equal_slprop
  //   (fact_test_vprop i res dist')
  //   (vptr i `star` vptr res);
  reveal_star (vptr i) (vptr res);
  let gi = gget (vptr i) in // necessary to tell Z3 to show that i == n
  let vres = read res in
  free res;
  free i;
  return vres
