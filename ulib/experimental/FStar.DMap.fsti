module FStar.DMap

noeq
type tele : nat -> Type = | TEnd: tele 0 | T: (n : nat) -> (t: Type0) -> (t -> tele n) -> tele (n + 1)

let rec type_of_tele (n: nat) (te: tele n) : Tot Type0 =
  if n = 0
  then unit
  else
    let T _ t te' = te in
    if n = 1
    then t
    else dtuple2 t (fun x -> type_of_tele (n - 1) (te' x))

val dmap : Type u#1

val type_of_dmap (d: dmap) (i: nat) : Tot Type0

val value_of_dmap (d: dmap) (i: nat) (t: Type0) : Pure t
  (requires (type_of_dmap d i == t))
  (ensures (fun _ -> True))

val norm_dmap : unit

[@@norm_dmap]
let rec dmap_types (processed: nat) (remaining: nat) (te: tele remaining) (d: dmap) : Tot prop
  (decreases remaining)
=
  if remaining = 0
  then True
  else
    let T _ t te' = te in
    type_of_dmap d processed == t /\ dmap_types (processed + 1) (remaining - 1) (te' (value_of_dmap d processed t)) d

noeq
type eprop : nat -> Type = | PEnd: prop -> eprop 0 | P: (n : nat) -> (t: Type0) -> (t -> eprop n) -> eprop (n + 1)

[@@norm_dmap]
let rec prop_of_eprop (n: nat) (e: eprop n) : Tot prop =
  match e with
  | PEnd p -> p
  | P _ t tp -> exists (x: t) . prop_of_eprop _ (tp x)

[@@norm_dmap]
let rec tele_of_eprop (n: nat) (e: eprop n) : Tot (tele n) =
  match e with
  | PEnd _ -> TEnd
  | P _ t tp -> T _ t (fun x -> tele_of_eprop _ (tp x))

[@@norm_dmap]
let rec tprop_body_of_eprop (processed: nat) (remaining: nat) (e: eprop remaining) (d: dmap { dmap_types processed remaining (tele_of_eprop _ e) d }) : Tot prop
  (decreases remaining)
= match e with
  | PEnd p -> p
  | P _ t tp -> tprop_body_of_eprop (processed + 1) (remaining - 1) (tp (value_of_dmap d processed t)) d

[@@norm_dmap]
let tprop_of_eprop (n: nat) (e: eprop n) : Tot prop =
  exists (d: dmap { dmap_types 0 n (tele_of_eprop n e) d }) . tprop_body_of_eprop 0 n e d

[@@norm_dmap]
let test1 = P _ _ (fun (i1: nat) -> P _ _ (fun (i2: nat) -> P _ _ (fun (i3: nat) -> PEnd (i1 + i2 + i3 + 1 == 0))))

[@@ FStar.Tactics.(postprocess_with (fun _ -> norm [delta_attr [`%norm_dmap]; zeta; iota; primops]; trefl ())) ]
let test1_before = prop_of_eprop _ test1

[@@ FStar.Tactics.(postprocess_with (fun _ -> norm [delta_attr [`%norm_dmap]; zeta; iota; primops]; trefl ())) ]
let test1_after = tprop_of_eprop _ test1

let _ : squash (test1_after ==> test1_before) = ()



// let test2 : prop = _ by (FStar.Tactics.

(*

let dmap_out_of_domain (n: nat) (d: dmap) : Tot prop =
  (forall (i: nat) . i >= n ==> type_of_dmap d i == squash False)

let eq_until (n: nat) (d1 d2: dmap) : Tot prop = (forall (i: nat) . i < n ==> (let t1 = type_of_dmap d1 i in let t2 = type_of_dmap d2 i in t1 == t2 /\ value_of_dmap d1 i t1 == value_of_dmap d2 i t2))

let ext_until
  (n: nat)
  (p: dmap -> Tot prop)
: Tot prop
= forall (d1 d2: dmap) . (eq_until n d1 d2 /\ p d1) ==> p d2
