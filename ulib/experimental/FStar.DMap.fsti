module FStar.DMap

noeq
type tele : nat -> Type = | TEnd: tele 0 | T: (n : nat) -> (t: Type0) -> (t -> tele n) -> tele (n + 1)

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
  match te with
  | TEnd -> True
  | T _ t te' ->
    type_of_dmap d processed == t /\
    dmap_types (processed + 1) (remaining - 1) (te' (value_of_dmap d processed t)) d

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

val tprop_of_eprop_correct
  (n: nat)
  (e: eprop n)
: Lemma
  (requires (prop_of_eprop n e))
  (ensures (tprop_of_eprop n e))

(*
val testp : nat -> nat -> prop

[@@norm_dmap]
let test1 = P _ _ (fun (i1: nat) -> P _ _ (fun (i2: nat) -> P _ _ (fun (i3: nat) -> PEnd (testp (i1 + i2) i3))))

[@@ FStar.Tactics.(postprocess_with (fun _ -> norm [delta_attr [`%norm_dmap]; zeta; iota; primops]; trefl ())) ]
let test1_before = prop_of_eprop _ test1

[@@ FStar.Tactics.(postprocess_with (fun _ -> norm [delta_attr [`%norm_dmap]; zeta; iota; primops]; trefl ())) ]
let test1_after = tprop_of_eprop _ test1

let _ : squash (test1_before) -> Lemma (test1_after) = fun _ -> tprop_of_eprop_correct _ test1
