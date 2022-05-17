module FStar.DMap

noeq
type tele : Type = | TEnd: tele | T: (t: Type0) -> (t -> tele) -> tele

[@@erasable; must_erase_for_extraction]
val dmap : Type u#1

val type_of_dmap (d: dmap) (i: nat) : Tot Type0

val value_of_dmap (d: dmap) (i: nat) (t: Type0) : Ghost t
  (requires (type_of_dmap d i == t))
  (ensures (fun _ -> True))

val norm_dmap : unit

[@@norm_dmap]
let rec dmap_types (processed: nat) (te: tele) (d: dmap) : Tot prop
  (decreases te)
=
  match te with
  | TEnd -> True
  | T t te' ->
    type_of_dmap d processed == t /\
    dmap_types (processed + 1) (te' (value_of_dmap d processed t)) d

noeq
type eprop : Type = | PEnd: prop -> eprop | P: (t: Type0) -> (t -> eprop) -> eprop

[@@norm_dmap]
let rec prop_of_eprop (e: eprop) : Tot prop =
  match e with
  | PEnd p -> p
  | P t tp -> exists (x: t) . prop_of_eprop (tp x)

[@@norm_dmap]
let rec tele_of_eprop (e: eprop) : Tot (tele) =
  match e with
  | PEnd _ -> TEnd
  | P t tp -> T t (fun x -> tele_of_eprop (tp x))

[@@norm_dmap]
let rec tprop_body_of_eprop (processed: nat) (e: eprop) (d: dmap { dmap_types processed (tele_of_eprop e) d }) : Tot prop
  (decreases e)
= match e with
  | PEnd p -> p
  | P t tp -> tprop_body_of_eprop (processed + 1) (tp (value_of_dmap d processed t)) d

[@@norm_dmap]
let tprop_of_eprop (e: eprop) : Tot prop =
  exists (d: dmap { dmap_types 0 (tele_of_eprop e) d }) . tprop_body_of_eprop 0 e d

val tprop_of_eprop_correct
  (e: eprop)
: Lemma
  (requires (prop_of_eprop e))
  (ensures (tprop_of_eprop e))

(*
val testp : nat -> nat -> prop

[@@norm_dmap]
let test1 = P _ (fun (i1: nat) -> P _ (fun (i2: nat) -> P _ (fun (i3: nat) -> PEnd (testp (i1 + i2) i3))))

[@@ FStar.Tactics.(postprocess_with (fun _ -> norm [delta_attr [`%norm_dmap]; zeta; iota; primops]; trefl ())) ]
let test1_before = prop_of_eprop test1

[@@ FStar.Tactics.(postprocess_with (fun _ -> norm [delta_attr [`%norm_dmap]; zeta; iota; primops]; trefl ())) ]
let test1_after = tprop_of_eprop test1

let _ : squash (test1_before) -> Lemma (test1_after) = fun _ -> tprop_of_eprop_correct test1
