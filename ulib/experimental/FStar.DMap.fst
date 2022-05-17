module FStar.DMap

let dmap = nat -> GTot (t: Type0 & t)

let type_of_dmap (d: dmap) (i: nat) : Tot Type0 = dfst (d i)

let value_of_dmap (d: dmap) (i: nat) (t: Type0) : Ghost t
  (requires (type_of_dmap d i == t))
  (ensures (fun _ -> True))
= dsnd (d i)

irreducible let norm_dmap : unit = ()

let dmap_nil : dmap = fun _ -> (| unit, () |)

let dmap_cons (#t: Type0) (x: t) (tl: dmap) : Tot dmap =
  fun n -> if n = 0 then (| t, x |) else tl (n - 1)

// assume val
let
dmap_diff (d_shifted d_base: dmap) (offset: nat) : Tot prop 
=  forall (i: nat) . d_shifted i == d_base (offset + i)

// assume val
let
dmap_diff_elim (d_shifted d_base: dmap) (offset: nat) (i: nat) (t: Type0) : Lemma
    (requires (
      dmap_diff d_shifted d_base offset /\
      (t == type_of_dmap d_shifted i \/ t == type_of_dmap d_base (offset + i))
    ))
    (ensures (
      type_of_dmap d_shifted i == type_of_dmap d_base (offset + i) /\
      value_of_dmap d_shifted i t == value_of_dmap d_base (offset + i) t
    ))
= ()

#push-options "--z3rlimit 64"
#restart-solver

let rec dmap_types_shifted
  (processed: nat) (remaining: nat) (te: tele remaining) (d: dmap)
  (offset: nat) (d': dmap)
: Lemma
  (requires (
    dmap_types processed remaining te d' /\
    dmap_diff d' d offset
  ))
  (ensures (
    dmap_types (offset + processed) remaining te d
  ))
  (decreases remaining)
= begin match te as te' returns squash (dmap_types processed remaining te' d') -> squash (dmap_types (offset + processed) remaining te' d) with
  | TEnd -> fun _ -> ()
  | T _ t tp -> fun _ ->
    dmap_diff_elim d' d offset processed t;
//    assert_norm (dmap_types processed remaining (T _ t tp) d' == (type_of_dmap d' processed == t /\ dmap_types (processed + 1) (remaining - 1) (tp (value_of_dmap d' processed t)) d'));
//    assert_norm (dmap_types (offset + processed) remaining (T _ t tp) d == (type_of_dmap d (offset + processed) == t /\ dmap_types ((offset + processed) + 1) (remaining - 1) (tp (value_of_dmap d (offset + processed) t)) d));
    dmap_types_shifted (processed + 1) (remaining - 1) (tp (value_of_dmap d' processed t)) d offset d'
  end ()

#pop-options

#push-options "--z3rlimit 128"
#restart-solver

let rec tprop_body_of_eprop_shifted
  (processed: nat) (remaining: nat) (e: eprop remaining) (d: dmap)
  (offset: nat) (d': dmap)
: Lemma
  (requires (
    dmap_types processed remaining (tele_of_eprop _ e) d' /\
    tprop_body_of_eprop processed remaining e d' /\
    dmap_diff d' d offset
  ))
  (ensures (
    dmap_types (offset + processed) remaining (tele_of_eprop _ e) d /\
    tprop_body_of_eprop (offset + processed) remaining e d
  ))
  (decreases remaining)
= dmap_types_shifted processed remaining (tele_of_eprop _ e) d offset d';
  begin match e as e' returns squash (
    dmap_types processed remaining (tele_of_eprop _ e') d' /\
    tprop_body_of_eprop processed remaining e' d' /\
    dmap_types (offset + processed) remaining (tele_of_eprop _ e') d
  ) -> squash (
    tprop_body_of_eprop (offset + processed) remaining e' d
  )
  with
  | PEnd _ -> fun _ -> ()
  | P _ t tp -> fun _ ->
    dmap_diff_elim d' d offset processed t;
    tprop_body_of_eprop_shifted (processed + 1) (remaining - 1) (tp (value_of_dmap d' processed t)) d offset d'
  end ()

#pop-options

let dmap_types_cons
  processed t (n: nat) (te' : t -> tele n)  d
: Lemma
  (requires (
    let remaining = n + 1 in
    processed >= 0 /\
    type_of_dmap d processed == t /\
    dmap_types (processed + 1) (remaining - 1) (te' (value_of_dmap d processed t)) d
  ))
  (ensures (
    let remaining = n + 1 in
    dmap_types processed remaining (T n t te') d
  ))
= ()

#push-options "--z3rlimit 64"
#restart-solver

let rec dmap_of_eprop
  (n: nat)
  (e: eprop n)
: Ghost dmap
  (requires (
    prop_of_eprop n e
  ))
  (ensures (fun y ->
    dmap_types 0 n (tele_of_eprop _ e) y /\
    tprop_body_of_eprop 0 n e y
  ))
  (decreases n)
= begin match e as e' returns (squash (prop_of_eprop n e') -> Ghost dmap True (fun y ->
    dmap_types 0 n (tele_of_eprop _ e') y /\
    tprop_body_of_eprop 0 n e' y
  )) with
  | PEnd p -> fun _ -> dmap_nil
  | P n' t tp -> fun _ ->
    let w : t = FStar.IndefiniteDescription.indefinite_description_ghost t (fun x -> prop_of_eprop _ (tp x)) in
    let d_rec = dmap_of_eprop (n - 1) (tp w) in
    let d_fin = dmap_cons w d_rec in
    assert (dmap_diff d_rec d_fin 1);
    tprop_body_of_eprop_shifted 0 (n - 1) (tp w) d_fin 1 d_rec;
    assert (type_of_dmap d_fin 0 == t);
    assert (dmap_types (0 + 1) (n - 1) (tele_of_eprop _ (tp (value_of_dmap d_fin 0 t))) d_fin);
    dmap_types_cons 0 t n' (fun x -> tele_of_eprop _ (tp x)) d_fin;
    d_fin
  end ()

#pop-options

let tprop_of_eprop_correct
  (n: nat)
  (e: eprop n)
: Lemma
  (requires (prop_of_eprop n e))
  (ensures (tprop_of_eprop n e))
= let _ = dmap_of_eprop n e in
  ()
