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

let dmap_diff (d_shifted d_base: dmap) (offset: nat) : Tot prop 
=  forall (i: nat) . d_shifted i == d_base (offset + i)

let rec dmap_types_shifted
  (processed: nat) (te: tele) (d: dmap)
  (offset: nat) (d': dmap)
: Lemma
  (requires (
    dmap_types processed te d' /\
    dmap_diff d' d offset
  ))
  (ensures (
    dmap_types (offset + processed) te d
  ))
  (decreases te)
= match te with
  | TEnd -> ()
  | T t tp ->
    dmap_types_shifted (processed + 1) (tp (value_of_dmap d' processed t)) d offset d'

let rec tprop_body_of_eprop_shifted
  (processed: nat) (e: eprop) (d: dmap)
  (offset: nat) (d': dmap)
: Lemma
  (requires (
    dmap_types processed (tele_of_eprop e) d' /\
    tprop_body_of_eprop processed e d' /\
    dmap_diff d' d offset
  ))
  (ensures (
    dmap_types (offset + processed) (tele_of_eprop e) d /\
    tprop_body_of_eprop (offset + processed) e d
  ))
  (decreases e)
= dmap_types_shifted processed (tele_of_eprop e) d offset d';
  match e with
  | PEnd _ -> ()
  | P t tp ->
    tprop_body_of_eprop_shifted (processed + 1) (tp (value_of_dmap d' processed t)) d offset d'

let dmap_types_cons
  processed t (te' : t -> tele)  d
: Lemma
  (requires (
    processed >= 0 /\
    type_of_dmap d processed == t /\
    dmap_types (processed + 1) (te' (value_of_dmap d processed t)) d
  ))
  (ensures (
    dmap_types processed (T t te') d
  ))
= ()

let rec dmap_of_eprop
  (e: eprop)
: Ghost dmap
  (requires (
    prop_of_eprop e
  ))
  (ensures (fun y ->
    dmap_types 0 (tele_of_eprop e) y /\
    tprop_body_of_eprop 0 e y
  ))
  (decreases e)
= begin match e as e' returns squash (prop_of_eprop e') -> Ghost dmap (requires True) (ensures fun y -> (dmap_types 0 (tele_of_eprop e) y /\ tprop_body_of_eprop 0 e y)) with
  | PEnd p -> fun _ -> dmap_nil
  | P t tp -> fun _ ->
    let w : t = FStar.IndefiniteDescription.indefinite_description_ghost t (fun x -> prop_of_eprop (tp x)) in
    let d_rec = dmap_of_eprop (tp w) in
    let d_fin = dmap_cons w d_rec in
    tprop_body_of_eprop_shifted 0 (tp w) d_fin 1 d_rec;
    d_fin
  end ()

let tprop_of_eprop_correct
  (e: eprop)
: Lemma
  (requires (prop_of_eprop e))
  (ensures (tprop_of_eprop e))
= let _ = dmap_of_eprop e in
  ()
