module Test

module DM = FStar.DependentMap
module S  = FStar.Pointer
module HH = FStar.HyperHeap
module HS = FStar.HyperStackNG
module HST = FStar.STNG

type fields =
| I
| B

let fields_def (x: fields) : Tot Type = match x with
| I -> int
| B -> bool

let struct = DM.t _ fields_def

let obj = S.pointer struct

let callee
   (pfrom pto: obj)
: HST.Stack int
  (requires (fun h -> S.live h pfrom /\ S.live h pto /\ Modifies.locset_disjoint (S.locset_of_pointer pfrom) (S.locset_of_pointer pto)))
  (ensures (fun h z h' ->
    S.live h pfrom /\ S.live h pto /\
    S.live h' pfrom /\ S.live h' pto /\
    Modifies.modifies (S.locset_of_pointer (S.gfield pto I)) h h' /\
    S.gread h (S.gfield pfrom I) == z /\
    S.gread h' (S.gfield pto I) == z + 1))
= S.write' (S.field pto I) (S.read (S.field pfrom I) + 1);
  S.read (S.field pfrom I)

type more_fields =
| Less
| ThisMore

let more_fields_def (x: more_fields) : Tot Type = match x with
| Less -> struct
| ThisMore -> unit

type more_struct = DM.t _ more_fields_def

let more_obj = S.pointer more_struct

#reset-options "--z3rlimit 128"

abstract
let locset_includes_trans
  (#heap: Type u#a)
  (#root_type: Type u#b)
  (#root_class: Modifies.class' heap 0 root_type)
  (ls0: Modifies.locset root_class)
  (ls1: Modifies.locset root_class)
  (ls2: Modifies.locset root_class)
: Lemma
  (requires (Modifies.locset_includes ls0 ls1 /\ Modifies.locset_includes ls1 ls2))
  (ensures (Modifies.locset_includes ls0 ls2))
  [SMTPatOr [
    [SMTPat (Modifies.locset_includes ls0 ls1); SMTPat (Modifies.locset_includes ls1 ls2)];
    [SMTPat (Modifies.locset_includes ls0 ls1); SMTPat (Modifies.locset_includes ls0 ls2)];
    [SMTPat (Modifies.locset_includes ls1 ls2); SMTPat (Modifies.locset_includes ls0 ls2)];
  ]]
= ()

let locset_of_region_includes_locset_of_pointer
  (#t: Type u#0)
  (r: HH.rid)
  (p: S.pointer t)
: Lemma
  (requires (S.frameOf p == r))
  (ensures (Modifies.locset_includes (HS.locset_of_region r) (S.locset_of_pointer p)))
  [SMTPat (Modifies.locset_includes (HS.locset_of_region r) (S.locset_of_pointer p))]
= Modifies.locset_includes_trans' (S.locset_of_pointer_with_liveness p)

let fresh_frame_modifies
  (m0 m1: HS.mem)
: Lemma
  (requires (HS.fresh_frame m0 m1))
  (ensures (Modifies.modifies HS.locset_of_tip m0 m1))
  [SMTPat (HS.fresh_frame m0 m1)]
= HS.fresh_frame_modifies m0 m1

let locset_includes_empty
  (ls: Modifies.locset HS.root_class)
: Lemma
  (Modifies.locset_includes ls TSet.empty)
  [SMTPat (Modifies.locset_includes ls TSet.empty)]
= ()

let modifies_pop
  (m0: HS.mem)
: Lemma
  (requires (HS.poppable m0))
  (ensures (HS.poppable m0 /\ Modifies.modifies u#0 u#1 (TSet.union HS.locset_of_tip (HS.locset_of_region_with_liveness m0.HS.tip)) m0 (HS.pop m0)))
  [SMTPat (HS.poppable m0)]
= HS.modifies_pop m0

let modifies_trans
  (#heap: Type u#a)
  (#root_type: Type u#b) (#root_class: Modifies.class' heap 0 root_type)
  (s: Modifies.locset root_class )
  (h1 h2 h3: heap)
: Lemma
  (requires (Modifies.modifies s h1 h2 /\ Modifies.modifies s h2 h3))
  (ensures (Modifies.modifies s h1 h3))
  [SMTPatT u#c (Modifies.modifies s h1 h2); SMTPatT (Modifies.modifies s h2 h3)]
= ()

#reset-options "--z3rlimit 16384"

let caller
  ()
: HST.Stack int
  (requires (fun _ -> True))
  (ensures (fun h z h' -> True (* Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) h h' /\  z == 18 *) ))
= let h0 = HST.get () in
  HST.push_frame();
  let h1 = HST.get () in
  let mh0h1 : squash (Modifies.modifies u#0 u#1 (HS.locset_of_tip) h0 h1) =
    assert (Modifies.modifies u#0 u#1 (HS.locset_of_tip) h0 h1)
  in
  let fresh : squash (HS.fresh_frame h0 h1) =
    assert (HS.fresh_frame h0 h1)
  in
  let r = h1.HS.tip in
  let not_live : squash (~ (HS.live_region h0 r)) =
    assert (~ (HS.live_region h0 r))
  in
  let ofrom : obj = S.screate' (DM.create #fields #fields_def (function | I -> 18 | B -> true)) in
  let h12 = HST.get () in
  let mh1h12 : squash (Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) h1 h12) =
    assert (Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) h1 h12)
  in
  let moto : more_obj = S.screate' (DM.create #more_fields #more_fields_def (function | Less -> DM.create #fields #fields_def (function  | I -> 1729 | B -> false ) | ThisMore -> ())) in
  let pfrom : obj = ofrom in
  let pto : obj = S.field moto Less in
  let h15 = HST.get () in
  let mh12h15 : squash (Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) h12 h15) =
    assert (Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) h12 h15)
  in
  let z = callee pfrom pto in
  let h17 = HST.get () in
  let mh15h17 : squash (Modifies.modifies (S.locset_of_pointer (S.gfield pto I)) h15 h17) = 
    assert (Modifies.modifies (S.locset_of_pointer (S.gfield pto I)) h15 h17)
  in
  HST.pop_frame ();
  let h2 = HST.get () in
  let mh17h2 : squash (Modifies.modifies u#0 u#1 (TSet.union HS.locset_of_tip (HS.locset_of_region_with_liveness r)) h17 h2) =
    assert (Modifies.modifies u#0 u#1 (TSet.union HS.locset_of_tip (HS.locset_of_region_with_liveness r)) h17 h2)
  in
  let s : Modifies.locset HS.root_class =
    TSet.union HS.locset_of_tip (HS.locset_of_region_with_liveness r)
  in
  let s_includes_empty : squash (Modifies.locset_includes s TSet.empty) =
    assert (Modifies.locset_includes s TSet.empty)
  in
  let s_includes_tip : squash (Modifies.locset_includes s HS.locset_of_tip) =
    assert (Modifies.locset_includes s HS.locset_of_tip)
  in
  let s_includes_region_with_liveness : squash (Modifies.locset_includes s (HS.locset_of_region_with_liveness r)) =
    assert (Modifies.locset_includes s (HS.locset_of_region_with_liveness r))
  in
  let s_includes_region : squash (Modifies.locset_includes s (HS.locset_of_region r)) =
    assert (Modifies.locset_includes s (HS.locset_of_region r))
  in
  let s_includes_pto_i : squash (Modifies.locset_includes s (S.locset_of_pointer (S.gfield pto I))) =
    assert (Modifies.locset_includes s (S.locset_of_pointer (S.gfield pto I)))
  in
  let _ : squash (Modifies.modifies s h0 h1) =
    mh0h1;
    s_includes_tip;
    ()
  in
  (*
  let _ : squash (Modifies.modifies u#0 u#1 s h1 h12) =
    mh1h12;
    s_includes_empty;
    ()
  in
  let _ : squash (Modifies.modifies u#0 u#1 s h12 h15) =
    mh12h15;
    s_includes_empty;
    ()
  in
  let _ : squash (Modifies.modifies s h15 h17) =
    mh15h17;
    s_includes_pto_i;
    ()
  in
  let _ : squash (Modifies.modifies u#0 u#1 s h17 h2) =
    mh17h2
  in
  *)
(*
  assert (Modifies.modifies s h0 h2);
*)
(*
  let _ : squash (Modifies.modifies u#0 u#1 (TSet.empty #(Modifies.loc HS.root_class)) h0 h2) =
    HS.modifies_not_live_region r TSet.empty h0 h2
  in
*)
  z
