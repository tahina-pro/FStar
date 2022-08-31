module Steel.ST.UntypedReference
open Steel.ST.GenElim

module R = Steel.ST.Reference

assume val uref : Type0

assume val uref_of_ref (#t: Type) (r: R.ref t) : Tot uref

[@@__reduce__]
let upts_to0 (r: uref) (#t: Type) (p: perm) (v: t) : Tot vprop =
  exists_ (fun (r': R.ref t) -> R.pts_to r' p v `star` pure (uref_of_ref r' == r))

let upts_to (r: uref) (#t: Type) (p: perm) (v: t) : Tot vprop =
  upts_to0 r p v

assume val uread (#t: Type) (#opened: _) (#p: perm) (#v: Ghost.erased t) (r: uref) : STAtomic t opened
  (upts_to r #t p (Ghost.reveal v))
  (fun _ -> upts_to r #t p (Ghost.reveal v))
  True
  (fun v' -> v' == Ghost.reveal v)

assume val uwrite (#t: Type) (#opened: _) (#v: Ghost.erased t) (r: uref) (v': t) : STAtomicT unit opened
  (upts_to r #t full_perm (Ghost.reveal v))
  (fun _ -> upts_to r #t full_perm v')

let ualloc (#t: Type) (v: t) : STT uref
  emp
  (fun r -> upts_to r full_perm v)
= let r' = R.alloc v in
  let r = uref_of_ref r' in
  noop ();
  rewrite
    (upts_to0 r full_perm v)
    (upts_to r full_perm v);
  return r

assume val uref_of_ref_unique
  (#opened: _)
  (#t1: Type) (r1: R.ref t1) (p1: perm) (v1: t1)
  (#t2: Type) (r2: R.ref t2) (p2: perm) (v2: t2)
: STGhost unit opened
    (R.pts_to r1 p1 v1 `star` R.pts_to r2 p2 v2)
    (fun _ -> R.pts_to r1 p1 v1 `star` R.pts_to r2 p2 v2)
    (uref_of_ref r1 == uref_of_ref r2)
    (fun _ ->
      t1 == t2 /\
      v1 == v2
    )

let upts_to_unique
  (#opened: _)
  (r: uref)
  (#t1: Type) (p1: perm) (v1: t1)
  (#t2: Type) (p2: perm) (v2: t2)
: STGhost unit opened
    (upts_to r p1 v1 `star` upts_to r p2 v2)
    (fun _ -> upts_to r p1 v1 `star` upts_to r p2 v2)
    True
    (fun _ ->
      t1 == t2 /\
      v1 == v2
    )
= rewrite
    (upts_to r p1 v1)
    (upts_to0 r p1 v1);
  let _ = gen_elim () in
  let r1 = vpattern_replace (fun r -> R.pts_to r _ _) in
  rewrite
    (upts_to r p2 v2)
    (upts_to0 r p2 v2);
  let _ = gen_elim () in
  let r2 = vpattern_replace (fun (r: R.ref t2) -> R.pts_to r _ _) in
  uref_of_ref_unique r1 _ _ r2 _ _;
  rewrite
    (upts_to0 r p1 v1)
    (upts_to r p1 v1);
  rewrite
    (upts_to0 r p2 v2)
    (upts_to r p2 v2)

[@@erasable]
noeq
type base_type_inv
  (r: uref)
  (t0: Type)
  (vp: vprop)
= {
    inv_reveal:
      (opened: _) ->
      STGhostT t0 opened
        (vp)
        (fun v -> upts_to r (half_perm full_perm) v);
    inv_hide:
      (opened: _) ->
      (v: t0) ->
      STGhostT unit opened
        (upts_to r (half_perm full_perm) v)
        (fun _ -> vp)
  }

let mk_base_type_inv
  (r: uref)
  (t0: Type)
: Tot (base_type_inv r t0 (exists_ (upts_to r #t0 (half_perm full_perm))))
= {
    inv_reveal = (fun _ ->
      let _ = gen_elim () in
      vpattern_replace (upts_to r #t0 (half_perm full_perm))
    );
    inv_hide = (fun _ v ->
      intro_exists v (upts_to r #t0 (half_perm full_perm))
    );
  }

let inv_reveal
  (#r: uref)
  (#t0: Type)
  (#vp: vprop)
  (#opened: _)
  (i: base_type_inv r t0 vp)
: STGhostT (Ghost.erased t0) opened
    (vp)
    (fun gv -> upts_to r (half_perm full_perm) (Ghost.reveal gv))
= let v = i.inv_reveal opened in
  let gv : Ghost.erased t0 = Ghost.hide v in
  rewrite
    (upts_to r #t0 (half_perm full_perm) _)
    (upts_to r #t0 (half_perm full_perm) (Ghost.reveal gv));
  gv

let inv_hide
  (#r: uref)
  (#t0: Type)
  (#vp: vprop)
  (#opened: _)
  (i: base_type_inv r t0 vp)
  (v: t0)
: STGhostT unit opened
    (upts_to r (half_perm full_perm) v)
    (fun _ -> vp)
= i.inv_hide opened v

let base_type_inv_idem
  (#r: uref)
  (#t0: Type)
  (#vp: vprop)
  (#opened: _)
  (i: base_type_inv r t0 vp)
  (#t: Type)
  (p: perm)
  (v: t)
: STGhostT (squash (t == t0)) opened
    (vp `star` upts_to r p v)
    (fun _ -> vp `star` upts_to r p v)
= let _ = inv_reveal i in
  upts_to_unique r p v _ _;
  inv_hide i _

let is_base_type
  (r: uref)
  (i: iname)
  (t0: Type)
: Tot prop
= exists (vp: vprop) . exists (f: base_type_inv r t0 vp) . (i >--> vp)

let has_base_type
  (r: uref)
  (i: iname)
: Tot prop
= exists (t0: Type) . is_base_type r i t0

let has_base_type_intro_gen
  (r: uref)
  (i: iname)
  (t0: Type)
  (vp: vprop)
  (f: base_type_inv r t0 vp)
: Lemma
  (requires (i >--> vp))
  (ensures (has_base_type r i))
= ()

let has_base_type_intro
  (r: uref)
  (i: iname)
  (t0: Type)
: Lemma
  (requires (i >--> exists_ (upts_to r #t0 (half_perm full_perm))))
  (ensures (has_base_type r i))
= let f: base_type_inv r t0 _ = mk_base_type_inv r t0 in
  has_base_type_intro_gen r i t0 _ f

let get_base_type
  (r: uref)
  (i: iname)
: Pure Type
    (requires (has_base_type r i))
    (ensures (fun t0 -> is_base_type r i t0))
= FStar.IndefiniteDescription.indefinite_description_ghost Type (fun t0 -> is_base_type r i t0)

let get_inv
  (r: uref)
  (i: iname)
: Pure vprop
    (requires (has_base_type r i))
    (ensures (fun vp -> exists (f: base_type_inv r (get_base_type r i) vp) . (i >--> vp)))
= let t0 = get_base_type r i in
  FStar.IndefiniteDescription.indefinite_description_ghost vprop (fun vp -> exists (f: base_type_inv r (get_base_type r i) vp) . (i >--> vp))

let get_inv_acc
  (r: uref)
  (i: iname)
  (_: squash (has_base_type r i))
: Pure (base_type_inv r (get_base_type r i) (get_inv r i))
    (requires True)
    (ensures (fun _ -> (i >--> get_inv r i)))
= let vp = get_inv r i in
  FStar.IndefiniteDescription.indefinite_description_ghost (base_type_inv r (get_base_type r i) vp) (fun _ -> (i >--> vp))

let with_invariant_g_f (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#opened_invariants:inames)
                     (#p:vprop)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     (f:unit -> STGhostT a (add_inv opened_invariants i)
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : STGhostF a opened_invariants fp fp' True (fun _ -> True)
= with_invariant_g i f

let has_base_type_idem
  (#opened: _)
  (r: uref)
  (i: iname)
  (#t: Type)
  (p: perm)
  (v: t)
  (sq: squash (
    not (mem_inv opened i) /\
    has_base_type r i
  ))
: STGhostT (squash (t == get_base_type r i)) opened
    (upts_to r p v)
    (fun _ -> upts_to r p v)
= with_invariant_g_f #_ #(upts_to r p v) #(fun _ -> upts_to r p v)  #_ #(get_inv r i) i (fun _ ->
    base_type_inv_idem #r #(get_base_type r i) #(get_inv r i) (get_inv_acc r i ()) p v
  )

module P = Steel.C.PCM
module C = Steel.C.Connection

noeq
type ptr (a: Type u#a) : (Type u#a) = {
  base: uref;
  base_inv: Ghost.erased iname;
  base_has_type: squash (has_base_type base base_inv);
  base_pcm: P.pcm (get_base_type base base_inv);
  target_pcm: P.pcm a;
  base_to_target_conn: C.connection base_pcm target_pcm;
}

let freeable (#a: Type) (p: ptr a) : Tot prop =
  get_base_type p.base p.base_inv == a /\
  p.target_pcm == p.base_pcm /\
  p.base_to_target_conn == C.connection_id _

[@@__reduce__]
let pts_to0
  (#a: Type)
  (p: ptr a)
  (v: a)
: Tot vprop
= exists_ (fun (v0: get_base_type p.base p.base_inv) ->
    upts_to p.base #(get_base_type p.base p.base_inv) (half_perm full_perm) v0 `star`
    pure (v == p.base_to_target_conn.conn_large_to_small.morph v0)
  )

let pts_to
  (#a: Type)
  (p: ptr a)
  (v: a)
: Tot vprop
= pts_to0 #a p v

let alloc
  (#a: Type0)
  (pcm: P.pcm a)
  (v: a)
: ST (ptr a)
    emp
    (fun p -> pts_to p v)
    True
    (fun p ->
      p.target_pcm == pcm /\
      freeable p
    )
= let ur = ualloc v in
  rewrite
    (upts_to ur full_perm v)
    (upts_to0 ur full_perm v);
  let _ = gen_elim () in
  let r: Ghost.erased (R.ref a) = vpattern_replace_erased (fun r -> R.pts_to r full_perm v) in
  R.share r;
  rewrite
    (upts_to0 ur (half_perm full_perm) v)
    (upts_to ur (half_perm full_perm) v);
  let i = new_invariant (exists_ (upts_to ur #a (half_perm full_perm))) in
  has_base_type_intro ur i a;
  rewrite
    (upts_to0 ur (half_perm full_perm) v)
    (upts_to ur (half_perm full_perm) v);
  has_base_type_idem ur i _ v ();
  let p = {
    base = ur;
    base_inv = i;
    base_has_type = ();
    base_pcm = pcm;
    target_pcm = pcm;
    base_to_target_conn = C.connection_id _;
  }
  in
  let v0 : get_base_type p.base p.base_inv = v in
  rewrite
    (upts_to ur (half_perm full_perm) v)
    (upts_to p.base (half_perm full_perm) v0);
  rewrite
    (pts_to0 p v)
    (pts_to p v);
  return p

let read
  (#a: Type0)
  (#opened: _)
  (#v: Ghost.erased a)
  (p: ptr a)
: STAtomic a opened
    (pts_to p v)
    (fun _ -> pts_to p v)
    (not (mem_inv opened p.base_inv))
    (fun v' -> Ghost.reveal v == v') // P.compatible p.target_pcm v v')
= rewrite
    (pts_to #a p v)
    (pts_to0 #a p v);
  let _ = gen_elim () in
  let v0 = uread p.base in
  let v' = p.base_to_target_conn.conn_large_to_small.morph v0 in
  rewrite
    (pts_to0 p v)
    (pts_to p v);
  return v'

(*
let write
  (#a: Type0)
  (#opened: _)
  (#v: Ghost.erased a)
  (v': Ghost.erased a)
  (p: ptr a)
  (f: P.frame_preserving_upd p.target_pcm v v')
: STAtomic unit opened
    (pts_to p v)
    (fun _ -> pts_to p v')
    (not (mem_inv opened p.base_inv))
    (fun _ -> True)
= rewrite
    (pts_to #a p v)
    (pts_to0 #a p v);
  let _ = gen_elim () in
  
  let v0 = uread p.base in
  let v' = p.base_to_target_conn.conn_large_to_small.morph v0 in
  rewrite
    (pts_to0 p v)
    (pts_to p v);
  return v'
