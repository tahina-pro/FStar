module Steel.ST.UntypedReference
open Steel.ST.GenElim

module R = Steel.ST.PCMReference.URef
module FP = FStar.PCM

let uref = core_ref

[@@erasable]
noeq
type base_type_inv
  (r: uref)
  (t0: Type)
  (p0: FP.pcm t0)
  (vp: vprop)
= {
    inv_reveal:
      (opened: _) ->
      STGhostT unit opened
        (vp)
        (fun _ -> R.upts_to r p0 p0.p.one);
    inv_hide:
      (opened: _) ->
      STGhostT unit opened
        (R.upts_to r p0 p0.p.one)
        (fun _ -> vp)
  }

let mk_base_type_inv
  (r: uref)
  (t0: Type)
  (p0: FP.pcm t0)
: Tot (base_type_inv r t0 p0 (R.upts_to r p0 p0.p.one))
= {
    inv_reveal = (fun _ ->
      noop ()
    );
    inv_hide = (fun _ ->
      noop ()
    );
  }

let inv_reveal
  (#r: uref)
  (#t0: Type)
  (#p0: FP.pcm t0)
  (#vp: vprop)
  (#opened: _)
  (i: base_type_inv r t0 p0 vp)
: STGhostT unit opened
    (vp)
    (fun gv -> R.upts_to r p0 p0.p.one)
= i.inv_reveal opened

let inv_hide
  (#r: uref)
  (#t0: Type)
  (#p0: FP.pcm t0)
  (#vp: vprop)
  (#opened: _)
  (i: base_type_inv r t0 p0 vp)
: STGhostT unit opened
    (R.upts_to r p0 p0.p.one)
    (fun _ -> vp)
= i.inv_hide opened

let base_type_inv_idem
  (#r: uref)
  (#t0: Type)
  (#p0: FP.pcm t0)
  (#vp: vprop)
  (#opened: _)
  (i: base_type_inv r t0 p0 vp)
  (#t: Type)
  (p: FP.pcm t)
  (v: t)
: STGhostT (squash (t == t0 /\ p === p0)) opened
    (vp `star` R.upts_to r p v)
    (fun _ -> vp `star` R.upts_to r p v)
= inv_reveal i;
  R.upts_to_unique r p v _ _;
  inv_hide i

let is_base_type
  (r: uref)
  (i: iname)
  (t0: Type)
: Tot prop
= exists (p0: FP.pcm t0) . exists (vp: vprop) . exists (f: base_type_inv r t0 p0 vp) . (i >--> vp)

let has_base_type
  (r: uref)
  (i: iname)
: Tot prop
= exists (t0: Type) . is_base_type r i t0

let has_base_type_intro_gen
  (r: uref)
  (i: iname)
  (t0: Type)
  (p0: FP.pcm t0)
  (vp: vprop)
  (f: base_type_inv r t0 p0 vp)
: Lemma
  (requires (i >--> vp))
  (ensures (has_base_type r i))
= ()

let has_base_type_intro
  (r: uref)
  (i: iname)
  (t0: Type)
  (p0: FP.pcm t0)
: Lemma
  (requires (i >--> R.upts_to r p0 p0.p.one)) 
  (ensures (has_base_type r i))
= let f: base_type_inv r t0 p0 _ = mk_base_type_inv r t0 p0 in
  has_base_type_intro_gen r i t0 p0 _ f

let get_base_type
  (r: uref)
  (i: iname)
: Pure Type
    (requires (has_base_type r i))
    (ensures (fun t0 -> is_base_type r i t0))
= FStar.IndefiniteDescription.indefinite_description_ghost Type (fun t0 -> is_base_type r i t0)

let get_base_pcm
  (r: uref)
  (i: iname)
  (sq: squash (has_base_type r i))
: Ghost (FP.pcm (get_base_type r i))
    (requires True)
    (ensures (fun p0 -> exists (vp: vprop) . exists (f: base_type_inv r (get_base_type r i) p0 vp) . (i >--> vp)
    ))
= FStar.IndefiniteDescription.indefinite_description_ghost (FP.pcm (get_base_type r i)) (fun p0 -> exists (vp: vprop) . exists (f: base_type_inv r (get_base_type r i) p0 vp) . (i >--> vp))

let get_inv
  (r: uref)
  (i: iname)
  (sq: squash (has_base_type r i))
: Pure vprop
    (requires True)
    (ensures (fun vp -> exists (f: base_type_inv r (get_base_type r i) (get_base_pcm r i ()) vp) . (i >--> vp)))
= let p0 = get_base_pcm r i sq in
  FStar.IndefiniteDescription.indefinite_description_ghost vprop (fun vp -> exists (f: base_type_inv r (get_base_type r i) p0 vp) . (i >--> vp))

let get_inv_acc
  (r: uref)
  (i: iname)
  (_: squash (has_base_type r i))
: Pure (base_type_inv r (get_base_type r i) (get_base_pcm r i ()) (get_inv r i ()))
    (requires True)
    (ensures (fun _ -> (i >--> get_inv r i ())))
= let vp = get_inv r i () in
  FStar.IndefiniteDescription.indefinite_description_ghost (base_type_inv r (get_base_type r i) (get_base_pcm r i ()) vp) (fun _ -> (i >--> vp))

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

let has_base_type_idem0
  (#opened: _)
  (r: uref)
  (i: iname)
  (#t: Type)
  (p: FP.pcm t)
  (v: t)
  (sq1: squash (not (mem_inv opened i)))
  (sq2: squash (has_base_type r i))
: STGhostT (squash (t == get_base_type r i /\ p === get_base_pcm r i sq2)) opened
    (R.upts_to r p v)
    (fun _ -> R.upts_to r p v)
= with_invariant_g_f
    #(squash (t == get_base_type r i /\ p === get_base_pcm r i sq2))
    #(R.upts_to r p v)
    #(fun _ -> R.upts_to r p v)
    #opened
    #(get_inv r i ())
    i
    (fun _ ->
      base_type_inv_idem #r #(get_base_type r i) #(get_base_pcm r i ()) #(get_inv r i ()) (get_inv_acc r i ()) p v
    )

let has_base_type_idem
  (#opened: _)
  (r: uref)
  (i: iname)
  (#t: Type)
  (p: FP.pcm t)
  (v: t)
  (sq: squash (
    not (mem_inv opened i) /\
    has_base_type r i)
  )
: STGhostT (squash (t == get_base_type r i /\ p == get_base_pcm r i ())) opened
    (R.upts_to r p v)
    (fun _ -> R.upts_to r p v)
= has_base_type_idem0 r i p v () ()

module P = Steel.C.PCM
module C = Steel.C.Connection

noeq
type ptr (a: Type u#0) : (Type u#0) = {
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
