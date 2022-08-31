module Steel.ST.UntypedReference
open Steel.ST.GenElim

module R = Steel.ST.PCMReference
module GHR = Steel.ST.GhostHigherReference
module FP = FStar.PCM

[@@erasable]
noeq
type base_type_inv
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
  (t0: Type)
  (p0: FP.pcm t0)
  (vp: vprop)
= {
    inv_reveal:
      (opened: _) ->
      STGhostT unit opened
        (vp)
        (fun _ -> GHR.pts_to r (half_perm full_perm) (| t0, p0 |));
    inv_hide:
      (opened: _) ->
      STGhostT unit opened
        (GHR.pts_to r (half_perm full_perm) (| t0, p0 |))
        (fun _ -> vp)
  }

let mk_base_type_inv
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
  (t0: Type)
  (p0: FP.pcm t0)
: Tot (base_type_inv r t0 p0 (GHR.pts_to r (half_perm full_perm) (| t0, p0 |)))
= {
    inv_reveal = (fun _ ->
      noop ()
    );
    inv_hide = (fun _ ->
      noop ()
    );
  }

let inv_reveal
  (#r: GHR.ref (dtuple2 Type0 FP.pcm))
  (#t0: Type)
  (#p0: FP.pcm t0)
  (#vp: vprop)
  (#opened: _)
  (i: base_type_inv r t0 p0 vp)
: STGhostT unit opened
    (vp)
    (fun gv -> GHR.pts_to r (half_perm full_perm) (| t0, p0 |))
= i.inv_reveal opened

let inv_hide
  (#r: GHR.ref (dtuple2 Type0 FP.pcm))
  (#t0: Type)
  (#p0: FP.pcm t0)
  (#vp: vprop)
  (#opened: _)
  (i: base_type_inv r t0 p0 vp)
: STGhostT unit opened
    (GHR.pts_to r (half_perm full_perm) (| t0, p0 |))
    (fun _ -> vp)
= i.inv_hide opened

let base_type_inv_idem
  (#r: GHR.ref (dtuple2 Type0 FP.pcm))
  (#t0: Type)
  (#p0: FP.pcm t0)
  (#vp: vprop)
  (#opened: _)
  (i: base_type_inv r t0 p0 vp)
  (p: perm)
  (v: dtuple2 Type0 FP.pcm)
: STGhostT (squash (v == (| t0, p0 |))) opened
    (vp `star` GHR.pts_to r p v)
    (fun _ -> vp `star` GHR.pts_to r p v)
= let _ = inv_reveal i in
  GHR.pts_to_injective_eq #_ #_ #(half_perm full_perm) #p r;
  inv_hide i

let is_base_type
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
  (i: iname)
  (t0: Type)
: Tot prop
= exists (p0: FP.pcm t0) . exists (vp: vprop) . exists (f: base_type_inv r t0 p0 vp) . (i >--> vp)

let has_base_type
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
  (i: iname)
: Tot prop
= exists (t0: Type) . is_base_type r i t0

let has_base_type_intro_gen
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
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
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
  (i: iname)
  (t0: Type)
  (p0: FP.pcm t0)
: Lemma
  (requires (i >--> GHR.pts_to r (half_perm full_perm) (| t0, p0 |)))
  (ensures (has_base_type r i))
= let f: base_type_inv r t0 p0 _ = mk_base_type_inv r t0 p0 in
  has_base_type_intro_gen r i t0 p0 _ f

let get_base_type
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
  (i: iname)
: Pure Type
    (requires (has_base_type r i))
    (ensures (fun t0 -> is_base_type r i t0))
= FStar.IndefiniteDescription.indefinite_description_ghost Type (fun t0 -> is_base_type r i t0)

let get_base_pcm
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
  (i: iname)
  (sq: squash (has_base_type r i))
: Ghost (FP.pcm (get_base_type r i))
    (requires True)
    (ensures (fun p0 ->
      let t0 = get_base_type r i in
      exists (vp: vprop) . exists (f: base_type_inv r t0 p0 vp) . (i >--> vp)
    ))
= let t0 = get_base_type r i in
  FStar.IndefiniteDescription.indefinite_description_ghost (FP.pcm (get_base_type r i)) (fun p0 -> exists (vp: vprop) . exists (f: base_type_inv r t0 p0 vp) . (i >--> vp))

let get_inv
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
  (i: iname)
  (sq: squash (has_base_type r i))
: Pure vprop
    (requires True)
    (ensures (fun vp -> exists (f: base_type_inv r (get_base_type r i) (get_base_pcm r i ()) vp) . (i >--> vp)))
= let t0 = get_base_type r i in
  let p0 = get_base_pcm r i () in
  FStar.IndefiniteDescription.indefinite_description_ghost vprop (fun vp -> exists (f: base_type_inv r t0 p0 vp) . (i >--> vp))

let get_inv_acc
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
  (i: iname)
  (sq: squash (has_base_type r i))
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

let has_base_type_idem
  (#opened: _)
  (r: GHR.ref (dtuple2 Type0 FP.pcm))
  (i: iname)
  (p: perm)
  (v: dtuple2 Type0 FP.pcm)
  (sq: squash (
    not (mem_inv opened i) /\
    has_base_type r i
  ))
: STGhostT (squash (v == (| get_base_type r i, get_base_pcm r i () |))) opened
    (GHR.pts_to r p v)
    (fun _ -> GHR.pts_to r p v)
= with_invariant_g_f
    #(squash (v == (| get_base_type r i, get_base_pcm r i () |)))
    #(GHR.pts_to r p v) #(fun _ -> GHR.pts_to r p v)  #_ #(get_inv r i ()) i (fun _ ->
    base_type_inv_idem #r #(get_base_type r i) #(get_base_pcm r i ()) #(get_inv r i ()) (get_inv_acc r i ()) p v
  )

module P = Steel.C.PCM
module C = Steel.C.Connection
module U = FStar.Universe
module FPU = FStar.Universe.PCM

noeq
type ptr (a: Type0) : (Type0) = {
  base_type: GHR.ref (dtuple2 Type0 FP.pcm);
  base_inv: Ghost.erased iname;
  base_has_type: squash (has_base_type base_type base_inv);
  base: ref (U.raise_t (get_base_type base_type base_inv)) (FPU.raise (get_base_pcm base_type base_inv ()));
  base_pcm: P.pcm (get_base_type base_type base_inv);
  base_pcm_eq: squash (get_base_pcm base_type base_inv () == P.fstar_pcm_of_pcm base_pcm);
  target_pcm: P.pcm a;
  base_to_target_conn: C.connection base_pcm target_pcm;
}

let freeable (#a: Type) (p: ptr a) : Tot prop =
  get_base_type p.base_type p.base_inv == a /\
  p.target_pcm == p.base_pcm /\
  p.base_to_target_conn == C.connection_id _

[@@__reduce__]
let pts_to0
  (#a: Type)
  (p: ptr a)
  (v: a)
: Tot vprop
= exists_ (GHR.pts_to p.base_type (half_perm full_perm)) `star`
  R.pts_to p.base (U.raise_val (p.base_to_target_conn.conn_small_to_large.morph v))

let pts_to
  (#a: Type)
  (p: ptr a)
  (v: a)
: Tot vprop
= pts_to0 #a p v

#push-options "--z3rlimit 16"

let alloc
  (#a: Type0)
  (pcm: P.pcm a)
  (v: a)
: ST (ptr a)
    emp
    (fun p -> pts_to p v)
    (P.p_refine pcm v)
    (fun p ->
      p.target_pcm == pcm /\
      freeable p
    )
= let r : ref (U.raise_t a) (FPU.raise (P.fstar_pcm_of_pcm pcm)) = R.alloc (U.raise_val v) in
  let g: GHR.ref (dtuple2 Type0 FP.pcm) = GHR.alloc (| a, P.fstar_pcm_of_pcm pcm |) in
  GHR.share g;
  let i = new_invariant (GHR.pts_to g (half_perm full_perm) (| a, P.fstar_pcm_of_pcm pcm |)) in
  has_base_type_intro g i a (P.fstar_pcm_of_pcm pcm);
  has_base_type_idem g i _ _ ();
  let p = {
    base_type = g;
    base_inv = i;
    base_has_type = ();
    base = r;
    base_pcm = pcm;
    base_pcm_eq = ();
    target_pcm = pcm;
    base_to_target_conn = C.connection_id _;
  }
  in
  rewrite
    (R.pts_to r _)
    (R.pts_to p.base (U.raise_val (p.base_to_target_conn.conn_small_to_large.morph v)));
  vpattern_rewrite (fun g -> GHR.pts_to g _ _) p.base_type;
  rewrite
    (pts_to0 p v)
    (pts_to p v);
  return p

#pop-options

(*
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
