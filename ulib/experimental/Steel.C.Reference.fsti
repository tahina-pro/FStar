module Steel.C.Reference
open Steel.C.Model.PCM
open Steel.C.Model.Ref
open Steel.Effect
open Steel.Effect.Atomic

val ptr (view_t: Type u#0) (#b: Type u#b) (q: pcm b)
: Type u#b

val null (view_t: Type u#0) (#b: Type u#b) (p: pcm b) : Tot (ptr view_t p)

val ptr_is_null (#view_t: Type u#0) (#b: Type u#b) (#q: pcm b) (p: ptr view_t q) : Ghost bool
  (requires True)
  (ensures (fun y -> y == true <==> p == null view_t q))

// [@@__reduce__]
inline_for_extraction
let ref (view_t: Type u#0) (#b: Type u#b) (q: pcm b)
: Tot (Type u#b)
=
  (x: ptr view_t q { ptr_is_null x == false })

val pts_to_view_hp
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ref view_t p) (view: sel_view p view_t' false)
: Tot (Steel.Memory.slprop u#1)

val pts_to_view_sel
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ref view_t p) (view: sel_view p view_t' false)
: Tot (selector view_t' (pts_to_view_hp r view))

[@@__steel_reduce__]
let pts_to_view
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ref view_t p) (view: sel_view p view_t' false)
: vprop
= VUnit ({
    hp = pts_to_view_hp r view;
    t = _;
    sel = pts_to_view_sel r view;
  })

val ref_read
  (#b: Type u#b)
  (#view_t: Type u#0)
  (#p: pcm b)
  (#vw: sel_view p view_t false)
  (r: ref view_t p)
: Steel view_t
  (r `pts_to_view` vw)
  (fun _ -> r `pts_to_view` vw)
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    res == h (r `pts_to_view` vw) /\
    res == h' (r `pts_to_view` vw)
  ))

val pts_to_view_or_null_hp
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ptr view_t p) (view: sel_view p view_t' false)
: Tot (Steel.Memory.slprop u#1)

val pts_to_view_or_null_sel
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ptr view_t p) (view: sel_view p view_t' false)
: Tot (selector (option view_t') (pts_to_view_or_null_hp r view))

[@@__steel_reduce__]
let pts_to_view_or_null
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ptr view_t p) (view: sel_view p view_t' false)
: vprop
= VUnit ({
    hp = pts_to_view_or_null_hp r view;
    t = _;
    sel = pts_to_view_or_null_sel r view;
  })

val intro_pts_to_view_or_null_null
  (#inames: _)
  (#b: Type) (#p: pcm b)
  (#c: Type0)
  (vw: sel_view p c false)
: SteelGhost unit inames
    emp
    (fun _ -> pts_to_view_or_null (null c p) vw)
    (requires (fun _ -> True))
    (ensures (fun _ _ h' -> h' (pts_to_view_or_null (null c p) vw) == None))

val elim_pts_to_view_or_null_null
  (#inames: _)
  (#b: Type) (#p: pcm b)
  (#c: Type0)
  (r: ptr c p)
  (vw: sel_view p c false)
: SteelGhost unit inames
    (pts_to_view_or_null r vw)
    (fun _ -> emp)
    (requires (fun _ -> ptr_is_null r == true))
    (ensures (fun _ _ _ -> True))

val intro_pts_to_view_or_null_not_null
  (#inames: _)
  (#b: Type) (#p: pcm b)
  (#c: Type0)
  (r: ref c p)
  (vw: sel_view p c false)
: SteelGhost unit inames
    (pts_to_view r vw)
    (fun _ -> pts_to_view_or_null r vw)
    (requires (fun _ -> True))
    (ensures (fun h _ h' -> h' (pts_to_view_or_null r vw) == Some (h (pts_to_view r vw))))

val elim_pts_to_view_or_null_not_null
  (#inames: _)
  (#b: Type) (#p: pcm b)
  (#c: Type0)
  (r: ref c p)
  (vw: sel_view p c false)
: SteelGhost unit inames
    (pts_to_view_or_null r vw)
    (fun _ -> pts_to_view r vw)
    (requires (fun _ -> True))
    (ensures (fun h _ h' -> h (pts_to_view_or_null r vw) == Some (h' (pts_to_view r vw))))

val freeable
  (#view_t: Type u#0) (#b: Type u#0) (#q: pcm b)
  (r: ref view_t q)
: Tot prop

(* Operations on views *)

let refine_view
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type u#b)
  (#can_view_unit:bool)
  (vw: sel_view p view can_view_unit)
  (pr: (view -> Tot prop))
: Tot (sel_view p (refine view pr) can_view_unit)
= {
  to_view_prop = (fun (c: carrier) -> vw.to_view_prop c /\ pr (vw.to_view c));
  to_view = (fun c -> vw.to_view c <: refine view pr);
  to_carrier = (fun (v: refine view pr) -> vw.to_carrier v <: carrier);
  to_carrier_not_one = vw.to_carrier_not_one;
  to_view_frame = (fun x frame -> vw.to_view_frame x frame);
}

inline_for_extraction
noextract
val intro_refine_view
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (pr: (view -> Tot prop))
  (r: ref view p)
: SteelAtomicBase (ref (refine view pr) p) false opened Unobservable
    (pts_to_view r vw)
    (fun r' -> pts_to_view r' (refine_view vw pr))
    (fun h -> pr (h (pts_to_view r vw)))
    (fun h r' h' ->
      let x = h (pts_to_view r vw) in
      pr x /\
      x == h' (pts_to_view r' (refine_view vw pr))
    )

inline_for_extraction
noextract
val elim_refine_view
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (pr: (view -> Tot prop))
  (r: ref (refine view pr) p)
: SteelAtomicBase (ref view p) false opened Unobservable
    (pts_to_view r (refine_view vw pr))
    (fun r' -> pts_to_view r' vw)
    (fun h -> True)
    (fun h r' h' ->
      let x = h' (pts_to_view r' vw) in
      pr x /\
      x == h (pts_to_view r (refine_view vw pr))
    )

let rewrite_view
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type u#b)
  (#can_view_unit:bool)
  (vw: sel_view p view can_view_unit)
  (#view' : Type u#c)
  (f: view -> view')
  (g: view' -> view)
  (prf: squash (f `Steel.C.Model.Connection.is_inverse_of` g))
: Tot (sel_view p view' can_view_unit)
= {
  to_view_prop = vw.to_view_prop;
  to_view = (fun c -> f (vw.to_view c));
  to_carrier = (fun v -> vw.to_carrier (g v));
  to_carrier_not_one = vw.to_carrier_not_one;
  to_view_frame = (fun x frame -> vw.to_view_frame (g x) frame);
}

inline_for_extraction
noextract
val intro_rewrite_view
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (#view' : Type)
  (f: view -> view')
  (g: view' -> view)
  (prf: squash (f `Steel.C.Model.Connection.is_inverse_of` g))
  (r: ref view p)
  (x' : Ghost.erased view')
: SteelAtomicBase (ref view' p) false opened Unobservable
    (pts_to_view r vw)
    (fun r' -> pts_to_view r' (rewrite_view vw f g prf))
    (fun h -> h (pts_to_view r vw) == g x')
    (fun h r' h' ->
      f (h (pts_to_view r vw)) == Ghost.reveal x' /\
      h' (pts_to_view r' (rewrite_view vw f g prf)) == Ghost.reveal x'
    )

inline_for_extraction
noextract
val elim_rewrite_view
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (#view' : Type)
  (f: view -> view')
  (g: view' -> view)
  (prf: squash (f `Steel.C.Model.Connection.is_inverse_of` g))
  (r: ref view' p)
: SteelAtomicBase (ref view p) false opened Unobservable
    (pts_to_view r (rewrite_view vw f g prf))
    (fun r' -> pts_to_view r' vw)
    (fun _ -> True)
    (fun h r' h' ->
      let x = h (pts_to_view r (rewrite_view vw f g prf)) in
      let x' = h' (pts_to_view r' vw) in
      Ghost.reveal x' == g (Ghost.reveal x) /\
      f (Ghost.reveal x') == Ghost.reveal x
    )
