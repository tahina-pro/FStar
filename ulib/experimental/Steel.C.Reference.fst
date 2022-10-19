module Steel.C.Reference
open Steel.C.Model.PCM
open Steel.C.Model.Ref
open Steel.Effect
open Steel.Effect.Atomic

#push-options "--print_universes"

// [@@__reduce__]
let ptr (view_t: Type u#0) (#b: Type u#b) (q: pcm b)
: Type u#b
= ptr q

let null _ p = null p

let ptr_is_null p = ptr_is_null p

unfold
let ref_of_ref
  (#view_t: Type u#0) (#b: Type u#b) (#q: pcm b)
  (r: ref view_t q)
: Tot (Steel.C.Model.Ref.ref q)
= r

[@@__steel_reduce__] // ; __reduce__]
let pts_to_view0
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ref view_t p) (view: sel_view p view_t' false)
: vprop
= r `pts_to_view` view

let pts_to_view_hp r view = hp_of (pts_to_view0 r view)
let pts_to_view_sel r view = sel_of (pts_to_view0 r view)

let intro_pts_to_view
  (#opened: _)
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ref view_t p) (view: Steel.C.Model.Ref.sel_view p view_t' false)
: SteelGhost unit opened
    (pts_to_view0 r view)
    (fun _ -> pts_to_view r view)
    (fun _ -> True)
    (fun h _ h' -> h' (pts_to_view r view) == h (pts_to_view0 r view))
= change_slprop_rel
    (pts_to_view0 r view)
    (pts_to_view r view)
    (fun x y -> x == y)
    (fun _ -> ())

let elim_pts_to_view
  (#opened: _)
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ref view_t p) (view: Steel.C.Model.Ref.sel_view p view_t' false)
: SteelGhost unit opened
    (pts_to_view r view)
    (fun _ -> pts_to_view0 r view)
    (fun _ -> True)
    (fun h _ h' -> h' (pts_to_view0 r view) == h (pts_to_view r view))
= change_slprop_rel
    (pts_to_view r view)
    (pts_to_view0 r view)
    (fun x y -> x == y)
    (fun _ -> ())

let ref_read
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
= elim_pts_to_view r vw;
  let res = ref_read_sel r vw in
  intro_pts_to_view r vw;
  return res

[@@__steel_reduce__] // ; __reduce__]
let pts_to_view_or_null0
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ptr view_t p) (view: sel_view p view_t' false)
: vprop
= r `pts_to_view_or_null` view

let pts_to_view_or_null_hp r view = hp_of (pts_to_view_or_null0 r view)
let pts_to_view_or_null_sel r view = sel_of (pts_to_view_or_null0 r view)

let intro_pts_to_view_or_null
  (#opened: _)
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ptr view_t p) (view: Steel.C.Model.Ref.sel_view p view_t' false)
: SteelGhost unit opened
    (pts_to_view_or_null0 r view)
    (fun _ -> pts_to_view_or_null r view)
    (fun _ -> True)
    (fun h _ h' -> h' (pts_to_view_or_null r view) == h (pts_to_view_or_null0 r view))
= change_slprop_rel
    (pts_to_view_or_null0 r view)
    (pts_to_view_or_null r view)
    (fun x y -> x == y)
    (fun _ -> ())

let elim_pts_to_view_or_null
  (#opened: _)
  (#view_t: Type u#0)
  (#view_t': Type u#0)
  (#b: Type u#b) (#p: pcm b)
  (r: ptr view_t p) (view: Steel.C.Model.Ref.sel_view p view_t' false)
: SteelGhost unit opened
    (pts_to_view_or_null r view)
    (fun _ -> pts_to_view_or_null0 r view)
    (fun _ -> True)
    (fun h _ h' -> h' (pts_to_view_or_null0 r view) == h (pts_to_view_or_null r view))
= change_slprop_rel
    (pts_to_view_or_null r view)
    (pts_to_view_or_null0 r view)
    (fun x y -> x == y)
    (fun _ -> ())

let is_null
  (#b: Type u#b) (#c: Type0) (#opened: _) (#p: pcm b)
  (r: ptr c p)
  (vw: sel_view p c false)
: SteelAtomicBase bool false opened Unobservable
    (pts_to_view_or_null r vw)
    (fun _ -> pts_to_view_or_null r vw)
    (requires (fun _ -> True))
    (ensures (fun h res h' ->
      let s = h (pts_to_view_or_null r vw) in
      h' (pts_to_view_or_null r vw) == s /\
      res == ptr_is_null r /\
      res == (None? s)
    ))
= elim_pts_to_view_or_null r vw;
  let res = is_null r vw in
  intro_pts_to_view_or_null r vw;
  return res

let intro_pts_to_view_or_null_null
  (#inames: _)
  (#b: Type) (#p: pcm b)
  (#c: Type0)
  (vw: sel_view p c false)
: SteelGhost unit inames
    emp
    (fun _ -> pts_to_view_or_null (null c p) vw)
    (requires (fun _ -> True))
    (ensures (fun _ _ h' -> h' (pts_to_view_or_null (null c p) vw) == None))
= intro_pts_to_view_or_null_null vw;
  intro_pts_to_view_or_null (null c p) vw

let elim_pts_to_view_or_null_null
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
= elim_pts_to_view_or_null r vw;
  change_equal_slprop
    (pts_to_view_or_null0 r vw)
    (pts_to_view_or_null0 (null c p) vw);
  elim_pts_to_view_or_null_null vw

let intro_pts_to_view_or_null_not_null
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
= elim_pts_to_view r vw;
  intro_pts_to_view_or_null_not_null r vw;
  intro_pts_to_view_or_null r vw

let elim_pts_to_view_or_null_not_null
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
= elim_pts_to_view_or_null r vw;
  elim_pts_to_view_or_null_not_null r vw;
  intro_pts_to_view r vw

let freeable
  (#view_t: Type u#0) (#b: Type u#0) (#q: pcm b)
  (r: ref view_t q)
: Tot prop
= freeable (r <: Steel.C.Model.Ref.ref q)

(* Operations on views *)

let intro_refine_view'
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (pr: (view -> Tot prop))
  (r: ref view p)
: SteelGhost unit opened
    (pts_to_view r vw)
    (fun _ -> pts_to_view r (refine_view vw pr))
    (fun h -> pr (h (pts_to_view r vw)))
    (fun h _ h' ->
      let x = h (pts_to_view r vw) in
      pr x /\
      x == h' (pts_to_view r (refine_view vw pr))
    )
= let g = gget (pts_to_view r vw) in
  elim_pts_to_view r vw;
  let v = pts_to_view_elim r vw in
  pts_to_view_intro r v (refine_view vw pr) (Ghost.hide (Ghost.reveal g));
  intro_pts_to_view _ _

inline_for_extraction
noextract
let intro_refine_view
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
      r == r' /\
      x == h' (pts_to_view r' (refine_view vw pr))
    )
= intro_refine_view' vw pr r;
  let r' : ref (refine view pr) p = r in
  change_equal_slprop
    (pts_to_view r (refine_view vw pr))
    (pts_to_view r' (refine_view vw pr));
  return r'

let elim_refine_view'
  (#opened: _)
  (#carrier: Type u#a)
  (#p: pcm carrier)
  (#view: Type)
  (vw: sel_view p view false)
  (pr: (view -> Tot prop))
  (r: ref (refine view pr) p)
: SteelGhost unit opened
    (pts_to_view r (refine_view vw pr))
    (fun _ -> pts_to_view r vw)
    (fun h -> True)
    (fun h _ h' ->
      let x = h' (pts_to_view r vw) in
      pr x /\
      x == h (pts_to_view r (refine_view vw pr))
    )
= let g = gget (pts_to_view r (refine_view vw pr)) in
  elim_pts_to_view _ _;
  let v = pts_to_view_elim r (refine_view vw pr) in
  pts_to_view_intro r v vw (Ghost.hide (Ghost.reveal g));
  intro_pts_to_view _ _

inline_for_extraction
noextract
let elim_refine_view
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
      r' == r /\
      x == h (pts_to_view r (refine_view vw pr))
    )
= elim_refine_view' vw pr r;
  let r' : ref view p = r in
  change_equal_slprop
    (pts_to_view r vw)
    (pts_to_view r' vw);
  return r'

let intro_rewrite_view'
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
: SteelGhost unit opened
    (pts_to_view r vw)
    (fun _ -> pts_to_view r (rewrite_view vw f g prf))
    (fun h -> h (pts_to_view r vw) == g x')
    (fun h _ h' ->
      f (h (pts_to_view r vw)) == Ghost.reveal x' /\
      h' (pts_to_view r (rewrite_view vw f g prf)) == Ghost.reveal x'
    )
= elim_pts_to_view _ _;
  let v = pts_to_view_elim r vw in
  pts_to_view_intro r v (rewrite_view vw f g prf) x';
  intro_pts_to_view _ _

inline_for_extraction
noextract
let intro_rewrite_view
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
= intro_rewrite_view' vw f g prf r x';
  let r' : ref view' p = r in
  change_equal_slprop
    (pts_to_view r (rewrite_view vw f g prf))
    (pts_to_view r' (rewrite_view vw f g prf));
  return r'

let elim_rewrite_view'
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
: SteelGhost unit opened
    (pts_to_view r (rewrite_view vw f g prf))
    (fun _ -> pts_to_view r vw)
    (fun _ -> True)
    (fun h _ h' ->
      let x = h (pts_to_view r (rewrite_view vw f g prf)) in
      let x' = h' (pts_to_view r vw) in
      Ghost.reveal x' == g (Ghost.reveal x) /\
      f (Ghost.reveal x') == Ghost.reveal x
    )
= let gv = gget (pts_to_view r (rewrite_view vw f g prf)) in
  elim_pts_to_view _ _;
  let v = pts_to_view_elim r (rewrite_view vw f g prf) in
  pts_to_view_intro r v vw (g gv);
  intro_pts_to_view _ _

inline_for_extraction
noextract
let elim_rewrite_view
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
= elim_rewrite_view' vw f g prf r;
  let r' : ref view p = r in
  change_equal_slprop
    (pts_to_view r vw)
    (pts_to_view r' vw);
  return r'
