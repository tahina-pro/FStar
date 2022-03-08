(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.V.Effect

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
open Steel.Semantics.Instantiate
module FExt = FStar.FunctionalExtensionality

#set-options "--ide_id_info_off"

#set-options "--warn_error -330"  //turn off the experimental feature warning

[@@ __steel_reduce__]
let req_to_act_req (#pre:pre_t) (req:req_t pre) : Sem.l_pre #state (hp_of pre) =
  fun m0 -> interp (hp_of pre) m0 /\ (value_is_valid_complete pre m0; req (sel_of pre m0))

unfold
let to_post (#a:Type) (post:post_t a) = fun x -> (hp_of (post x))

// [@@ __steel_reduce__]

let ens_to_act_ens0 (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
  (m0: mem)
  (x: a)
  (m1: mem)
: Tot prop
=
    interp (hp_of pre) m0 /\ interp (hp_of (post x)) m1 /\ (value_is_valid_complete pre m0; value_is_valid_complete (post x) m1; ens (sel_of pre m0) x (sel_of (post x) m1))

let ens_to_act_ens (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
: Sem.l_post #state #a (hp_of pre) (to_post post)
= ens_to_act_ens0 ens

unfold
let ens_to_act_ens1 (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
  (m0: mem)
  (x: a)
  (m1: mem)
: Tot prop
=
    interp (hp_of pre) m0 /\
    interp (hp_of (post x)) m1 /\ (
      (value_is_valid pre (sel_of pre m0) /\
      value_is_valid (post x) (sel_of (post x) m1)) ==> (
        ens (sel_of pre m0) x (sel_of (post x) m1)
    ))

let ens_to_act_ens1_correct
  (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
  (m0: mem)
  (x: a)
  (m1: mem)
: Lemma
  (requires (ens_to_act_ens1 ens m0 x m1))
  (ensures (ens_to_act_ens ens m0 x m1))
= value_is_valid_complete pre m0;
  value_is_valid_complete (post x) m1

val can_be_split_3_interp (p1 p2 q r:slprop u#1) (m:mem)
: Lemma
  (requires p1 `slimp` p2 /\  interp (p1 `Mem.star` q `Mem.star` r) m)
  (ensures interp (p2 `Mem.star` q `Mem.star` r) m)

let can_be_split_3_interp p1 p2 q r m =
  Mem.star_associative p1 q r;
  Mem.star_associative p2 q r;
  slimp_star p1 p2 (q `Mem.star` r) (q `Mem.star` r)

let repr (a:Type) (_:bool) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a (hp_of pre) (to_post post)
    ((req_to_act_req req))
    ((ens_to_act_ens ens))

let nmst_get (#st:Sem.st) ()
  : Sem.Mst (Sem.full_mem st)
           (fun _ -> True)
           (fun s0 s s1 -> s0 == s /\ s == s1)
  = NMST.get ()

let return_ a x #p = fun _ ->
      x

#push-options "--fuel 0 --ifuel 0"

val req_frame (frame:vprop) (snap:valid_value frame) : mprop (hp_of frame)

let req_frame' (frame:vprop) (snap:valid_value frame) (m:mem) : prop =
  interp (hp_of frame) m /\ sel_of frame m == snap

let req_frame frame snap =
  req_frame' frame snap

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1 --query_stats" // ifuel 1 necessary because of the Sem record

val frame00 (#a:Type)
          (#framed:bool)
          (#pre:pre_t)
          (#post:post_t a)
          (#req:req_t pre)
          (#ens:ens_t pre a post)
          ($f:repr a framed pre post req ens)
          (frame:vprop)
  : repr a
    true
    (pre `star` frame)
    (fun x -> post x `star` frame)
    (fun h -> req (vselect h pre))
    (fun h0 r h1 -> req (vselect h0 pre) /\ ens (vselect h0 pre) r (vselect h1 (post r)) /\
     vselect h0 frame == vselect h1 frame)

#restart-solver
let frame00 #a #framed #pre #post #req #ens f frame =
  fun frame' ->
      let m00 = nmst_get () in
      let m0 = core_mem m00 in
      vselect_correct (pre `star` frame) pre m0;
      vselect_correct (pre `star` frame) frame m0;
      let snap = Ghost.hide (sel_of frame m0) in

      let x = Sem.run #state #_ #_ #_ #_ #_ frame' (Sem.Frame (Sem.Act f) (hp_of frame) (req_frame frame snap)) in

      let m01 = nmst_get () in
      let m1 = core_mem m01 in
      vselect_correct (post x `star` frame) (post x) m1;
      vselect_correct (post x `star` frame) frame m1;

      x

#pop-options

let bind_ens_intro (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (#pr:a -> prop)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:vprop) (frame_g:a -> vprop)
  (post:post_t b)
  (p1:squash (can_be_split_forall_dep pr (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (m0: valid_value (pre_f `star` frame_f))
  (y: b)
  (m2: valid_value (post y))
  (x: a)
  (h1: valid_value (post_f x `star` frame_f))
: Lemma
  (requires (
    req_f (vselect m0 pre_f) /\
    pr x /\
    vselect m0 frame_f == vselect h1 frame_f /\
    vselect h1 (frame_g x) == vselect m2 (frame_g x) /\
    ens_f (vselect m0 pre_f) x (vselect h1 (post_f x)) /\
    ens_g x (vselect h1 (pre_g x)) y (vselect m2 (post_g x y))
  ))
  (ensures (
    bind_ens req_f ens_f ens_g frame_f frame_g post p1 p2 m0 y m2
  ))
= ()

#push-options "--print_implicits --ifuel 1 --fuel 1 --query_stats --z3rlimit_factor 24"

#restart-solver
let bind a b #framed_f #framed_g #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #frame_g #post #_ #_ #pr #p1 #p2 f g =
  fun frame ->
    let m0 = nmst_get () in
    value_is_valid_complete (pre_f `star` frame_f) (core_mem m0);
    let v0 = Ghost.hide (sel_of (pre_f `star` frame_f) (core_mem m0)) in
    let x = frame00 f frame_f frame in
    let m1 = nmst_get () in
    value_is_valid_complete (post_f x `star` frame_f) (core_mem m1);
    let v1 = Ghost.hide (sel_of (post_f x `star` frame_f) (core_mem m1)) in
    assert (interp (hp_of (post_f x `star` frame_f)) m1);
    assert (ens_f (vselect v0 pre_f) x (vselect v1 (post_f x)));
    assert (vselect v0 frame_f == vselect v1 frame_f);
    assert (pr x);
    assert ((post_f x `star` frame_f) `can_be_split` (pre_g x `star` frame_g x));
    assert (req_g x (vselect v1 (pre_g x)));
    vselect_correct (post_f x `star` frame_f) (pre_g x `star` frame_g x) (core_mem m1);
    let v1' = Ghost.hide (sel_of (pre_g x `star` frame_g x) (core_mem m1)) in
    assert (Ghost.reveal v1' == vselect v1 (pre_g x `star` frame_g x));
    assert (req_g x (vselect v1' (pre_g x)));
    can_be_split_slimp
      (post_f x `star` frame_f)
      (pre_g x `star` frame_g x);
    can_be_split_3_interp
      (hp_of (post_f x `star` frame_f))
      (hp_of (pre_g x `star` frame_g x))
      frame (locks_invariant Set.empty m1) m1;
    let y = frame00 (g x) (frame_g x) frame in
    let m2 = nmst_get () in
    let prf () : Lemma (
      ens_to_act_ens1 (bind_ens req_f ens_f ens_g frame_f frame_g post p1 p2) (core_mem m0) y (core_mem m2)
    ) =
      value_is_valid_complete (post_g x y `star` frame_g x) (core_mem m2);
      let v2' = Ghost.hide (sel_of (post_g x y `star` frame_g x) (core_mem m2)) in
      assert (ens_g x (vselect v1' (pre_g x)) y (vselect v2' (post_g x y))); 
      assert (vselect v2' (frame_g x) == vselect v1' (frame_g x));
      assert (vselect v1' (frame_g x) == vselect v1 (frame_g x));
      vselect_correct (post_g x y `star` frame_g x) (post y) (core_mem m2);
      vselect_correct (post y) (post_g x y `star` frame_g x) (core_mem m2);
      let v2 = Ghost.hide (sel_of (post y) (core_mem m2)) in
      assert (vselect v2 (frame_g x) == vselect v2' (frame_g x));
      assert (vselect v2 (post_g x y) == vselect v2' (post_g x y));
      assert (ens_g x (vselect v1 (pre_g x)) y (vselect v2 (post_g x y)));
      bind_ens_intro req_f ens_f ens_g frame_f frame_g post p1 p2 v0 y v2 x v1
    in
    prf ();
    ens_to_act_ens1_correct (bind_ens req_f ens_f ens_g frame_f frame_g post p1 p2) (core_mem m0) y (core_mem m2);
    can_be_split_slimp
      (post_g x y `star` frame_g x)
      (post y);
    can_be_split_3_interp
      (hp_of (post_g x y `star` frame_g x))
      (hp_of (post y))
      frame (locks_invariant Set.empty m2) m2;
    y

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
#restart-solver

let subcomp a #framed_f #framed_g #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #fr #_ #p1 #p2 f =
  fun frame ->
    let m0 = nmst_get () in
    value_is_valid_complete pre_g (core_mem m0);
    let v0 = Ghost.hide (sel_of pre_g (core_mem m0)) in
    vselect_correct pre_g (pre_f `star` fr) (core_mem m0);
    can_be_split_slimp pre_g (pre_f `star` fr);
    can_be_split_3_interp (hp_of pre_g) (hp_of (pre_f `star` fr)) frame (locks_invariant Set.empty m0) m0;
    let x = frame00 f fr frame in
    let m1 = nmst_get () in
    can_be_split_slimp (post_f x `star` fr) (post_g x);
    can_be_split_3_interp (hp_of (post_f x `star` fr)) (hp_of (post_g x)) frame (locks_invariant Set.empty m1) m1;
    value_is_valid_complete (post_f x `star` fr) (core_mem m1);
    let v1 = Ghost.hide (sel_of (post_f x `star` fr) (core_mem m1)) in
    vselect_correct (post_f x `star` fr) (post_g x) (core_mem m1);
    vselect_correct (post_g x) (post_f x `star` fr) (core_mem m1);
    x

#pop-options

#push-options "--z3rlimit_factor 8 --fuel 1 --ifuel 1"

let bind_pure_steel_ a b #wp #pre #post #req #ens f g
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun frame ->
      let x = f () in
      g x frame

#pop-options

(* We need a bind with DIV to implement par, using reification *)

unfold
let bind_div_steel_req (#a:Type) (wp:pure_wp a)
  (#pre_g:pre_t) (req_g:a -> req_t pre_g)
: req_t pre_g
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun h -> wp (fun _ -> True) /\ (forall x. (req_g x) h)

unfold
let bind_div_steel_ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre_g:pre_t) (#post_g:post_t b) (ens_g:a -> ens_t pre_g b post_g)
: ens_t pre_g b post_g
= fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. ens_g x h0 r h1)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let bind_div_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (framed:eqtype_as_type bool)
  (pre_g:pre_t) (post_g:post_t b) (req_g:a -> req_t pre_g) (ens_g:a -> ens_t pre_g b post_g)
  (f:eqtype_as_type unit -> DIV a wp) (g:(x:a -> repr b framed pre_g post_g (req_g x) (ens_g x)))
: repr b framed pre_g post_g
    (bind_div_steel_req wp req_g)
    (bind_div_steel_ens wp ens_g)
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun frame ->
  let x = f () in
  g x frame
#pop-options

polymonadic_bind (DIV, SteelBase) |> SteelBase = bind_div_steel
#pop-options

let par0 (#aL:Type u#a) (#preL:vprop) (#postL:aL -> vprop)
         (f:repr aL false preL postL (fun _ -> True) (fun _ _ _ -> True))
         (#aR:Type u#a) (#preR:vprop) (#postR:aR -> vprop)
         (g:repr aR false preR postR (fun _ -> True) (fun _ _ _ -> True))
  : SteelT (aL & aR)
    (preL `star` preR)
    (fun y -> postL (fst y) `star` postR (snd y))
  = Steel?.reflect (fun frame -> Sem.run #state #_ #_ #_ #_ #_ frame (Sem.Par (Sem.Act f) (Sem.Act g)))

(*
 * AR: Steel is not marked reifiable since we intend to run Steel programs natively
 *     However to implement the par combinator we need to reify a Steel thunk to its repr
 *     We could implement it better by having support for reification only in the .fst file
 *     But for now assuming a (Dv) function
 *)
assume val reify_steel_comp
  (#a:Type) (#framed:bool) (#pre:vprop) (#post:a -> vprop) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> SteelBase a framed pre post req ens)
  : Dv (repr a framed pre post req ens)

let par f g =
  par0 (reify_steel_comp f) (reify_steel_comp g)

let action_as_repr (#a:Type) (#p:slprop) (#q:a -> slprop) (f:action_except a Set.empty p q)
  : repr a false (to_vprop p) (fun x -> to_vprop (q x)) (fun _ -> True) (fun _ _ _ -> True)
  = Steel.Semantics.Instantiate.state_correspondence Set.empty; f

let as_action #a #p #q f = Steel?.reflect (action_as_repr f)
