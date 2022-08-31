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
module Steel.ST.GhostHigherReference
open FStar.Ghost
open Steel.ST.Util
open Steel.ST.Coercions
module R = Steel.ST.GhostHigherPCMReference
module P = Steel.PCMFrac

[@@ erasable]
let ref (a:Type u#1)
  : Type u#0
  = R.ref _ (P.pcm_frac #a)

[@@__reduce__]
let pts_to0 (#a:_)
           (r:ref a)
           (p:perm)
           (v:a)
  : vprop
  = R.pts_to r (Some (v, p)) `star` pure (lesser_equal_perm p full_perm == true)

let pts_to (#a:_)
           (r:ref a)
           (p:perm)
           ([@@@smt_fallback] v:a)
  : vprop
  = pts_to0 r p v

let pts_to_injective_eq (#a:_)
                        (#u:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  : STGhost unit u
      (pts_to r p v0 `star` pts_to r q v1)
      (fun _ -> pts_to r p v0 `star` pts_to r q v0)
      (requires True)
      (ensures fun _ -> v0 == v1)
  = rewrite
      (pts_to r p v0)
      (pts_to0 r p v0);
    rewrite
      (pts_to r q v1)
      (pts_to0 r q v1);
    R.gather r (Some (v0, p)) (Some (v1, q));
    R.share r _ (Some (v0, p)) (Some (v0, q));
    rewrite
      (pts_to0 r p v0)
      (pts_to r p v0);
    rewrite
      (pts_to0 r q v0)
      (pts_to r q v0)

let alloc (#a:Type)
          (#u:_)
          (x:erased a)
  : STGhostT (ref a) u
      emp
      (fun r -> pts_to r full_perm x)
  = R.alloc (Some (Ghost.reveal x, full_perm))

let read (#a:Type)
         (#u:_)
         (#p:perm)
         (#v:erased a)
         (r:ref a)
  : STGhost (erased a) u
      (pts_to r p v)
      (fun x -> pts_to r p x)
      (requires True)
      (ensures fun x -> x == v)
  = rewrite (pts_to r p v) (pts_to0 r p v);
    let Some (vx, _) = R.read r in
    let x = Ghost.hide vx in
    rewrite (pts_to0 r p v) (pts_to r p x);
    x

let write (#a:Type)
          (#u:_)
          (#v:erased a)
          (r:ref a)
          (x:erased a)
  : STGhostT unit u
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm x)
  = rewrite (pts_to r full_perm (Ghost.reveal v)) (pts_to0 r full_perm (Ghost.reveal v));
    R.write r (Some (Ghost.reveal v, full_perm)) (Some ((Ghost.reveal x), full_perm));
    rewrite (pts_to0 r full_perm (Ghost.reveal x)) (pts_to r full_perm (Ghost.reveal x))

let share (#a:Type)
          (#u:_)
          (#p:perm)
          (#x:erased a)
          (r:ref a)
  : STGhostT unit u
      (pts_to r p x)
      (fun _ -> pts_to r (half_perm p) x `star`
             pts_to r (half_perm p) x)
  = rewrite (pts_to r p x) (pts_to0 r p x);
    elim_pure _;
    R.share r _ (Some (Ghost.reveal x, half_perm p)) (Some (Ghost.reveal x, half_perm p));
    rewrite (pts_to0 r (half_perm p) x) (pts_to r (half_perm p) x);
    rewrite (pts_to0 r (half_perm p) x) (pts_to r (half_perm p) x)

let gather (#a:Type)
           (#u:_)
           (#p0 #p1:perm)
           (#x0 #x1:erased a)
           (r:ref a)
  : STGhost unit u
      (pts_to r p0 x0 `star` pts_to r p1 x1)
      (fun _ -> pts_to r (sum_perm p0 p1) x0)
      (requires True)
      (ensures fun _ -> x0 == x1)
  = rewrite (pts_to r p0 x0) (pts_to0 r p0 x0);
    elim_pure _;
    rewrite (pts_to r p1 x1) (pts_to0 r p1 x1);
    elim_pure _;
    R.gather r (Some (Ghost.reveal x0, p0)) (Some (Ghost.reveal x1, p1));
    rewrite (pts_to0 r (sum_perm p0 p1) x0) (pts_to r (sum_perm p0 p1) x0)

let free #_ #_ #v r =
  rewrite
    (pts_to r full_perm (Ghost.reveal v))
    (pts_to0 r full_perm (Ghost.reveal v));
  elim_pure _;
  R.free r;
  drop (R.pts_to r (P.Mkpcm'?.one (P.Mkpcm?.p P.pcm_frac)))
