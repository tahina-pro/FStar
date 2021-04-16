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

module Steel.SelArray
open Steel.Memory
open Steel.SelEffect
open FStar.Ghost
module U32 = FStar.UInt32

val array (t:Type u#0) : Type u#0
val length (#t: Type) (a: array t) : GTot nat

val is_array (#a:Type0) (r:array a) : slprop u#1
val array_sel (#a:Type0) (r:array a) : selector (Seq.lseq a (length r)) (is_array r)

[@@ __steel_reduce__]
let varray' #a r : vprop' =
  {hp = is_array r;
   t = Seq.lseq a (length r);
   sel = array_sel r}

[@@ __steel_reduce__]
let varray r = VUnit (varray' r)

[@@ __steel_reduce__]
let asel (#a:Type) (#p:vprop) (r:array a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (varray r) /\ True)})
: GTot (Seq.lseq a (length r))
  = h (varray r)


(* Splitting an array (inspired from Steel.Array) *)

val adjacent
  (#t: Type)
  (r1 r2: array t)
: Tot prop

val merge
  (#t: Type)
  (r1 r2: array t)
: Ghost (array t)
  (requires (adjacent r1 r2))
  (ensures (fun _ -> True))

let merge_into
  (#t: Type)
  (r1 r2 r3: array t)
: Tot prop
= adjacent r1 r2 /\
  merge r1 r2 == r3

val freeable (#t: Type) (a: array t) : Tot prop

val join (#t:Type) (al ar:array t)
  : SteelSel (array t)
          (varray al `star` varray ar)
          (fun a -> varray a)
          (fun _ -> adjacent al ar)
          (fun h a h' ->
            let s = h' (varray a) in
            s == (h (varray al) `Seq.append` h (varray ar)) /\
            merge_into al ar a
          )

val split (#t:Type) (a:array t) (i:U32.t)
  : SteelSel (array t & array t)
          (varray a)
          (fun res -> varray (fst res) `star` varray (snd res))
          (fun _ -> U32.v i <= length a)
          (fun h (al, ar) h' ->
            let s = h (varray a) in
            let sl = h' (varray al) in
            let sr = h' (varray ar) in
            U32.v i <= length a /\
            merge_into al ar a /\
            sl == Seq.slice s 0 (U32.v i) /\
            sr == Seq.slice s (U32.v i) (length a)
          )

val alloc (#t:Type) (x:t) (n:U32.t)
  : SteelSel (array t)
             vemp
             (fun r -> varray r)
             (requires fun _ -> True)
             (ensures fun _ r h1 ->
               asel r h1 == Seq.create (U32.v n) x /\
               freeable r
             )

val index (#t:Type) (r:array t) (i:U32.t)
  : SteelSel t
             (varray r)
             (fun _ -> varray r)
             (requires fun _ -> U32.v i < length r)
             (ensures fun h0 x h1 ->
               let s = asel r h1 in
               U32.v i < length r /\
               asel r h0 == s /\
               x == Seq.index s (U32.v i))

val upd (#t:Type) (r:array t) (i:U32.t) (x:t)
  : SteelSel unit
             (varray r)
             (fun _ -> varray r)
             (requires fun h -> U32.v i < length r)
             (ensures fun h0 _ h1 ->
               U32.v i < length r /\
               asel r h1 == Seq.upd (asel r h0) (U32.v i) x)

val free (#t:Type) (r:array t)
  : SteelSel unit
             (varray r)
             (fun _ -> vemp)
             (requires fun _ -> freeable r)
             (ensures fun _ _ _ -> True)
