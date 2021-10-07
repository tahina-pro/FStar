(*
   Copyright 2021 Microsoft Research

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
module Steel.Loops
open Steel.Effect.Common
open Steel.Effect
module AT = Steel.Effect.Atomic
module U32 = FStar.UInt32

(* This module provides some common iterative looping combinators *)

let nat_at_most (f:U32.t)
  = x:nat{ x <= U32.v f }

let u32_between (s f:U32.t)
  = x:U32.t { U32.v s <= U32.v x /\ U32.v x < U32.v f}

/// for_loop: for (i = start; i < finish; i++) inv { body i }
val for_loop (start:U32.t)
             (finish:U32.t { U32.v start <= U32.v finish })
             (inv: nat_at_most finish -> vprop)
             (body:
                    (i:u32_between start finish ->
                          SteelT unit
                          (inv (U32.v i))
                          (fun _ -> inv (U32.v i + 1))))
  : SteelT unit
      (inv (U32.v start))
      (fun _ -> inv (U32.v finish))

/// while_loop: while (cond()) { body () }
val while_loop (inv: Ghost.erased bool -> vprop)
               (cond: (unit -> SteelT bool
                                     (AT.h_exists inv)
                                     (fun b -> inv b)))
               (body: (unit -> SteelT unit
                                     (inv true)
                                     (fun _ -> AT.h_exists inv)))
  : SteelT unit
    (AT.h_exists inv)
     (fun _ -> inv false)

/// Alternative while loop combinator with 3 vprops instead of 2

val while3
  (test_vpre: vprop)
  (test_pre: t_of test_vpre -> prop)
  (test_vpost: bool -> Tot vprop)
  (test_post: (b: bool) -> t_of (test_vpost b) -> Tot prop)
  (test: unit ->
    Steel bool
    (test_vpre)
    (fun x -> test_vpost x)
    (requires (fun h -> test_pre (h test_vpre)))
    (ensures (fun _ x h' -> test_post x (h' (test_vpost x))))
  )
  (body: unit -> Steel unit
    (test_vpost true)
    (fun _ -> test_vpre)
    (requires (fun h -> test_post true (h (test_vpost true))))
    (ensures (fun _ _ h' -> test_pre (h' test_vpre)))
  )
: Steel unit
    (test_vpre)
    (fun _ -> test_vpost false)
    (requires (fun h -> test_pre (h test_vpre)))
    (ensures (fun _ _ h' -> test_post false (h' (test_vpost false))))

let while3'
  (inv: vprop)
  (test_pre: t_of inv -> prop)
  (test_post: (b: bool) -> t_of inv -> Tot prop)
  (test: unit ->
    Steel bool
    inv
    (fun _ -> inv)
    (requires (fun h -> test_pre (h inv)))
    (ensures (fun _ x h' -> test_post x (h' inv)))
  )
  (body: unit -> Steel unit
    inv
    (fun _ -> inv)
    (requires (fun h -> test_post true (h inv)))
    (ensures (fun _ _ h' -> test_pre (h' inv)))
  )
: Steel unit
    inv
    (fun _ -> inv)
    (requires (fun h -> test_pre (h inv)))
    (ensures (fun _ _ h' -> test_post false (h' inv)))
=
  while3
    inv
    test_pre
    (fun _ -> inv)
    test_post
    test
    body
