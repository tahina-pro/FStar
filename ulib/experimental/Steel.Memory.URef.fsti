module Steel.Memory.URef
include Steel.Memory

open FStar.PCM

let upts_to (r: core_ref) (#a: Type u#a) (p: pcm a) (v: a) : slprop u#a =
  pts_to #a #p r v

val upts_to_unique
  (r: core_ref)
  (a1: Type u#a)
  (p1: pcm a1)
  (v1: a1)
  (a2: Type u#a)
  (p2: pcm a2)
  (v2: a2)
  (h: mem)
: Lemma
  (requires (
    interp
      (upts_to r p1 v1 `star`
        upts_to r p2 v2)
      h
  ))
  (ensures (
    a1 == a2 /\
    p1 == p2
  ))
