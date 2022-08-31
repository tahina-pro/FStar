module Steel.PCMReference.URef

open FStar.PCM
open Steel.Memory
open Steel.Effect.Common
open Steel.Effect.Atomic

include Steel.PCMReference

val upts_to (r: core_ref) (#a: Type u#1) (p: pcm a) (v: a) : Tot vprop

val intro_upts_to
  (#opened: _)
  (r: core_ref) (#a: Type) (p: pcm a) (v: a)
: SteelGhostT unit opened
    (pts_to #a #p r v)
    (fun _ -> upts_to r p v)

val elim_upts_to
  (#opened: _)
  (r: core_ref) (#a: Type) (p: pcm a) (v: a)
: SteelGhostT unit opened
    (upts_to r p v)
    (fun _ -> pts_to #a #p r v)

val upts_to_unique
  (#opened: _)
  (r: core_ref)
  (#a1: Type)
  (p1: pcm a1)
  (v1: a1)
  (#a2: Type)
  (p2: pcm a2)
  (v2: a2)
: SteelGhost unit opened
    (upts_to r p1 v1 `star`
      upts_to r p2 v2)
    (fun _ -> upts_to r p1 v1 `star`
      upts_to r p2 v2)
  (fun _ -> True)
  (ensures (fun _ _ _ ->
    a1 == a2 /\
    p1 == p2
  ))
