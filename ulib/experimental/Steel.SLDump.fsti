module Steel.SLDump

include Steel.SLDump.Base
include Steel.Effect
include Steel.Effect.Atomic

val sldump'
  (#opened: _)
  (p: vprop)
  (text: string)
  (sq: squash (sldump_prop text p))
  (_: unit)
: SteelGhost unit opened p (fun _ -> p) (fun _ -> True) (fun h _ h' -> h' p == h p) // TODO: replace with frame_equalities p h h'?

val sldump
  (#opened: _)
  (#[@@@framing_implicit] p: vprop)
  (text: string)
  (#[@@@framing_implicit] sq: squash (sldump_prop text p))
  (_: unit)
: SteelGhostF unit opened p (fun _ -> p) (fun _ -> True) (fun h _ h' -> h' p == h p) // TODO: replace with frame_equalities p h h'?
