module Steel.ST.PCMReference.URef

module C = Steel.ST.Coercions
module P = Steel.PCMReference.URef

let upts_to = P.upts_to

let intro_upts_to
  r p v
= C.coerce_ghost (fun _ -> P.intro_upts_to r p v)

let elim_upts_to
  r p v
= C.coerce_ghost (fun _ -> P.elim_upts_to r p v)

let upts_to_unique
  r p1 v1 p2 v2
= C.coerce_ghost (fun _ -> P.upts_to_unique r p1 v1 p2 v2)
