module Steel.PCMReference.URef

friend Steel.PCMReference

module M = Steel.Memory.URef

let upts_to r p v =
  to_vprop (M.upts_to r p v)

let intro_upts_to
  r p v
=
  rewrite_slprop
    (pts_to #_ #p r v)
    (upts_to r p v)
  (fun _ -> ())

let elim_upts_to
  r p v
= rewrite_slprop
    (upts_to r p v)
    (pts_to #_ #p r v)
  (fun _ -> ())

let upts_to_unique
  r #a1 p1 v1 #a2 p2 v2
=
  extract_info_raw
    (upts_to r p1 v1 `star` upts_to r p2 v2)
    (a1 == a2 /\ p1 == p2)
    (fun m ->
      M.upts_to_unique r a1 p1 v1 a2 p2 v2 m
    )
