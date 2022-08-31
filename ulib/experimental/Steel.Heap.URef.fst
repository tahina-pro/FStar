module Steel.Heap.URef
friend Steel.Heap

open FStar.PCM

let upts_to_unique
  r a1 p1 v1 a2 p2 v2 h
= elim_star
    (pts_to #a1 #p1 r v1)
    (pts_to #a2 #p2 r v2)
    h
