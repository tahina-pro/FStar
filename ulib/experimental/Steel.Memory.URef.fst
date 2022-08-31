module Steel.Memory.URef
friend Steel.Memory

module H = Steel.Heap.URef

let upts_to_unique
  r a1 p1 v1 a2 p2 v2 h
= H.upts_to_unique r a1 p1 v1 a2 p2 v2 h.heap
