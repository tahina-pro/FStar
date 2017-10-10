module Tes4
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32

inline_for_extraction
let f1 (x: bool) : HST.Stack U32.t (requires (fun _ -> True)) (ensures (fun _ z _ -> UInt32.v z <= 18)) = 2ul

inline_for_extraction
let f1' (x: bool) : HST.Stack U32.t (requires (fun _ -> True)) (ensures (fun _ z _ -> UInt32.v z <= 18)) = 3ul

inline_for_extraction
let f2 (x: bool) : HST.Stack U32.t  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True)) = 4ul

inline_for_extraction
let g
  (k1: ((x: bool) -> HST.Stack U32.t (requires (fun _ -> True)) (ensures (fun _ z _ -> UInt32.v z <= 18))))
  (k2: ((y: UInt32.t) -> (x: bool) -> HST.Stack U32.t (requires (fun _ -> UInt32.v y <= 18)) (ensures (fun _ z _ -> UInt32.v z <= 18))))
  (x: bool)
: HST.Stack U32.t  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
= let y1 = k1 x in
  let x' = x && (UInt32.lt y1 6ul) in
  let y2 = k2 y1 x' in
  U32.add y1 y2

inline_for_extraction
let test (x y: bool) : HST.Stack U32.t  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True)) =
  if x
  then
    g f1 (fun y -> if UInt32.lt y 17ul then f1 else f1') y
  else
    f2 y
