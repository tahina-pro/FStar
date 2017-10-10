module Tes
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32

inline_for_extraction
let f1 (x: U32.t) : HST.Stack U32.t (requires (fun _ -> True)) (ensures (fun _ z _ -> UInt32.v z <= 18)) = 2ul

inline_for_extraction
let f2 (x: U32.t) : HST.Stack U32.t  (requires (fun _ -> True)) (ensures (fun _ _ _ -> True)) = 4ul

inline_for_extraction
let g (x1 x2: U32.t) : HST.Stack U32.t  (requires (fun _ -> UInt32.v x1 + UInt32.v x2 <= UInt.max_int 32)) (ensures (fun _ _ _ -> True)) = U32.add x1 x2

inline_for_extraction
let test (x: U32.t) (y: U32.t) : HST.Stack U32.t  (requires (fun _ -> UInt32.v y > 0)) (ensures (fun _ _ _ -> True)) =
  if x = 0ul
  then
    let v = f1 y in
    let y' = U32.sub y 1ul in
    let v' = f1 y' in
    g v v'
  else
    f2 y
