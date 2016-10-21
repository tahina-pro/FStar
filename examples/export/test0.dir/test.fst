module Test

val k : unit
let k = ()

val y : int
let y = A.x

let prf : (z: unit {y = 42})
  = ()
