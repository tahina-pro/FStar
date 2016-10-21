module Test
open A

val y : int
let y = x

let prf : (z: unit {y = 42})
  = ()
