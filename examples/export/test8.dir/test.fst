module Test
open B

module B = C
let y = x

let prf : (z : unit {y = 18}) = ()
