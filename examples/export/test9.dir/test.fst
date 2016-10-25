module Test
module B = C
open B

let y = x

let prf : (z : unit {y = 18}) = ()
