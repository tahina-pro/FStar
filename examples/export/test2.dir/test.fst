module Test
open B

let prf1 : (z: unit { x = 42 } ) = ()

val x : int
let x = 18

let prf2 : (z: unit { x = 18 } ) = ()
