module FStar.DMap

let dmap = nat -> (t: Type0 & t)

let type_of_dmap (d: dmap) (i: nat) : Tot Type0 = dfst (d i)

let value_of_dmap (d: dmap) (i: nat) (t: Type0) : Pure t
  (requires (type_of_dmap d i == t))
  (ensures (fun _ -> True))
= dsnd (d i)

irreducible let norm_dmap : unit = ()

