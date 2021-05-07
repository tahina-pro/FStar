module Steel.SelLoops

open Steel.SelEffect

 // pure pre and postconditions should be embedded in vprops with vrefine

val while
  (t: Type)
  (test_vpre: (Ghost.erased t -> vprop))
  (test_vpost: bool -> Ghost.erased t -> Tot vprop)
  (test: (e: Ghost.erased t) ->
    SteelSelT bool
    (test_vpre e)
    (fun x -> test_vpost x e)
  )
  (body: (e: Ghost.erased t) -> SteelSel (Ghost.erased t)
    (test_vpost true e)
    (fun res -> test_vpre res)
    (fun _ -> True)
    (fun _ res _ ->
      Ghost.reveal res << Ghost.reveal e
    )
  )
  (x0: Ghost.erased t)
: SteelSelT (Ghost.erased t)
    (test_vpre x0)
    (fun res -> test_vpost false res)
