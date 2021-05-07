module Steel.SelLoops

open Steel.SelEffect

 // pure pre and postconditions should be embedded in vprops with vrefine

val while
  (t: Type)
  (test_vpre: (Ghost.erased t -> vprop))
  (test_pre: (x: Ghost.erased t) -> (y: (t_of (test_vpre x))) -> Tot prop)
  (test_vpost: bool -> Ghost.erased t -> Tot vprop)
  (test_post: (b: bool) -> (x: Ghost.erased t) -> (y: (t_of (test_vpost b x))) -> Tot prop)
  (test: (e: Ghost.erased t) ->
    SteelSel bool
    (test_vpre e)
    (fun x -> test_vpost x e)
    (fun h -> test_pre e (h (test_vpre e)))
    (fun _ b h' -> test_post b e (h' (test_vpost b e)))
  )
  (body: (e: Ghost.erased t) -> SteelSel (Ghost.erased t)
    (test_vpost true e)
    (fun res -> test_vpre res)
    (fun h -> test_post true e (h (test_vpost true e)))
    (fun _ res h' ->
      test_pre res (h' (test_vpre res)) /\
      Ghost.reveal res << Ghost.reveal e
    )
  )
  (x0: Ghost.erased t)
: SteelSel (Ghost.erased t)
    (test_vpre x0)
    (fun res -> test_vpost false res)
    (fun h -> test_pre x0 (h (test_vpre x0)))
    (fun _ res h' -> test_post false res (h' (test_vpost false res)))
