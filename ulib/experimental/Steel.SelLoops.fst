module Steel.SelLoops

open Steel.SelEffect
open Steel.SelEffect.Atomic

let rec while
  t test_vpre test_vpost test body x0
: SteelSelT
  (Ghost.erased t)
    (test_vpre x0)
    (fun res -> test_vpost false res)
  (decreases (Ghost.reveal x0))
=
  let b = test x0 in
  if b
  then begin
    change_equal_slprop
      (test_vpost b x0)
      (test_vpost true x0);
    let x1 = body x0 in
    while t test_vpre test_vpost test body x1
  end else begin
    change_equal_slprop
      (test_vpost b x0)
      (test_vpost false x0);
    return x0
  end
