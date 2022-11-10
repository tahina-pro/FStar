module TE

open Steel.Effect.Common
open Steel.Effect
open Steel.Effect.Atomic

let equals (#a: Type) (x y: a) : Tot prop = x == y

#restart-solver
let vdep_intro'
  (#inames: _)
  (vtag: vprop)
  (vpl: (t_of vtag -> Tot vprop))
  (tag: t_of vtag)
  (vpl0: vprop)
  (pl: t_of vpl0)
: SteelGhost (Ghost.erased (normal (t_of (vtag `vdep` vpl)))) inames
    ((vtag `vrefine` equals tag) `star` (vpl0 `vrefine` equals pl))
    (fun res -> (vtag `vdep` vpl) `vrefine` equals (Ghost.reveal res))
    (fun _ -> vpl0 == vpl tag)
    (fun _ res _ ->
      vpl0 == vpl tag /\
      dfst (Ghost.reveal res) == tag /\
      dsnd (Ghost.reveal res) == pl
    )
= elim_vrefine vtag (equals tag);
  elim_vrefine vpl0 (equals pl);
  intro_vdep vtag vpl0 vpl; // FIXME: F* fails to prove stateful precondition about the selector value of vtag: vpl0 == vpl (h vtag), which should hold since: h vtag == tag
  let res : Ghost.erased (normal (t_of (vtag `vdep` vpl))) = (| tag, pl |) in
  intro_vrefine (vtag `vdep` vpl) (equals (Ghost.reveal res));
  res
