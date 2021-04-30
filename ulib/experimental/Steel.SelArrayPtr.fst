module Steel.SelArrayPtr

(* We could implement this module as a pointer to an array, 
   but we would like to be as close as possible to C 
   pointers, i.e. as base+offset.
 *)
friend Steel.SelArray
module A = Steel.SelArray

let to_v
  (#t: Type)
  (base: A.array1 t)
  (from: U32.t)
: Tot Type0
= (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= Seq.length base })

let to_t
  (#t: Type)
  (base: A.array1 t)
  (from: U32.t)
: Tot Type0
= (to_v base from) // FIXME: should be Ghost.erased (to_v a), but we currently cannot because of the case analysis in Steel.SelArray.vappend; we need support for something like SteelSelGhost

noeq
type t (a: Type u#0) = {
  base: A.array1 a;
  from: U32.t;
  to: ref (to_t base from);
}

let mk_t (#a: Type u#0) (base: A.array1 a) (from: U32.t) (to: ref (to_t base from)) : Tot (t a) =
  {
    base = base;
    from = from;
    to = to;
  }

let array_of
  (#a: Type)
  (p: t a)
  (to: to_t p.base p.from)
: Tot (A.array a)
= {
  A.base = p.base;
  A.from = p.from;
  A.to = to;
}

let varrayptr0_dep
  (#a: Type)
  (p: t a)
  (to: to_t p.base p.from)
: Tot vprop
= A.varray (array_of p to)

let varrayptr0_rewrite
  (#a: Type)
  (p: t a)
  (x: normal (t_of (vptr p.to `vdep` varrayptr0_dep p)))
: Tot (v a)
= let (| to, contents |) = x in
  {
    array = array_of p to;
    contents = contents;
  }

let varrayptr0
  (#a: Type)
  (r: t a)
: Tot vprop
= (vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r

let is_arrayptr #a r = hp_of (varrayptr0 r)

let arrayptr_sel #a r = fun h -> sel_of (varrayptr0 r) h

let intro_varrayptr
  (#a: Type)
  (r: t a)
: SteelSel unit
    ((vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r)
    (fun _ -> varrayptr r)
    (fun _ -> True)
    (fun h0 _ h1 -> h1 (varrayptr r) == h0 ((vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r))
=
  change_slprop_rel
    ((vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r)
    (varrayptr r)
    (fun x y -> x == y)
    (fun _ -> ())

let elim_varrayptr
  (#a: Type)
  (r: t a)
: SteelSel unit
    (varrayptr r)
    (fun _ -> (vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r)
    (fun _ -> True)
    (fun h0 _ h1 -> h0 (varrayptr r) == h1 ((vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r))
=
  change_slprop_rel
    (varrayptr r)
    ((vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r)
    (fun x y -> x == y)
    (fun _ -> ())

#push-options "--z3rlimit 32"
let join #a al ar =
  elim_varrayptr al;
  elim_vrewrite (vptr al.to `vdep` varrayptr0_dep al) (varrayptr0_rewrite al);
  let g_al_to = elim_vdep (vptr al.to) (varrayptr0_dep al) in
  let al_to = read al.to in // FIXME: if to_t is Ghost, then this read is not necessary
  let aal = array_of al al_to in
  change_equal_slprop
    (varrayptr0_dep al (Ghost.reveal g_al_to))
    (A.varray aal);
  elim_varrayptr ar;
  elim_vrewrite (vptr ar.to `vdep` varrayptr0_dep ar) (varrayptr0_rewrite ar);
  let g_ar_to = elim_vdep (vptr ar.to) (varrayptr0_dep ar) in
  let ar_to = read ar.to in // same here
  free ar.to;
  let aar = array_of ar ar_to in
  change_equal_slprop
    (varrayptr0_dep ar (Ghost.reveal g_ar_to))
    (A.varray aar);
  let aj = A.join aal aar in
  let ar_to : U32.t = ar_to in
  let ar_to : to_t al.base al.from = ar_to in
  write al.to ar_to;
  assert (aj == array_of al ar_to);
  intro_vdep (vptr al.to) (A.varray aj) (varrayptr0_dep al);
  intro_vrewrite (vptr al.to `vdep` varrayptr0_dep al) (varrayptr0_rewrite al);
  intro_varrayptr al
#pop-options

let u32_bounded_add
  (x y: U32.t) (z: Ghost.erased U32.t)
: Pure U32.t
  (requires (U32.v x + U32.v y <= U32.v z))
  (ensures (fun t -> U32.v t == U32.v x + U32.v y))
=
  x `U32.add` y

#push-options "--z3rlimit 32"
#restart-solver
let split #a x i =
  elim_varrayptr x;
  elim_vrewrite (vptr x.to `vdep` varrayptr0_dep x) (varrayptr0_rewrite x);
  let g_x_to = elim_vdep (vptr x.to) (varrayptr0_dep x) in
  let x_to = read x.to in // same here
  let xa = array_of x x_to in
  change_equal_slprop
    (varrayptr0_dep x (Ghost.reveal g_x_to))
    (A.varray xa);
  let res2 = A.split xa i in
  reveal_star (A.varray (A.pfst res2)) (A.varray (A.psnd res2));
  let x_to : U32.t = x_to in
  let j : to_t x.base x.from = u32_bounded_add x.from i x_to in
  let x_to : to_t x.base j = x_to in
  write x.to j;
  assert (A.pfst res2 == array_of x j);
  intro_vdep
    (vptr x.to)
    (A.varray (A.pfst res2))
    (varrayptr0_dep x);
  intro_vrewrite (vptr x.to `vdep` varrayptr0_dep x) (varrayptr0_rewrite x);
  intro_varrayptr x;
  let to2 : ref (to_t x.base j) = alloc x_to in
  let res : t a = mk_t x.base j to2 in
  assert (A.psnd res2 == array_of res x_to);
  change_equal_slprop
    (vptr to2)
    (vptr res.to);
  intro_vdep
    (vptr res.to)
    (A.varray (A.psnd res2))
    (varrayptr0_dep res);
  intro_vrewrite (vptr res.to `vdep` varrayptr0_dep res) (varrayptr0_rewrite res);
  intro_varrayptr res;
  res
#pop-options

let alloc
  #a x n
=
  Seq.slice_length (Seq.create (U32.v n) x);
  let ar = A.alloc2 x n in
  let n2 : to_t ar.A.base 0ul = n in
  let to : ref (to_t ar.A.base 0ul) = alloc n2 in
  let res = {
    base = ar.A.base;
    from = 0ul;
    to = to;
  } in
  assert (array_of res n2 == ar);
  change_equal_slprop
    (vptr to)
    (vptr res.to);
  intro_vdep
    (vptr res.to)
    (A.varray ar)
    (varrayptr0_dep res);
  intro_vrewrite (vptr res.to `vdep` varrayptr0_dep res) (varrayptr0_rewrite res);
  intro_varrayptr res;
  res

let index
  #a r i
=
  elim_varrayptr r;
  elim_vrewrite (vptr r.to `vdep` varrayptr0_dep r) (varrayptr0_rewrite r);
  let g = elim_vdep (vptr r.to) (varrayptr0_dep r) in
  let to = read r.to in
  let ar = array_of r to in
  change_equal_slprop
    (varrayptr0_dep r (Ghost.reveal g))
    (A.varray ar);
  let res = A.index ar i in
  intro_vdep
    (vptr r.to)
    (A.varray ar)
    (varrayptr0_dep r);
  intro_vrewrite (vptr r.to `vdep` varrayptr0_dep r) (varrayptr0_rewrite r);
  intro_varrayptr r;
  res

let upd
  #a r i x
=
  elim_varrayptr r;
  elim_vrewrite (vptr r.to `vdep` varrayptr0_dep r) (varrayptr0_rewrite r);
  let g = elim_vdep (vptr r.to) (varrayptr0_dep r) in
  let to = read r.to in
  let ar = array_of r to in
  change_equal_slprop
    (varrayptr0_dep r (Ghost.reveal g))
    (A.varray ar);
  A.upd ar i x;
  intro_vdep
    (vptr r.to)
    (A.varray ar)
    (varrayptr0_dep r);
  intro_vrewrite (vptr r.to `vdep` varrayptr0_dep r) (varrayptr0_rewrite r);
  intro_varrayptr r

let free #a r =
  elim_varrayptr r;
  elim_vrewrite (vptr r.to `vdep` varrayptr0_dep r) (varrayptr0_rewrite r);
  let g = elim_vdep (vptr r.to) (varrayptr0_dep r) in
  let to = read r.to in
  free r.to;
  let ar = array_of r to in
  change_equal_slprop
    (varrayptr0_dep r (Ghost.reveal g))
    (A.varray ar);
  A.free ar
