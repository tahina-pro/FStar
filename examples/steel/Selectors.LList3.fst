module Selectors.LList3

open Steel.FractionalPermission
open Steel.ST.Util
open Steel.ST.Reference
open Steel.ST.Effect

#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  tail_fuel: Ghost.erased nat;
  next: ref (cell a);
  data: a;
}
#pop-options

let next #a (c:cell a) : t a = c.next
let data #a (c:cell a) : a = c.data
let mk_cell #a (n: t a) (d:a) = {
  tail_fuel = Ghost.hide 0;
  next = n;
  data = d
}

let null_llist #a = null
let is_null #a ptr = is_null ptr

let v_null_rewrite
  (a: Type0)
  (_: t_of emp)
: Tot (list a)
= []

let v_c
  (n: Ghost.erased nat)
  (#a: Type0)
  (r: t a)
  (c: t_of (vptr r))
: Tot prop
= ((c <: cell a).tail_fuel < Ghost.reveal n) == true // to ensure vprop termination

let v_c_dep
  (n: Ghost.erased nat)
  (#a: Type0)
  (r: t a)
  (nllist: (n': Ghost.erased nat) -> (r: t a  { Ghost.reveal n' < Ghost.reveal n }) -> Pure vprop (requires True) (ensures (fun y -> t_of y == list a)))
  (c: t_of (C.vrefine (vptr r) (v_c n r)))
: Tot vprop
= nllist (c <: cell a).tail_fuel c.next

let v_c_l_rewrite
  (n: Ghost.erased nat)
  (#a: Type0)
  (r: t a)
  (nllist: (n': Ghost.erased nat) -> (r: t a { Ghost.reveal n' < Ghost.reveal n }) -> Pure vprop (requires True) (ensures (fun y -> t_of y == list a)))
  (res: t_of ((vptr r `C.vrefine` v_c n r) `vdep` v_c_dep n r nllist))
: Tot (list a)
=
  let (| c, l |) = (res <: vdep_t (vptr r `C.vrefine` v_c n r) (v_c_dep n r nllist)) in
  c.data :: l

let rec nllist
  (a: Type0)
  (n: Ghost.erased nat)
  (r: t a)
: Pure vprop
  (requires True)
  (ensures (fun y -> t_of y == list a))
  (decreases (Ghost.reveal n))
= if is_null r
  then emp `C.vrewrite` v_null_rewrite a
  else ((vptr r `C.vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) `C.vrewrite` v_c_l_rewrite n r (nllist a)

let nllist_eq_not_null
  (a: Type0)
  (n: Ghost.erased nat)
  (r: t a)
: Lemma
  (requires (is_null r == false))
  (ensures (
    nllist a n r == ((vptr r `C.vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) `C.vrewrite` v_c_l_rewrite n r (nllist a)
  ))
= assert_norm (nllist a n r ==
    begin if is_null r
    then emp `C.vrewrite` v_null_rewrite a
    else ((vptr r `C.vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) `C.vrewrite` v_c_l_rewrite n r (nllist a)
    end
  )

let llist_vdep
  (#a: Type0)
  (r: t a)
  (c: t_of (vptr r))
: Tot vprop
= nllist a (c <: cell a).tail_fuel c.next

let llist_vrewrite
  (#a: Type0)
  (r: t a)
  (cl: t_of (vptr r `vdep` llist_vdep r))
: Tot (list a)
= (C.vdep_dfst (vptr r) (llist_vdep r) cl).data :: C.vdep_dsnd (vptr r) (llist_vdep r) cl

let llist0
  (#a: Type0)
  (r: t a)
: Pure vprop
  (requires True)
  (ensures (fun y -> t_of y == list a))
= if is_null r
  then emp `C.vrewrite` v_null_rewrite a
  else (vptr r `vdep` llist_vdep r) `C.vrewrite` llist_vrewrite r

#set-options "--print_implicits"

let nllist_of_llist0_post
  (#a: Type0)
  (r: t a)
  (l: Ghost.erased (t_of (llist0 r)))
  (res: Ghost.erased nat)
  (l' : t_of (nllist a res r))
: Tot prop
= (l' <: list a) == Ghost.reveal l

val nllist_of_llist0
  (#inames: _)
  (#a: Type0)
  (r: t a)
  (l: Ghost.erased (t_of (llist0 r)))
: STGhostT (Ghost.erased nat) inames
    (llist0 r `C.vselect` l)
    (fun res -> nllist a res r `C.vrefine0` nllist_of_llist0_post r l res)

#set-options "--ide_id_info_off"

let nllist_of_llist0
  #_ #a r l
=
  if is_null r
  then begin
    let res = Ghost.hide 0 in
    let _ = C.rewrite_eq_l_gen
      (llist0 r)
      (nllist a res r)
      ()
    in
    C.vselect_to_vrefine _ _ _ ();
    res
  end else begin
    let _ = C.rewrite_eq_l_gen
      (llist0 r)
      ((vptr r `vdep` llist_vdep r) `C.vrewrite` llist_vrewrite r)
      ()
    in
    let _ = C.vrewrite_elim (vptr r `vdep` llist_vdep r) (llist_vrewrite r) _ in
    let gk = C.vdep_elim2 (vptr r) (llist_vdep r) _ in
    let _ = C.vrefine_to_vselect _ _ in
    let res = Ghost.hide ((Ghost.reveal gk <: cell a).tail_fuel + 1) in
    let _ = C.vrefine_intro
      (vptr r)
      (v_c res r)
      _
    in
    let _ = C.vdep_intro
      (vptr r `C.vrefine` v_c res r)
      _
      (llist_vdep r _)
      _
      (v_c_dep res r (nllist a))
    in
    C.vrewrite_intro
      ((vptr r `C.vrefine` v_c res r) `vdep` v_c_dep res r (nllist a)) (v_c_l_rewrite res r (nllist a)) _;
    nllist_eq_not_null a res r;
    let _ = C.rewrite_eq_l_gen
      _ // (((vptr r `C.vrefine` v_c res r) `vdep` v_c_dep res r (nllist a)) `C.vrewrite` v_c_l_rewrite res r (nllist a))
      (nllist a res r)
      ()
    in
    C.vselect_to_vrefine _ _ _ ();
    res
  end

let llist0_of_nllist
  (#inames: _)
  (#a: Type0)
  (n: Ghost.erased nat)
  (r: t a)
  (l: Ghost.erased (t_of (nllist a n r)))
: STGhost (Ghost.erased (t_of (llist0 r))) inames
    (nllist a n r `C.vselect` l)
    (fun res -> llist0 r `C.vselect` res)
    (True)
    (fun res -> (Ghost.reveal res <: list a) == (Ghost.reveal l <: list a))
=
  if is_null r
  then begin
    C.rewrite_eq_l_gen
      (nllist a n r)
      (llist0 r)
      ()
  end else begin
    nllist_eq_not_null a n r;
    let _ = C.rewrite_eq_l_gen
      (nllist a n r)
      (((vptr r `C.vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) `C.vrewrite` v_c_l_rewrite n r (nllist a))
      ()
    in
    let _ = C.vrewrite_elim ((vptr r `C.vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) (v_c_l_rewrite n r (nllist a)) _ in
    C.vdep_elim 
      (vptr r `C.vrefine` v_c n r) (v_c_dep n r (nllist a))
      _;
    let _ = C.vrefine_elim (vptr r) (v_c n r) _ in
    let _ = C.vdep_intro
      (vptr r)
      _
      (v_c_dep n r (nllist a) _)
      _
      (llist_vdep r)
    in
    C.vrewrite_intro (vptr r `vdep` llist_vdep r) (llist_vrewrite r) _;
    C.rewrite_eq_l_gen
      ((vptr r `vdep` llist_vdep r) `C.vrewrite` llist_vrewrite r)
      (llist0 r)
      ()
  end

let llist_of_llist0
  (#inames: _)
  (#a: Type)
  (r: t a)
  (l: Ghost.erased (t_of (llist0 r)))
: STGhost (Ghost.erased (list a)) inames
    (llist0 r `C.vselect` l)
    (fun res -> llist r `C.vselect` res)
    (True)
    (fun res -> Ghost.reveal res == (Ghost.reveal l <: list a))
=
  C.vunit_intro (llist0 r) (list a) _

let llist0_of_llist
  (#inames: _)
  (#a: Type)
  (#l: Ghost.erased (list a))
  (r: t a)
: STGhost (Ghost.erased (t_of (llist0 r))) inames
    (llist r `C.vselect` l)
    (fun res -> llist0 r `C.vselect` res)
    True
    (fun res -> (Ghost.reveal res <: list a) == Ghost.reveal l)
=
  C.vunit_elim (llist0 r) (list a) _

let intro_llist_nil a =
  let _ = C.vselect_intro emp in 
  let _ = C.vrewrite_intro emp (v_null_rewrite a) _ in
  C.rewrite_eq_l
    _ // (emp `C.vrewrite` v_null_rewrite a)
    (llist0 (null_llist #a))
    ();
  let _ = llist_of_llist0 _ _ in
  ()

let is_nil
  #a #l ptr
=
  let l0 = llist0_of_llist ptr in
  let res = is_null ptr in
  if res
  then begin
    let _ = C.rewrite_eq_l_gen
      (llist0 ptr)
      (emp `C.vrewrite` v_null_rewrite a)
      ()
    in
    let _ = C.vrewrite_elim emp (v_null_rewrite a) _ in 
    C.vrewrite_intro emp (v_null_rewrite a) _;
    rewrite
      _
      (llist0 ptr `C.vselect` l0)
  end else begin
    let _ = C.rewrite_eq_l_gen
      (llist0 ptr)
      ((vptr ptr `vdep` llist_vdep ptr) `C.vrewrite` llist_vrewrite ptr)
      ()
    in
    let _ = C.vrewrite_elim
      (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr) _
    in
    C.vrewrite_intro
      (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr) _
    ;
    rewrite
      _
      (llist0 ptr `C.vselect` l0)
  end;
  let _ = llist_of_llist0 ptr _ in
  return res

let intro_llist_cons
  #a ptr1 ptr2
=
  let _ = llist0_of_llist ptr2 in
  let n = nllist_of_llist0 ptr2 _ in
  let _ = C.vrefine_to_vselect _ _ in
  (* set the fuel of the new cons cell *)
  let c = vread ptr1 in
  let c' = {c with tail_fuel = n} in
  vwrite ptr1 c' ;
  (* actually cons the cell *)
  vptrp_not_null ptr1;
  let _ = C.vdep_intro
    (vptr ptr1)
    _
    (nllist a n ptr2)
    _
    (llist_vdep ptr1)
  in
  C.vrewrite_intro
    (vptr ptr1 `vdep` llist_vdep ptr1)
    (llist_vrewrite ptr1)
    _
  ;
  let _ = C.rewrite_eq_l_gen
    _
    _
    ()
  in
  let _ = llist_of_llist0 ptr1 _ in
  ()

#set-options "--ide_id_info_off"

let tail
  #a #l ptr
=
  let _ = llist0_of_llist ptr in
  let _ = C.rewrite_eq_l_gen
    (llist0 ptr)
    ((vptr ptr `vdep` llist_vdep ptr) `C.vrewrite` llist_vrewrite ptr)
    ()
  in
  let _ = C.vrewrite_elim
    (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr)
    _
  in
  C.vdep_elim (vptr ptr) (llist_vdep ptr) _;
  (* reset tail fuel to match mk_cell *)
  let c = vread ptr in
  let c' = {c with tail_fuel = Ghost.hide 0} in
  vwrite ptr c' ;
  (* actually destruct the list *)
  let res : t a = c.next in
  let _ = C.rewrite_eq_l_gen
    (llist_vdep ptr _)
    (nllist a c.tail_fuel res)
    ()
  in
  let _ = llist0_of_nllist c.tail_fuel res _ in
  let _ = llist_of_llist0 res _ in
  C.vselect_to_vrefine_2 (vptr ptr) (llist res) _ _ _ ();
  return res
