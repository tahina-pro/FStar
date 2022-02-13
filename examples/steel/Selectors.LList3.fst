module Selectors.LList3

open Steel.FractionalPermission

module C = Steel.ST.Combinators

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
  (c: normal (t_of (vptr r)))
: Tot vprop
= nllist a c.tail_fuel c.next

let llist_vrewrite
  (#a: Type0)
  (r: t a)
  (cl: normal (t_of (vptr r `vdep` llist_vdep r)))
: Tot (list a)
= (dfst cl).data :: dsnd cl

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

let nllist_of_llist0
  (#inames: _)
  (#a: Type0)
  (#l: list a)
  (r: t a)
: STGhostT (Ghost.erased nat) inames
    (llist0 r `C.vrefine` equals (l <: t_of (llist0 r)))
    (fun res -> nllist a res r `C.vrefine` equals (l <: t_of (nllist a res r)))
=
  if is_null r
  then begin
    let res = Ghost.hide 0 in
    rewrite_eq_l
      (llist0 r)
      (nllist a res r)
      ();
    res
  end else begin
    rewrite_eq_l
      (llist0 r)
      ((vptr r `vdep` llist_vdep r) `C.vrewrite` llist_vrewrite r)
      ();
    let _ = vrewrite_vrefine_equals_elim (vptr r `vdep` llist_vdep r) (llist_vrewrite r) _ in
    vdep_elim (vptr r) (llist_vdep r) _;
    let gk = vrefine_equals_gget (vptr r) () in
    let res = Ghost.hide (Ghost.reveal (Ghost.reveal gk <: cell a).tail_fuel + 1) in
    let _ = vrefine_vrefine_equals_intro
      (vptr r)
      (v_c res r)
      _
    in
    let _ = vdep_intro
      (vptr r `C.vrefine` v_c res r)
      (v_c_dep res r (nllist a))
      _
      (llist_vdep r _)
      _
    in
    vrewrite_vrefine_equals_intro
      ((vptr r `C.vrefine` v_c res r) `vdep` v_c_dep res r (nllist a)) (v_c_l_rewrite res r (nllist a)) _;
    nllist_eq_not_null a res r;
    rewrite_eq_l
      (((vptr r `C.vrefine` v_c res r) `vdep` v_c_dep res r (nllist a)) `C.vrewrite` v_c_l_rewrite res r (nllist a))
      (nllist a res r)
      ();
    rewrite_eq_r
      (nllist a res r)
      l;
    res
  end

let llist0_of_nllist
  (#inames: _)
  (#a: Type0)
  (#l: list a)
  (n: Ghost.erased nat)
  (r: t a)
: STGhostT unit inames
    (nllist a n r `C.vrefine` equals (l <: t_of (nllist a n r)))
    (fun _ -> llist0 r `C.vrefine` equals (l <: t_of (llist0 r)))
=
  if is_null r
  then begin
    rewrite_eq_l
      (nllist a n r)
      (llist0 r)
      ();
    ()
  end else begin
    admit_ ()
  end

(*

    nllist_eq_not_null a n r;
    change_equal_slprop
      (nllist a n r)
      (((vptr r `C.vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) `C.vrewrite` v_c_l_rewrite n r (nllist a));
    elim_vrewrite ((vptr r `C.vrefine` v_c n r) `vdep` v_c_dep n r (nllist a)) (v_c_l_rewrite n r (nllist a));
    let gk = elim_vdep (vptr r `C.vrefine` v_c n r) (v_c_dep n r (nllist a)) in
    elim_C.vrefine (vptr r) (v_c n r);
    intro_vdep
      (vptr r)
      (v_c_dep n r (nllist a) (Ghost.reveal gk))
      (llist_vdep r);
    intro_vrewrite (vptr r `vdep` llist_vdep r) (llist_vrewrite r);
    change_equal_slprop
      ((vptr r `vdep` llist_vdep r) `C.vrewrite` llist_vrewrite r)
      (llist0 r)
  end

*)

let llist_of_llist0
  (#inames: _)
  (#a: Type)
  (#l: list a)
  (r: t a)
: STGhostT unit inames
    (llist0 r `C.vrefine` equals (l <: t_of (llist0 r)))
    (fun _ -> llist r `C.vrefine` equals l)
=
  vunit_intro (llist0 r) (list a) _

let llist0_of_llist
  (#inames: _)
  (#a: Type)
  (#l: list a)
  (r: t a)
: STGhostT unit inames
    (llist r `C.vrefine` equals l)
    (fun _ -> llist0 r `C.vrefine` equals (l <: t_of (llist0 r)))
=
  vunit_elim (llist0 r) (list a) _

let intro_llist_nil a =
  let _ = vrefine_equals_intro emp in
  let _ = vrewrite_vrefine_equals_intro0 emp (v_null_rewrite a) _ in
  rewrite_eq_l
    _ // (emp `C.vrewrite` v_null_rewrite a)
    _ // (llist0 (null_llist #a))
    ();
  rewrite_eq_r
    _
    _;
  llist_of_llist0 _

let is_nil
  #a ptr
=
  llist0_of_llist ptr;
  let res = is_null ptr in
  if res
  then begin
    rewrite_eq_l
      (llist0 ptr)
      (emp `C.vrewrite` v_null_rewrite a)
      ();
    let _ = vrewrite_vrefine_equals_elim emp (v_null_rewrite a) _ in 
    let _ = vrewrite_vrefine_equals_intro0 emp (v_null_rewrite a) _ in
    rewrite_eq_l
      _
      _
      ();
    rewrite_eq_r
      _
      _
  end else begin
    rewrite_eq_l
      (llist0 ptr)
      ((vptr ptr `vdep` llist_vdep ptr) `C.vrewrite` llist_vrewrite ptr)
      ();
    let _ = vrewrite_vrefine_equals_elim
      (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr) _
    in
    let _ = vrewrite_vrefine_equals_intro0
      (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr) _
    in
    rewrite_eq_l
      _
      _
      ();
    rewrite_eq_r
      _
      _
  end;
  llist_of_llist0 ptr;
  return res

let intro_llist_cons
  #a ptr1 ptr2
=
  llist0_of_llist ptr2;
  let n = nllist_of_llist0 ptr2 in
  (* set the fuel of the new cons cell *)
  let c = vread ptr1 in
  let c' = {c with tail_fuel = n} in
  vwrite ptr1 c' ;
  (* actually cons the cell *)
  vptrp_not_null ptr1;
  let _ = vdep_intro
    (vptr ptr1)
    (llist_vdep ptr1)
    _
    (nllist a n ptr2)
    _
  in
  let _ = vrewrite_vrefine_equals_intro0
    (vptr ptr1 `vdep` llist_vdep ptr1)
    (llist_vrewrite ptr1)
    _
  in
  rewrite_eq_l _ _ ();
  rewrite_eq_r _ _;
  llist_of_llist0 ptr1

#set-options "--ide_id_info_off"

let tail
  #a #l ptr
=
  llist0_of_llist ptr;
  rewrite_eq_l
    (llist0 ptr)
    ((vptr ptr `vdep` llist_vdep ptr) `C.vrewrite` llist_vrewrite ptr)
    ();
  let _ = vrewrite_vrefine_equals_elim
    (vptr ptr `vdep` llist_vdep ptr) (llist_vrewrite ptr)
    _
  in
  vdep_elim (vptr ptr) (llist_vdep ptr) _;
  (* reset tail fuel to match mk_cell *)
  let c = vread ptr in
  let c' = {c with tail_fuel = Ghost.hide 0} in
  vwrite ptr c' ;
  (* actually destruct the list *)
  let res : t a = c.next in
  rewrite_eq_l
    (llist_vdep ptr _)
    (nllist a c.tail_fuel res)
    ();
  llist0_of_nllist c.tail_fuel res;
  llist_of_llist0 res;
//  let g = vrefine_equals_gget (llist res) () in
//  vrefine_equals_star_intro (vptr ptr) (llist res) _ _;
//  vrefine_intro (vptr ptr `star` llist res) (tail_postcond l ptr res) _;
  admit_ ();
  return #(t a) res
