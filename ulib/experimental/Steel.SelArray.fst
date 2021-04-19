module Steel.SelArray

(* Once brought into the Z3 context, the following equations allow sequences to behave like lists *)

let seq_facts () : Lemma (
  (forall (t: Type) (s: Seq.seq t) .
    Seq.length s == 0 ==> s == Seq.empty) /\
  (forall (t: Type) (a: t) (s: Seq.seq t) .
    Seq.head (Seq.cons a s) == a /\ Seq.tail (Seq.cons a s) == s) /\
  (forall (t: Type) (s: Seq.seq t) .
    Seq.length s > 0 ==>
    s == Seq.cons (Seq.head s) (Seq.tail s))
) =
  let e
    (t: Type) (s: Seq.seq t)
  : Lemma
    (Seq.length s == 0 ==> s == Seq.empty)
  =
    if Seq.length s = 0 then assert (s `Seq.equal` Seq.empty)
  in
  let f
    (t: Type) (a: t) (s: Seq.seq t)
  : Lemma
    (Seq.head (Seq.cons a s) == a /\ Seq.tail (Seq.cons a s) == s)
  = Seq.head_cons a s;
    Seq.lemma_tl a s
  in
  let g
    (t: Type) (s: Seq.seq t)
  : Lemma
    (Seq.length s > 0 ==> s == Seq.cons (Seq.head s) (Seq.tail s))
  =
    if Seq.length s > 0
    then Seq.cons_head_tail s
  in
  Classical.forall_intro_2 e;
  Classical.forall_intro_3 f;
  Classical.forall_intro_2 g

let array t = Seq.seq (ref t)
let length #t a = Seq.length a

let vnil_rewrite
  (t: Type)
  (x: t_of vemp)
: GTot (Seq.lseq t 0)
= Seq.empty

let vnil
  (t: Type)
: Pure vprop
  (requires True)
  (ensures (fun v -> t_of v == Seq.lseq t 0))
= vrewrite vemp (vnil_rewrite t)

let vcons_rewrite
  (#t: Type)
  (n: nat)
  (r: ref t)
  (v: vprop)
  (sq: squash (t_of v == Seq.lseq t n))
  (xy: t_of (vptr r `star` v))
: GTot (Seq.lseq t (n + 1))
= Seq.cons (fst xy) (snd xy)

let vcons
  (#t: Type)
  (n: nat)
  (r: ref t)
  (v: vprop)
: Pure vprop
  (requires (t_of v == Seq.lseq t n))
  (ensures (fun v' -> t_of v' == Seq.lseq t (n + 1)))
= vrewrite (vptr r `star` v) (vcons_rewrite n r v ())

let rec varray1
  (#t: Type0)
  (a: array t)
: Pure vprop
  (requires True)
  (ensures (fun v -> t_of v == Seq.lseq t (length a)))
  (decreases (length a))
= if length a = 0
  then vnil t
  else vcons (Seq.length a - 1) (Seq.index a 0) (varray1 (Seq.slice a 1 (length a)))

let is_array #a r = hp_of (varray1 r)

let array_sel #a r = fun h -> sel_of (varray1 r) h

let intro_varray
  (#t: Type)
  (r: array t)
: SteelSel unit
    (varray1 r)
    (fun _ -> varray r)
    (fun _ -> True)
    (fun h _ h' -> h' (varray r) == h (varray1 r))
=
  let m = get #(varray1 r) () in
  let x : Ghost.erased (t_of (varray1 r)) = Ghost.hide (m (varray1 r <: vprop)) in
  let x' : Ghost.erased (Seq.lseq t (length r)) = Ghost.hide (Ghost.reveal x) in
  change_slprop
    (varray1 r)
    (varray r)
    x
    x'
    (fun _ -> ())

#restart-solver

unfold
let coerce (#t1: Type) (x: t1) (t2: Type) : Pure t2
  (requires (t1 == t2))
  (ensures (fun y -> y == x))
= x

let elim_varray
  (#t: Type)
  (r: array t)
: SteelSel unit
    (varray r)
    (fun _ -> varray1 r)
    (fun _ -> True)
    (fun h _ h' -> h' (varray1 r) == h (varray r))
=
  let m = get #(varray r) () in
  let x : Ghost.erased (t_of (varray r)) = Ghost.hide (m (varray r)) in
  assert (t_of (varray1 r) == t_of (varray r));
  let x' : Ghost.erased (t_of (varray1 r)) = Ghost.hide (coerce (Ghost.reveal x) (t_of (varray1 r))) in
  change_slprop
    (varray r)
    (varray1 r)
    x
    x'
    (fun _ -> ())

let intro_vnil1
  (t: Type)
: SteelSel (array t)
    vemp
    (fun r -> varray1 r)
    (fun _ -> True)
    (fun _ r _ -> length r == 0)
=
  intro_vrewrite vemp (vnil_rewrite t);
  let r : array t = Seq.empty in
  change_slprop
    (vrewrite vemp (vnil_rewrite t))
    (varray1 r)
    (Ghost.hide (Seq.empty #t <: t_of (vrewrite vemp (vnil_rewrite t))))
    (Ghost.hide (Seq.empty #t <: t_of (varray1 r)))
    (fun _ -> ());
  r

let intro_vnil
  (t: Type)
: SteelSel (array t)
    vemp
    (fun r -> varray r)
    (fun _ -> True)
    (fun _ r h' ->
      r == Seq.empty /\
      h' (varray r) == Seq.empty
    )
=
  seq_facts ();
  let res = intro_vnil1 t in
  intro_varray res;
  res

let intro_vcons1
  (#t: Type)
  (r: ref t)
  (a: array t)
: SteelSel (array t)
    (vptr r `star` varray1 a)
    (fun a' -> varray1 a')
    (fun _ -> True)
    (fun h a' h' ->
      a' == Seq.cons r a /\
      (coerce (h' (varray1 a')) (Seq.lseq t (Seq.length a')) <: Seq.seq t) ==
        Seq.cons (h (vptr r)) (coerce (h (varray1 a)) (Seq.lseq t (length a)))
    )
=
  seq_facts ();
  reveal_star (vptr r) (varray1 a); // FIXME: WHY WHY WHY?
  intro_vrewrite (vptr r `star` varray1 a) (vcons_rewrite (Seq.length a) r (varray1 a) ());
  let a' : array t = Seq.cons r a in
  change_equal_slprop
    (vrewrite (vptr r `star` varray1 a) (vcons_rewrite (Seq.length a) r (varray1 a) ()))
    (varray1 a');
  a'

let intro_vcons
  (#t: Type)
  (r: ref t)
  (a: array t)
: SteelSel (array t)
    (vptr r `star` varray a)
    (fun a' -> varray a')
    (fun _ -> True)
    (fun h a' h' ->
      a' == Seq.cons r a /\
      h' (varray a') ==
        Seq.cons (h (vptr r)) (h (varray a))
    )
= elim_varray a;
  let res = intro_vcons1 r a in
  intro_varray res;
  res

#set-options "--ide_id_info_off" 

#push-options "--z3rlimit 16"
#restart-solver

let elim_vcons1
  (#t: Type)
  (a: array t)
: SteelSel (ref t & array t)
    (varray1 a)
    (fun res -> vptr (pfst res) `star` varray1 (psnd res))
    (fun _ -> length a > 0)
    (fun h res h' ->
      length a > 0 /\
      begin let s = coerce (h (varray1 a)) (Seq.lseq t (length a)) in
      h' (vptr (pfst res)) == Seq.head s /\
      Seq.tail s == coerce (h' (varray1 (psnd res))) (Seq.lseq t (length (psnd res))) /\
      a == Seq.cons (pfst res) (psnd res)
      end
    )
=
  seq_facts ();
  let a0 : Seq.seq (ref t) = a in
  let r = Seq.head a0 in
  let q = Seq.tail a0 in
  change_equal_slprop
    (varray1 a)
    (vrewrite (vptr (r) `star` varray1 (q)) (vcons_rewrite (Seq.length (q)) (r) (varray1 (q)) ()));
  elim_vrewrite (vptr (r) `star` varray1 (q)) (vcons_rewrite (Seq.length (q)) (r) (varray1 (q)) ());
  reveal_star (vptr (r)) (varray1 (q));
  let res : (ref t & array t) = (r, q) in
  change_equal_slprop
    (vptr (r) `star` varray1 (q))
    (vptr (pfst res) `star` varray1 (psnd res));
  reveal_star (vptr (pfst res)) (varray1 (psnd res));
  res

#pop-options

let elim_vcons
  (#t: Type)
  (a: array t)
: SteelSel (ref t & array t)
    (varray a)
    (fun res -> vptr (pfst res) `star` varray (psnd res))
    (fun _ -> length a > 0)
    (fun h res h' ->
      length a > 0 /\
      begin let s = h (varray a) in
      s == Seq.cons (h' (vptr (pfst res))) (h' (varray (psnd res))) /\
      a == Seq.cons (pfst res) (psnd res)
      end
    )
=
  elim_varray a;
  let res = elim_vcons1 a in
  intro_varray (psnd res);
  res

let elim_nil
  (#t: Type)
  (a: array t)
: SteelSel unit
    (varray a)
    (fun _ -> vemp)
    (fun _ -> length a == 0)
    (fun _ _ _ -> True)
= sladmit ()

let seq_append_nil
  (#t: Type)
  (a2: Seq.seq t)
: Lemma
  (Seq.append Seq.empty a2 == a2)
  [SMTPat (Seq.append Seq.empty a2)]
= assert (Seq.append Seq.empty a2 `Seq.equal` a2)

#push-options "--z3rlimit 16"
#restart-solver

let seq_append_cons
  (#t: Type)
  (c: t)
  (a1 a2: Seq.seq t)
: Lemma
  (Seq.append (Seq.cons c a1) a2 == Seq.cons c (Seq.append a1 a2))
  [SMTPat (Seq.append (Seq.cons c a1) a2)]
=
  assert (Seq.append (Seq.cons c a1) a2 `Seq.equal` Seq.cons c (Seq.append a1 a2))

#pop-options

#push-options "--z3rlimit 16"
#restart-solver

let rec vappend
  (#t: Type)
  (a1 a2: array t)
: SteelSel (array t)
    (varray a1 `star` varray a2)
    (fun r -> varray r)
    (fun _ -> True)
    (fun h r h' ->
      h' (varray r) == Seq.append (h (varray a1)) (h (varray a2)) /\
      r == Seq.append a1 a2
    )
    (decreases (length a1))
=
  seq_facts ();
  if Seq.length a1 = 0
  then begin
    elim_nil a1;
    a2
  end else begin
    let hd_tl = elim_vcons a1 in
    reveal_star_3 (vptr (pfst hd_tl)) (varray (psnd hd_tl)) (varray a2); // FIXME: WHY WHY WHY?
    let tl' = vappend (psnd hd_tl) a2 in
    let res = intro_vcons (pfst hd_tl) tl' in
    res
  end

#pop-options

let slice_cons_left
  (#t: Type)
  (a: t)
  (x: Seq.seq t)
  (i: nat)
: Lemma
  ((i > 0 /\ i <= Seq.length x + 1) ==> Seq.slice (Seq.cons a x) 0 i == Seq.cons a (Seq.slice x 0 (i - 1)))
= if i > 0 && i <= Seq.length x + 1 then assert (Seq.slice (Seq.cons a x) 0 i `Seq.equal` Seq.cons a (Seq.slice x 0 (i - 1)))

let slice_cons_right
  (#t: Type)
  (a: t)
  (x: Seq.seq t)
  (i: nat)
: Lemma
  ((i > 0 /\ i <= Seq.length x + 1) ==> Seq.slice (Seq.cons a x) i (Seq.length x + 1) == Seq.slice x (i - 1) (Seq.length x))
= if i > 0 && i <= Seq.length x + 1 then assert (Seq.slice (Seq.cons a x) i (Seq.length x + 1) `Seq.equal` Seq.slice x (i - 1) (Seq.length x))

#push-options "--z3rlimit 16"  // 256 --fuel 6 --ifuel 6"
#restart-solver

let rec vsplit
  (#t: Type)
  (a: array t)
  (i: U32.t)
: SteelSel (array t & array t)
    (varray a)
    (fun res -> varray (pfst res) `star` varray (psnd res))
    (fun _ -> U32.v i <= length a)
    (fun h res h' ->
      let s = h (varray a) in
      U32.v i <= length a /\
      pfst res `Seq.equal` Seq.slice a 0 (U32.v i) /\
      psnd res `Seq.equal` Seq.slice a (U32.v i) (length a) /\
      h' (varray (pfst res)) == Seq.slice s 0 (U32.v i) /\
      h' (varray (psnd res)) `Seq.equal` Seq.slice s (U32.v i) (length a)
    )
    (decreases (U32.v i))
=
  seq_facts ();
  let m0 = get #(varray a) () in
  if i = 0ul
  then begin
    let n = intro_vnil t in
    reveal_star (varray n) (varray a);
    let res = (n, a) in
    change_equal_slprop
      (varray n `star` varray a)
      (varray (pfst res) `star` varray (psnd res));
    reveal_star (varray (pfst res)) (varray (psnd res));
    res
  end else begin
    let hd_tl : (ref t & array t) = elim_vcons a in
    reveal_star (vptr (pfst hd_tl)) (varray (psnd hd_tl));
    let j = i `U32.sub` 1ul in
    assert (U32.v j == U32.v i - 1);
    let m2 = get #(vptr (pfst hd_tl) `star` varray (psnd hd_tl)) () in
    slice_cons_left (m2 (vptr (pfst hd_tl))) (m2 (varray (psnd hd_tl))) (U32.v i);
    slice_cons_right (m2 (vptr (pfst hd_tl))) (m2 (varray (psnd hd_tl))) (U32.v i);
    let sl_sr = vsplit (psnd hd_tl) j in
    reveal_star_3 (vptr (pfst hd_tl)) (varray (pfst sl_sr)) (varray (psnd sl_sr)); // FIXME: WHY WHY WHY?
    let sl = intro_vcons (pfst hd_tl) (pfst sl_sr) in
    reveal_star (varray sl) (varray (psnd sl_sr));
    let res = (sl, psnd sl_sr) in
    change_equal_slprop
      (varray sl `star` varray (psnd sl_sr))
      (varray (pfst res) `star` varray (psnd res));
    reveal_star (varray (pfst res)) (varray (psnd res));
    res
  end

#pop-options

noeq
type ith_t
  (t: Type)
= {
  ith_lhs: array t;
  ith_item: ref t;
  ith_rhs: array t;
}

let unpack_ith
  (#t: Type)
  (a: array t)
  (i: U32.t)
: SteelSel (ith_t t)
    (varray a)
    (fun res -> varray res.ith_lhs `star` vptr res.ith_item `star` varray res.ith_rhs)
    (fun _ -> U32.v i < length a)
    (fun h res h' ->
      U32.v i < length a /\
      a == Seq.append res.ith_lhs (Seq.cons res.ith_item res.ith_rhs) /\
      can_be_split (varray res.ith_lhs `star` vptr res.ith_item `star` varray res.ith_rhs) (varray res.ith_lhs) /\
      can_be_split (varray res.ith_lhs `star` vptr res.ith_item `star` varray res.ith_rhs) (vptr res.ith_item) /\
      h (varray a) == Seq.append (h' (varray res.ith_lhs)) (Seq.cons (h' (vptr res.ith_item)) (h' (varray res.ith_rhs))) /\
      length res.ith_lhs == U32.v i
    )
=
  let m = get #(varray a) () in
  Seq.lemma_split a (U32.v i);
  Seq.lemma_split (m (varray a)) (U32.v i);
  let rsplit = vsplit a i in
  reveal_star (varray (pfst rsplit)) (varray (psnd rsplit));
  noop ();
  let rcons = elim_vcons (psnd rsplit) in
  reveal_star_3 (varray (pfst rsplit)) (vptr (pfst rcons)) (varray (psnd rcons));
  let res = { ith_lhs = pfst rsplit; ith_item = pfst rcons; ith_rhs = psnd rcons } in
  change_equal_slprop
    (varray (pfst rsplit) `star` vptr (pfst rcons) `star` varray (psnd rcons))
    (varray res.ith_lhs `star` vptr res.ith_item `star` varray res.ith_rhs);
  reveal_star_3 (varray res.ith_lhs) (vptr res.ith_item) (varray res.ith_rhs);
  res

let pack_ith
  (#t: Type)
  (res: ith_t t)
  (a: array t)
: SteelSel unit
    (varray res.ith_lhs `star` vptr res.ith_item `star` varray res.ith_rhs)
    (fun _ -> varray a)
    (fun _ ->
      a == Seq.append res.ith_lhs (Seq.cons res.ith_item res.ith_rhs)
    )
    (fun h _ h' ->
      let i = length res.ith_lhs in
      can_be_split (varray res.ith_lhs `star` vptr res.ith_item `star` varray res.ith_rhs) (varray res.ith_lhs) /\
      can_be_split (varray res.ith_lhs `star` vptr res.ith_item `star` varray res.ith_rhs) (vptr res.ith_item) /\
      h' (varray a) == Seq.append (h (varray res.ith_lhs)) (Seq.cons (h (vptr res.ith_item)) (h (varray res.ith_rhs)))
    )
=
  reveal_star_3 (varray res.ith_lhs) (vptr res.ith_item) (varray res.ith_rhs);
  let rhs = intro_vcons res.ith_item res.ith_rhs in
  reveal_star (varray res.ith_lhs) (varray rhs);
  let a' = vappend res.ith_lhs rhs in
  change_equal_slprop (varray a') (varray a)

let seq_index_append_cons
  (#t: Type)
  (i: nat)
  (a: Seq.seq t) (x: t) (b: Seq.seq t)
: Lemma
  (requires (Seq.length a == i))
  (ensures (Seq.index (Seq.append a (Seq.cons x b)) i == x))
= ()

let seq_upd_append_cons
  (#t: Type)
  (i: nat)
  (y: t)
  (a: Seq.seq t) (x: t) (b: Seq.seq t)
: Lemma
  (Seq.length a == i ==> Seq.upd (Seq.append a (Seq.cons x b)) i y == Seq.append a (Seq.cons y b))
=
  assert (Seq.length a == i ==> Seq.upd (Seq.append a (Seq.cons x b)) i y `Seq.equal` Seq.append a (Seq.cons y b))

let rec valloc
  (#t: Type)
  (i: nat)
  (x: t)
: SteelSel (array t)
    vemp
    (fun res -> varray res)
    (fun _ -> True)
    (fun _ res h' ->
      h' (varray res) == Seq.create i x
    )
    (decreases i)
=
  if i = 0
  then
    let res = intro_vnil t in
    assert (Seq.create 0 x `Seq.equal` Seq.empty);
    noop ();
    res
  else begin
    let hd = Steel.SelEffect.alloc x in
    let j : nat = i - 1 in
    assert (Seq.cons x (Seq.create j x) `Seq.equal` Seq.create i x);
    let tl = valloc j x in
    let res = intro_vcons hd tl in
    res
  end

(* FIXME: refine the model with nontrivial allocation units. To do that, I will need fractional permissions. *)

let adjacent #_ _ _ = True
let merge #t a1 a2 = Seq.append a1 a2
let freeable #t a = True

let join #t al ar =
  vappend al ar

let split #t a i =
  Seq.lemma_split a (U32.v i);
  vsplit a i

let alloc x n = valloc (U32.v n) x

let index #t r i =
  let p = unpack_ith r i in
  let m1 = get #(varray p.ith_lhs `star` vptr p.ith_item `star` varray p.ith_rhs) () in
  seq_index_append_cons (U32.v i) (m1 (varray p.ith_lhs)) (m1 (vptr p.ith_item)) (m1 (varray p.ith_rhs));
  let res = read p.ith_item in 
  pack_ith p r;
  res

let upd #t r i x =
  let p = unpack_ith r i in
  let m1 = get #(varray p.ith_lhs `star` vptr p.ith_item `star` varray p.ith_rhs) () in
  seq_upd_append_cons (U32.v i) x (m1 (varray p.ith_lhs)) (m1 (vptr p.ith_item)) (m1 (varray p.ith_rhs));
  write p.ith_item x;
  pack_ith p r

(* TODO: properly deallocate instead of just dropping the vprop *)
let free #t r =
  reveal_vemp ();
  let res : Ghost.erased (t_of vemp) = Ghost.hide (coerce () (t_of vemp)) in
  change_slprop_2
    (varray r)
    (vemp)
    res
    (fun m -> intro_emp m)
