module Steel.SelArray

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

let vcons_rewrite_recip
  (#t: Type)
  (n: nat)
  (r: ref t)
  (v: vprop)
  (sq: squash (t_of v == Seq.lseq t n))
  (l: Seq.lseq t (n + 1))
: GTot (t_of (vptr r `star` v))
= (Seq.head l, Seq.tail l)

let vcons_rewrite_recip_correct
  (#t: Type)
  (n: nat)
  (r: ref t)
  (v: vprop)
  (sq: squash (t_of v == Seq.lseq t n))
: Lemma
  (elim_vrewrite_precond (vptr r `star` v) (vcons_rewrite n r v sq) (vcons_rewrite_recip n r v sq))
  [SMTPat (elim_vrewrite_precond (vptr r `star` v) (vcons_rewrite n r v sq) (vcons_rewrite_recip n r v sq))]
=
  let g (xy: t_of (vptr r `star` v)) 
    : Lemma
      (vcons_rewrite_recip n r v sq (vcons_rewrite n r v sq xy) == xy)
      [SMTPat (vcons_rewrite_recip n r v sq (vcons_rewrite n r v sq xy))]
  = Seq.head_cons (fst xy) (snd xy);
    Seq.lemma_tl (fst xy) (snd xy)
  in
  ()

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

let intro_nil
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

let intro_vcons
  (#t: Type)
  (r: ref t)
  (a: array t)
: SteelSel (array t)
    (vptr r `star` varray1 a)
    (fun a' -> varray1 a')
    (fun _ -> True)
    (fun h a' h' ->
      (coerce (h' (varray1 a')) (Seq.lseq t (Seq.length a')) <: Seq.seq t) ==
        Seq.cons (h (vptr r)) (coerce (h (varray1 a)) (Seq.lseq t (length a)))
    )
=
  reveal_star (vptr r) (varray1 a); // FIXME: WHY WHY WHY?
  intro_vrewrite (vptr r `star` varray1 a) (vcons_rewrite (Seq.length a) r (varray1 a) ());
  let a' : array t = Seq.cons r a in
  Seq.head_cons r a;
  Seq.lemma_tl r a;
  change_equal_slprop
    (vrewrite (vptr r `star` varray1 a) (vcons_rewrite (Seq.length a) r (varray1 a) ()))
    (varray1 a');
  a'

#set-options "--ide_id_info_off" 

#push-options "--z3rlimit 16"
#restart-solver

let elim_vcons
  (#t: Type)
  (a: array t)
: SteelSel (ref t & array t)
    (varray1 a)
    (fun res -> vptr (fst res) `star` varray1 (snd res))
    (fun _ -> length a > 0)
    (fun h res h' ->
      length a > 0 /\
      begin let s = coerce (h (varray1 a)) (Seq.lseq t (length a)) in
      h' (vptr (fst res)) == Seq.head s /\
      Seq.tail s `Seq.equal` coerce (h' (varray1 (snd res))) (Seq.lseq t (length (snd res)))
      end
    )
=
  let m0 = get #(varray1 a) () in
  Seq.cons_head_tail (coerce (m0 (varray1 a)) (Seq.lseq t (length a)));
  let a0 : Seq.seq (ref t) = a in
  Seq.cons_head_tail a0;
  let r = Seq.head a0 in
  let q = Seq.tail a0 in
  Seq.head_cons r q;
  Seq.lemma_tl r q;
  change_equal_slprop
    (varray1 a)
    (vrewrite (vptr (r) `star` varray1 (q)) (vcons_rewrite (Seq.length (q)) (r) (varray1 (q)) ()));
  elim_vrewrite (vptr (r) `star` varray1 (q)) (vcons_rewrite (Seq.length (q)) (r) (varray1 (q)) ()) (vcons_rewrite_recip (Seq.length (q)) (r) (varray1 (q)) ());
  reveal_star (vptr (r)) (varray1 (q));
  let m = get #(vptr (r) `star` varray1 (q)) () in
  Seq.head_cons (m (vptr (r))) (coerce (m (varray1 (q))) (Seq.lseq t (length (q))));
  Seq.lemma_tl (m (vptr (r))) (coerce (m (varray1 (q))) (Seq.lseq t (length (q))));
  let res : (ref t & array t) = (r, q) in
  change_equal_slprop
    (vptr (r) `star` varray1 (q))
    (vptr (fst res) `star` varray1 (snd res));
  reveal_star (vptr (fst res)) (varray1 (snd res));
  res

#pop-options

(* FIXME: refine the model with nontrivial boundaries. To do that, I will need fractional permissions. *)

let boundary = unit
let lhs #_ _ = ()
let rhs #_ _ = ()
let freeable_boundaries _ _ = true

let join #t al ar = sladmit ()

let split #t a i = sladmit ()

let alloc x n = sladmit ()
(*
  let s = Seq.create (U32.v n) x in
  alloc s
*)

let index r i = sladmit ()
(*
  let s = read r in
  Seq.index s (U32.v i)
*)

let upd r i x = sladmit ()
(*
  let s = read r in
  let s' = Seq.upd s (U32.v i) x in
  write r s'
*)

let free #t r =
  reveal_vemp ();
  let res : Ghost.erased (t_of vemp) = Ghost.hide (coerce () (t_of vemp)) in
  change_slprop_2
    (varray r)
    (vemp)
    res
    (fun m -> intro_emp m)
