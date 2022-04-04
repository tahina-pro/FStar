(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Steel.ST.Util
(** This module aggregates several of the core effects and utilities
    associated with the Steel.ST namespace.

    Client modules should typically just [open Steel.ST.Util] and
    that should bring most of what they need in scope.
*)
open FStar.Ghost
open Steel.Memory
open Steel.ST.Effect.Ghost
module U = FStar.Universe
include Steel.FractionalPermission
include Steel.Memory
include Steel.Effect.Common
include Steel.ST.Effect
include Steel.ST.Effect.Atomic
include Steel.ST.Effect.Ghost

module T = FStar.Tactics

/// Weaken a vprop from [p] to [q]
/// of every memory validating [p] also validates [q]
val weaken (#opened:inames)
           (p q:vprop)
           (l:(m:mem) -> Lemma
                           (requires interp (hp_of p) m)
                           (ensures interp (hp_of q) m))
  : STGhostT unit opened p (fun _ -> q)

/// Rewrite [p] to [q] when they are equal
val rewrite (#opened:inames)
            (p q: vprop)
  : STGhost unit opened p (fun _ -> q) (p == q) (fun _ -> True)

/// Rewrite p to q, proving their equivalence using the framing tactic
/// Most places, this rewriting kicks in automatically in the framework,
///   but sometimes it is useful to explicitly rewrite, while farming AC reasoning
///   to the tactic
val rewrite_with_tactic (#opened:_) (p q:vprop)
  : STGhost unit opened
      p
      (fun _ -> q)
      (requires T.with_tactic init_resolve_tac (squash (p `equiv` q)))
      (ensures fun _ -> True)

/// This rewrite is useful when you have equiv predicate in the logical context
/// Internally implemented using `weaken`
val rewrite_equiv (#opened:_) (p q:vprop)
  : STGhost unit opened p (fun _ -> q)
      (requires equiv p q \/ equiv q p)
      (ensures fun _ -> True)

/// A noop operator, occasionally useful for forcing framing of a
/// subsequent computation
val noop (#opened:inames) (_:unit)
  : STGhostT unit opened emp (fun _ -> emp)

/// Asserts the validity of vprop [p] in the current context
val assert_ (#opened_invariants:_)
            (p:vprop)
  : STGhostT unit opened_invariants p (fun _ -> p)

/// Allows assuming [p] for free
/// See also Steel.ST.Effect.Ghost.admit_
[@@warn_on_use "uses an axiom"]
val assume_ (#opened_invariants:_)
            (p:vprop)
  : STGhostT unit opened_invariants emp (fun _ -> p)

/// Drops vprop [p] from the context. Although our separation logic is
/// affine, the frame inference tactic treats it as linear.
/// Leveraging affinity requires a call from the user to this helper,
/// to avoid implicit memory leaks.  This should only be used for pure
/// and ghost vprops
val drop (#opened:inames) (p:vprop) : STGhostT unit opened p (fun _ -> emp)

/// Introduce a pure vprop, when [p] is valid in the context
val intro_pure (#uses:_) (p:prop)
  : STGhost unit uses emp (fun _ -> pure p) p (fun _ -> True)

/// Eliminate a pure vprop, gaining that p is valid in the context
val elim_pure (#uses:_) (p:prop)
  : STGhost unit uses (pure p) (fun _ -> emp) True (fun _ -> p)

/// Extracting a proposition from a [pure p] while retaining [pure p]
let extract_pure (#uses:_) (p:prop)
  : STGhost unit uses (pure p) (fun _ -> pure p) True (fun _ -> p)
  = let _ = elim_pure p in
    intro_pure p

/// Useful lemmas to make the framing tactic automatically handle `pure`
val intro_can_be_split_pure
  (p: prop)
  (sq: squash p)
: Tot (squash (emp `can_be_split` pure p))

val intro_can_be_split_forall_dep_pure
  (#a: Type)
  (p: prop)
: Tot (squash (can_be_split_forall_dep (fun (x: a) -> p) (fun _ -> emp) (fun _ -> pure p)))

/// It's generally good practice to end a computation with a [return].
///
/// It becomes necessary when combining ghost and non-ghost
/// computations, so it is often less surprising to always write it.
///
/// Because of the left-associative structure of F* computations, this
/// is necessary when a computation is atomic and returning a value
/// with an informative type, but the previous computation was ghost.
/// Else, the returned value will be given type SteelGhost, and F*
/// will fail to typecheck the program as it will try to lift a
/// SteelGhost computation with an informative return type
val return (#a:Type u#a)
           (#opened_invariants:inames)
           (#p:a -> vprop)
           (x:a)
  : STAtomicBase a true opened_invariants Unobservable
                 (return_pre (p x)) p
                 True
                 (fun v -> v == x)

/// An existential quantifier for vprop
val exists_ (#a:Type u#a) (p:a -> vprop) : vprop

/// Useful lemmas to make the framing tactic automatically handle `exists_`
val intro_can_be_split_exists (a:Type) (x:a) (p: a -> vprop)
  : Lemma
    (ensures (p x `can_be_split` (exists_ (fun x -> p x))))

val intro_can_be_split_forall_dep_exists (a:Type) (b:Type)
                           (x:a)
                           (p: b -> a -> vprop)
  : Lemma
    (ensures (fun (y:b) -> p y x) `(can_be_split_forall_dep (fun _ -> True))` (fun (y:b) -> exists_ (fun x -> p y x)))

/// Introducing an existential if the predicate [p] currently holds for value [x]
val intro_exists (#a:Type) (#opened_invariants:_) (x:a) (p:a -> vprop)
  : STGhostT unit opened_invariants (p x) (fun _ -> exists_ p)

/// Variant of intro_exists above, when the witness is a ghost value
val intro_exists_erased (#a:Type)
                        (#opened_invariants:_)
                        (x:Ghost.erased a)
                        (p:a -> vprop)
  : STGhostT unit opened_invariants (p x) (fun _ -> exists_ p)

/// Extracting a witness for predicate [p] if it currently holds for some [x]
val elim_exists (#a:Type)
                (#opened_invariants:_)
                (#p:a -> vprop)
                (_:unit)
  : STGhostT (Ghost.erased a) opened_invariants
             (exists_ p)
             (fun x -> p x)

/// Lifting the existentially quantified predicate to a higher universe
val lift_exists (#a:_)
                (#u:_)
                (p:a -> vprop)
  : STGhostT unit u
             (exists_ p)
             (fun _a -> exists_ #(U.raise_t a) (U.lift_dom p))

/// If two predicates [p] and [q] are equivalent, then their existentially quantified versions
/// are equivalent, and we can switch from `h_exists p` to `h_exists q`
val exists_cong (#a:_)
                (#u:_)
                (p:a -> vprop)
                (q:a -> vprop {forall x. equiv (p x) (q x) })
  : STGhostT unit u
             (exists_ p)
             (fun _ -> exists_ q)

/// Creation of a new invariant associated to vprop [p].
/// After execution of this function, [p] is consumed and not available in the context anymore
val new_invariant (#opened_invariants:inames) (p:vprop)
  : STGhostT (inv p) opened_invariants p (fun _ -> emp)

/// Atomically executing function [f] which relies on the predicate [p] stored in invariant [i]
/// as long as it maintains the validity of [p]
/// This requires invariant [i] to not belong to the set of currently opened invariants.
val with_invariant (#a:Type)
                   (#fp:vprop)
                   (#fp':a -> vprop)
                   (#opened_invariants:inames)
                   (#p:vprop)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   ($f:unit -> STAtomicT a (add_inv opened_invariants i)
                                          (p `star` fp)
                                          (fun x -> p `star` fp' x))
  : STAtomicT a opened_invariants fp fp'

/// Variant of the above combinator for ghost computations
val with_invariant_g (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#opened_invariants:inames)
                     (#p:vprop)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     ($f:unit -> STGhostT a (add_inv opened_invariants i)
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : STGhostT a opened_invariants fp fp'

/// A tactic to automatically generate a unique binder

let gen_elim_f
  (p: vprop)
  (a: Type0) // FIXME: generalize this universe
  (q: (a -> vprop))
  (post: (a -> prop))
: Tot Type
= ((opened: inames) -> STGhostF a opened p q True (fun x -> post x))

[@@erasable]
noeq
type gen_elim_t
  (p: vprop)
= | GenElim:
    a: Type0 ->
    q: (a -> vprop) ->
    post: (a -> prop) ->
    f: gen_elim_f p a q post ->
    gen_elim_t p

[@@__reduce__]
let gen_elim_a
  (#p: vprop)
  (g: gen_elim_t p)
: Tot Type0
= match g with
  | GenElim a _ _ _ -> a

[@@__reduce__]
let gen_elim_q
  (#p: vprop)
  (g: gen_elim_t p)
: Tot (gen_elim_a g -> Tot vprop)
= match g with
  | GenElim _ q _ _ -> q

[@@__reduce__]
let gen_elim_post
  (#p: vprop)
  (g: gen_elim_t p)
: Tot (gen_elim_a g -> Tot prop)
= match g with
  | GenElim _ _ post _ -> post

let gen_elim_id'
  (p: vprop)
: Tot (gen_elim_f p unit (fun _ -> p) (fun _ -> True))
= (fun _ -> noop ())

[@__reduce__]
let gen_elim_id
  (p: vprop)
: Tot (gen_elim_t p)
= GenElim
    _
    _
    _
    (gen_elim_id' p)

let gen_elim_exists_simple'
  (a: Type0)
  (p: a -> Tot vprop)
: Tot (gen_elim_f (exists_ p) (Ghost.erased a) (fun x -> p x) (fun _ -> True))
= fun _ -> elim_exists _

[@__reduce__]
let gen_elim_exists_simple
  (a: Type0)
  (p: a -> Tot vprop)
: Tot (gen_elim_t (exists_ p))
= GenElim
    _
    _
    _
    (gen_elim_exists_simple' a p)

[@@erasable]
noeq
type g_dep_pair
  (a: Type)
  (b: (a -> Type))
=
  | GDepPair:
    x: a ->
    y: b x ->
    g_dep_pair a b

let gen_elim_exists'
  (a: Type0)
  (p: a -> Tot vprop)
  (g: (x: a) -> gen_elim_t (p x))
: Tot (gen_elim_f (exists_ p) (g_dep_pair a (fun x -> gen_elim_a (g x))) (fun y -> gen_elim_q (g (GDepPair?.x y)) (GDepPair?.y y)) (fun y -> gen_elim_post (g (GDepPair?.x y)) (GDepPair?.y y)))
= admit ()

[@@__reduce__]
let gen_elim_exists
  (a: Type0)
  (p: a -> Tot vprop)
  (g: (x: a) -> gen_elim_t (p x))
: Tot (gen_elim_t (exists_ p))
= GenElim _ _ _ (gen_elim_exists' a p g)

[@@erasable]
noeq
type g_pair
  (a b: Type)
=
  | GPair:
    fst: a ->
    snd: b ->
    g_pair a b

let gen_elim_star'
  (p q: vprop)
  (gp: gen_elim_t p)
  (gq: gen_elim_t q)
: Tot (gen_elim_f (p `star` q) (gen_elim_a gp `g_pair` gen_elim_a gq) (fun x -> gen_elim_q gp (GPair?.fst x) `star` gen_elim_q gq (GPair?.snd x)) (fun x -> gen_elim_post gp (GPair?.fst x) /\ gen_elim_post gq (GPair?.snd x)))
= admit ()

[@@__reduce__]
let gen_elim_star
  (p q: vprop)
  (gp: gen_elim_t p)
  (gq: gen_elim_t q)
: Tot (gen_elim_t (p `star` q))
= GenElim _ _ _ (gen_elim_star' p q gp gq)

let gen_elim_pure'
  (p: prop)
: Tot (gen_elim_f (pure p) unit (fun _ -> emp) (fun _ -> p))
= admit ()

[@@__reduce__]
let gen_elim_pure
  (p: prop)
: Tot (gen_elim_t (pure p))
= GenElim _ _ _ (gen_elim_pure' p)

let gen_elim'
  (#p: vprop)
  (f: gen_elim_t p)
  (#opened: _)
  ()
: STGhostF (GenElim?.a f) opened p (fun x -> GenElim?.q f x) True (fun x -> GenElim?.post f x)
= GenElim?.f f opened

module T = FStar.Tactics

let rec solve_gen_elim
  ()
: T.Tac unit
= 
  T.focus (fun _ ->
    T.norm [];    
    let g = T.cur_goal () in
    let (hd, tl) = T.collect_app g in
    if not (hd `T.term_eq` (`gen_elim_t))
    then T.fail "solve_gen_elim: not a gen_elim_t goal";
    match tl with
    | [tl', T.Q_Explicit] ->
      let (hd, _) = T.collect_app tl' in
      if hd `T.term_eq` (`pure)
      then T.apply (`gen_elim_pure)
      else if hd `T.term_eq` (`exists_)
      then begin
        T.apply (`gen_elim_exists);
        let _ = T.intro () in
        solve_gen_elim ()
      end
      else if hd `T.term_eq` (`star) || hd `T.term_eq` (`VStar)
      then begin
        T.apply (`gen_elim_star);
        T.iseq [
          solve_gen_elim;
          solve_gen_elim;
        ];
        T.qed ()
      end
      else
        T.apply (`gen_elim_id)
    | _ -> T.fail "ill-formed gen_elim_t"
  )

let gen_elim
  (#p: vprop)
  (#[ solve_gen_elim () ] f: gen_elim_t p)
  (#opened: _)
: Tot (unit ->
      STGhostF (gen_elim_a f) opened p (fun x -> gen_elim_q f x) True (fun x -> gen_elim_post f x))
= let coerce (#tfrom tto: Type) (x: tfrom) (sq: squash (tfrom == tto)) : Tot tto = x
  in
  coerce _ (gen_elim' f #opened) (_ by (T.trefl ()))

let f
  (#opened: _)
  (p q: vprop)
  (x: nat)
: STGhostT bool opened (exists_ (fun n -> p `star` q `star` pure (n > 42 /\ x > 18))) (fun _ -> q)
= noop ();
  let _ = gen_elim () in
  assert (x > 18);
  drop p;
  true
