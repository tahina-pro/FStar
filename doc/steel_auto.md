tl;dr: this PR solves the following two issues for `Steel.ST`:
* it removes the need for `intro_exists` or `intro_pure` when calling a function whose pre-resource has `exists_` or `pure`, or at the end of the body of a function whose post-resource has `exists_` or `pure`
* at the beginning of the body of a function whose pre-resource has `exists_` or `pure`, or after returning from a function whose post-resource has `exists_` or `pure`, the user can destruct all of them with a single eliminator, `gen_elim ()`, instead of repeatedly calling `elim_exists` or `elim_pure`.

While I could have submitted two distinct PRs for those two features, I claim that both together support a single unified programming style for Steel.ST, and I'd also like to review potential interactions between the two features.

Beyond introduction and elimination of intro/exists, I claim that my detailed description below can serve as a blueprint for generic automation improvements integrated with Steel's framing tactic: how to schedule and solve goals more generic than `can_be_split` or equalities, and how to automatically generate pre- and post-resources for more generic purposes than just frame inference.

# Automatic introduction for `exists_`, `pure_`
<details>
    <summary>Click to expand</summary>

## Example
Consider the following example:
```
open Steel.ST.Util
assume val ptr: Type0
assume val pts_to: ptr -> nat -> vprop
assume val free (p:ptr) : STT unit (exists_ (fun v -> pts_to p v)) (fun _ -> emp)

let free_one_default (p q r:ptr)
  : STT unit
    (pts_to p 17 `star` pts_to q 18 `star` pts_to r 19)
    (fun _ -> pts_to p 17 `star` pts_to r 19)
 = intro_exists _ (fun v -> pts_to q v);
   let _ = free q in ()
```
With this PR, the call to `intro_exists` is no longer needed, so the following code works:
```
let free_one (p q r:ptr)
  : STT unit
    (pts_to p 17 `star` pts_to q 18 `star` pts_to r 19)
    (fun _ -> pts_to p 17 `star` pts_to r 19)
 = let _ = free q in ()
```
## How it works

### Automatic invocation of introduction lemmas
I modified Steel's framing tactic so that, when it produces a goal of the form `can_be_split p (exists_ q)`, where `p` and `q _` are vprops, the tactic automatically calls an introduction lemma to turn the goal into `can_be_split p (q ?x)`, where `?x` is a data uvar, namely a witness to be unified with some instance of `q ?x` in `p`. I did the same for `can_be_split_forall_dep`.

Similarly, if Steel's framing tactic produces a goal of the form `can_be_split p (pure s)`, where `p` is a vprop and `s` is a prop, then I make the tactic automatically call an introduction lemma to turn the goal into `s`. For `can_be_split_forall_dep`, I take advantage of the _abduction variable_ mechanism: I solve `can_be_split_forall_dep ?a p (fun x -> pure (s x))` by instantiating the abduction variable `?a` with `s`, meaning that this goal transformation is valid only if `s` holds (thanks @nikswamy for the trick; more detailed notes by Nik at the beginning of https://github.com/FStarLang/FStar/blob/taramana_steel_auto/tests/micro-benchmarks/SteelIntroExists.fst )

### Generic : call a lemma on a can-be-split right-hand-side pattern
In both cases, my modified framing tactic, for any `can_be_split` (or `can_be_split_forall_dep`) goal with at most one vprop uvar and that couldn't be solved yet:
1. reads the head symbol of the right-hand-side, say `hs`
2. collect all lemmas associated to `hs`. By "associated", I mean those tagged with the `solve_can_be_split_for hs` (or `solve_can_be_split_forall_dep_for hs`) attribute. However, since F* does not directly support retrieving global definitions from attributes more complex than global variables, such lemmas must be tagged with `solve_can_be_split_lookup` (or `solve_can_be_split_forall_dep_lookup`) first. So the tactic first collect all of them, and among them, filters those having the right more complex attribute.
3. calls each such lemma in turn, until one works.

Thus, I accordingly tagged lemmas for `exists_` and `pure`. See 9e3256ab6c2f8697c995e3f6027a7f7298f20bb8 for more details.

</details>

# Generic elimination of `exists_` and `pure`
<details>
    <summary>Click to expand</summary>

## Example
Consider the following example:
```
open Steel.ST.Util
assume val pred ([@@@smt_fallback] n: nat) : vprop
assume val pred' ([@@@smt_fallback] n: nat) : vprop
let g ()
: STT bool (exists_ (fun n -> exists_ (fun p -> pred n `star` pred' p `star` pure (n == 18 /\ p == 42))))
   (fun _ -> pred 18 `star` pred' 42)
= let _ = elim_exists () in
  let _ = elim_exists () in
  elim_pure _;
  return true
```

With this PR, the calls to `elim_exists` and `elim_pure` can be collapsed into one single eliminator:
```
let g  ()
: STT bool (exists_ (fun n -> exists_ (fun p -> pred n `star` pred' p `star` pure (n == 18 /\ p == 42))))
   (fun _ -> pred 18 `star` pred' 42)
= let _ = gen_elim () in
  return true
```
I claim that this style is most useful for code ported from selector-style Steel to Steel.ST where the code does not need to explicitly refer to the binders obtained by opening existentials (such existentials would correspond to the actual values returned by selectors.)

However, in cases where a binder is still needed, I claim that `gen_elim` gives rise to a more robust proof style, where the binder only depends on a pattern on the resources present in the context, rather than on the original nesting order of  `exists_`. Indeed, consider the following example:
```
let g1 ()
: STT (Ghost.erased nat) (exists_ (fun n -> exists_ (fun p -> pred n `star` pred' p `star` pure (n == 18))))
  (fun p -> pred 18 `star` pred' (Ghost.reveal p))
= let _ = elim_exists () in
  let p = elim_exists () in
  elim_pure _;
  return p
```
That code is not robust in the sense that the user has to remember the position of the `exists_` corresponding to `p` in the nesting. I claim that the following code is more robust, relying on a pattern against the current context:
```
let g2 ()
: STT (Ghost.erased nat) (exists_ (fun n -> exists_ (fun p -> pred n `star` pred' p `star` pure (n == 18))))
  (fun p -> pred 18 `star` pred' (Ghost.reveal p))
= let _ = gen_elim () in
  let p = vpattern_replace_erased (fun p -> pred' p) in
  return p
```
While this code might seemingly require more boilerplate from the user, any additional arguments to `pred'` (if any) in the pattern can actually be replaced with `_`, left for the framing tactic to solve.

## How it works

I wrote a single generic eliminator, `gen_elim`, such that, if `p` is the whole current resource, then `gen_elim ()` returns a tuple containing all the values obtained by eliminating all `exists_` in `p`, and the whole new resource is `p` with all existentials opened; moreover, after `gen_elim`, all pure vprops in `p` hold.

### Step 1: a tactic to produce eliminator calls

<details>
    <summary>Click to expand</summary>

I first implemented `gen_elim ()` as follows (neglecting the invariants; see tahina-pro/FStar@e8dc3e1259e395b22ebbcbd65e8f0e1ce966939d for more details):
```
val gen_elim
  (#p: vprop)
  (#[ solve_gen_elim () ] i: gen_elim_t p)
  (_: unit)
: STGhost (Ghost.erased (gen_elim_a i)) p (gen_elim_q i) True (gen_elim_post i)
```
where `i: gen_elim_t p` is basically a dependent tuple containing the return type of the eliminator (`gen_elim_a i`) and the post-resource (`gen_elim_q i`) and the postcondition (`gen_elim_post i`) after opening all `exists_` and `pure` from `p`. `i` is to be computed by a tactic (`solve_gen_elim p`) pattern-matching on the shape of `p` to produce the corresponding calls to elementary eliminators.

I wrote the tactic with some optimizations to avoid producing useless `unit`s (e.g. if the body of an `exists_` has no `exists_`) and to produce dependent pairs only for nested `exists_` (so that I just produce a non-dependent pair for two eliminators linked only by `star`.)

However, this initial design choked on two issues:
* I had to properly normalize the type, post-resource and postcondition
* @nikswamy and @aseemr noticed that I was relying on meta-arguments solved by tactics, which interacted with Steel's framing tactic in an unpredicable way.

While I tried to solve those two issues all at once, I'm going to describe the two parts of my solution separately below, conceptually.

</details>

### Step 2: normalizing the post-resource and the postcondition

<details>
    <summary>Click to expand</summary>

To solve the former issue, instead of building such an intermediate object, I chose to hide it under an existential predicate, `gen_elim_prop`, predicate basically asserting that there exists an intermediate `gen_elim_t` dependent tuple (see above) such that `a`, `q` and `post`  are its normalized components. So, I wrote a tactic, `solve_gen_elim_prop`, to infer `a`, `q`, `post` with `solve_gen_elim` and prove `gen_elim_prop` at the same time:

```
val gen_elim
  (#p: vprop)
  (#a: Type)
  (#q: Ghost.erased a -> vprop)
  (#post -> vprop)
  (#[ solve_gen_elim_prop () ] prf: squash (gen_elim_prop p a q post))
  (_: unit)
: STGhost (Ghost.erased a) p q True post
```

However, when using that version of `gen_elim`, I stumbled upon SMT issues because the proof of `gen_elim_prop` generated by the tactic was kept as is and retypechecked by F* (and, worse, when I used `apply_lemma` to call the introduction lemma for `gen_elim_prop`, F* replaced that lemma call with `()` , which of course made the goal fail.) So, upon advice by @nikswamy and @aseemr, I split the solving process into two parts (see tahina-pro/FStar@b2a9bf6a10e4473904dfe4c98949602327b0e5c4 for more details):

```
val gen_elim
  (#p: vprop)
  (#a: Type)
  (#q: Ghost.erased a -> vprop)
  (#post -> vprop)
  (#[ solve_gen_elim () ] dummy: squash (gen_elim_prop_placeholder p a q post))
  (_: unit)
: STGhost (Ghost.erased a) p q (with_tactic solve_gen_elim_prop (squash (gen_elim_prop p a q post))) post
```

where the `gen_elim_prop_placeholder` predicate is just defined as `True`, and is solved by basically just calling the `solve_gen_elim` tactic in Phase 1 of F\*'s two-phase type checking to infer `a`, `q` and `post`. The actual proof for `gen_elim_prop_placeholder` kept by F* after running the tactic, was just `()`, so retypechecking the proof by SMT would no longer fail. On the other hand, the actual proof of `gen_elim_prop` is done in Phase 2 once all arguments are solved.

Relying on these two phases made it more critical to integrate `solve_gen_elim` into the framing tactic to avoid spurious interactions between the tactic for solving the arguments to `gen_elim_prop_placeholder` and the framing tactic.

</details>

### Step 3: integrating with the framing tactic

<details>
    <summary>Click to expand</summary>

Meta-implicits expected to be inferred by Steel's framing tactics are tagged with the `framing_implicit` attribute:  F* collects all such arguments and produces a set of goals to be solved all at once by the `init_resolve_tac` tactic, by virtue of that tactic being tagged with the `[@@ resolve_implicits; framing_implicit]` attributes. To avoid unpredictable interaction between Steel's framing tactic and `solve_gen_elim`, I managed to integrate the latter in the former and have implicit arguments to `gen_elim` be inferred by the framing tactic instead:

```
val gen_elim
  (#p: vprop)
  (#[@@@framing_implicit] a: Type)
  (#[@@@framing_implicit] q: Ghost.erased a -> vprop)
  (#[@@@framing_implicit] post -> vprop)
  (#[@@@framing_implicit] dummy: squash (gen_elim_prop_placeholder p a q post))
  (_: unit)
: STGhost (Ghost.erased a) p q (with_tactic solve_gen_elim_prop (squash (gen_elim_prop p a q post))) post
```

To this end, I sought to mimic the "lemma-by-attribute" approach I already applied above for automatic introduction lemmas, and to use that approach to select tactics instead of lemmas: if the framing tactic encounters a goal that is neither a `can_be_split` variant nor an equality, then I make it look at its head symbol, and gather all tactics tagged with an attribute matching that head symbol, and repeatedly trying each such tactic candidate until one makes progress. For the latter part, I used a trick by @mtzguido to call tactics with `unquote`. See tahina-pro/FStar@1360ed6791dac7fac2f195e535b4e709cd1f535e for more details.

Alas, Guido's trick does not work with native tactics, since they do not support `unquote`. So, I finally ended up with a more "pedestrian" solution, replacing the tactic-by-attribute approach with an explicit tactic dictionary (see 52134b9d85e02bd779609260f96eb8cf7abad032 for more details.) This approach leads to the framing tactic being instantiated twice separately, once in `Steel.Effect` with an empty dictionary, and once in `Steel.ST.Util` with a dictionary including the tactics for `gen_elim`. So, if `Steel.Effect` and `Steel.ST.Util` are both present in the context, then there will be two tactics associated with the `framing_implicit` attributes, so I don't know how F* should handle this potential "conflict".

In both cases, now since the framing tactic can deal with more goals than just `can_be_split` variants or equalities, I had to clarify the goal scheduling tactics so that they do not rely on the previous shape of a goal if it has changed since (see 2187aced0bb29c7726ec696d104bdc264594bfd6 for more details.)

</details>

### Step 4: ensuring that vprops are unified in the right order

<details>
    <summary>Click to expand</summary>

Consider the following example, where I have, say, an array but want to split it into two parts and run an operation on its right-hand-side part only and join the two parts back again:

```
assume val ptr : Type0
assume val pts_to (p: ptr) (v: Ghost.erased nat) : vprop
assume val split (#v: Ghost.erased nat) (p: ptr)
    : STT ptr (pts_to p v)
        (fun res -> exists_ (fun vl -> pts_to p vl `star` exists_ (fun vr -> pts_to res vr)))
assume val join (#opened: _) (#pl #pr: Ghost.erased nat) (al ar: ptr)
    : STGhostT (Ghost.erased nat) opened (pts_to al pl `star` pts_to ar pr)
        (fun res -> pts_to al res)
assume val v1 (#p: Ghost.erased nat) (a: ptr) (err: ptr)
    : STT unit (pts_to a p `star` pts_to err 0)
        (fun _ -> pts_to a p `star` exists_ (fun v -> pts_to err v))

let v2 (#p: Ghost.erased nat) (al: ptr) (err: ptr) : STT unit
  (pts_to al p `star` pts_to err 0)
  (fun _ -> exists_ (fun p -> pts_to al p `star` exists_ (fun v -> pts_to err v)))
= let ar = split al in
  let _ = gen_elim () in
  let _ = v1 ar err in
  let _ = gen_elim () in
  let _ = join al ar in
  return ()
```

With `gen_elim` as described so far, the framing tactic wrongly unified the pre-resource for `join` with the expected post-resource for the second call to `gen_elim`, which would conflict with the one that would be computed by the tactic for `gen_elim`:

```
Goal 1/1 (Instantiating meta argument in application)
p: Ghost.erased nat
al err ar: ptr
uu___: Ghost.erased (x: Ghost.erased nat & (Ghost.erased nat <: Prims.Tot Type0))
uu___'0: unit
--------------------------------------------------------------------------------
squash (gen_elim_prop_placeholder (VStar (pts_to1 al (dfstp (Ghost.reveal _)))
          (VStar (exists_ (fun v -> pts_to1 err v)) (pts_to1 ar (dsndp (Ghost.reveal _)))))
      (*?u8765*)
      _
      (fun x ->
          star (star (pts_to1 al ((*?u8818*) _ x)) (pts_to1 ar ((*?u8817*) _ x)))
            (exists_ (fun v -> pts_to1 err v)))
      (*?u552*)
      _)
(*?u50*) _
```

A candidate for the post-resource for `gen_elim` already appears to have been inferred by the framing tactic even before the tactic for `gen_elim` has started running.

To solve this issue, upon advice from @nikswamy, I marked the post-resource of `gen_elim` with an identity function, `guard_vprop`, and I modified the framing tactic to systematically delay any goal where `guard_vprop` has any unsolved vprop uvar (even if that vprop uvar is the only one), so that the post-resource of `gen_elim` is first fully computed by the `gen_elim`-specific tactics before the framing tactic has any opportunity to unify it with any vprops arising afterwards (see bf48d2b14703fba972bcfdd583c1783b6e884f74 for more details.)

</details>

</details>

# Lessons learned
While this PR is already working as it is now, I implemented it using many workarounds (as I described above), from which I learned lessons which hopefully should lead to the following F\* improvements:

* Should `lookup_attr` support more than just fvar attributes?
* Should native tactics support `unquote`?
* Should we clarify the potential interactions between F*'s various tactic hooks:
  + meta-implicits marked to solve with a tactic as opposed to an attribute and `resolve_implicits`
  + what if several tactics are associated to the same attribute with `resolve_implicits`?
  + what if a function uses meta-implicits marked with different attributes at once?

Thank you Nik, Aseem, Guido and @R1kM for your critical help and feedback!
