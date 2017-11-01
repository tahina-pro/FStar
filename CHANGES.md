master
==========

Guidelines for the changelog:
- There should be an entry, however brief, for each user-facing change to F*.
- Entries should include a link to a PR if at all possible, which can provide
  rationale and a detailed technical explanation.
- Each section lists PRs in ascending numerical order, then entries without a PR
  in roughly chronological order.
- Changes that break existing code should explain how to update the code,
  possibly with details in the PR or links to sample fixes (for example, changes
  to F*'s test suite).

## Basic type-checking and inference

* A revision to implicit generalization of types
    (Since [commit FStar@e15c2fa4eb4cd7a10dd74fc5532b6cac8e23b4f1])

  F* has for a while supported implicit generalization of types in
  support of ML-style, let-polymorphism. E.g., `let id x = x` would
  have the implicitly generalized type `#a:Type -> a -> Tot a`.

  However, F* would incorrectly also allow implicitly generalizing
  over variables of types other than `Type`. For example, this program
  would type-check, at a rather counter-intuitive type.

  ```
  type empty (x:False) =
  let rec t (#x:False) (n:nat) : empty x = t #x n
  let f () = t 0
  ```

  where, `f` would be given the type `#x:False -> unit -> empty x`.

  Worse, sometimes F* would generalize over types with free variables,
  leading to crashes as in bug #1091.

  We now restrict implicit generalization to variables whose type is a
  closed refinement of `Type`, e.g.,
    `let id x = x` has the same type as before;
    `let eq = op_Equality` has the type `#a:eqtype -> a -> a -> bool`;
     etc.

  This restriction is a breaking change. For a sampling of the changes
  needed to accommodate it see:

       [commit mitls/hacl-star@c93dd40b89263056c6dec8c606eebd885ba2984e]
       [commit FStar@8529b03e30e8dd77cd181256f0ec3473f8cd68bf]

## Standard library

* [commit FStar@f73f295e](https://github.com/FStarLang/FStar/commit/f73f295ed0661faec205fdf7b76bdd85a2a94a32)

  The specifications for the machine integer libraries (`Int64.fst`,
  `UInt64.fst`, etc) now forbid several forms of undefined behavior in
  C.

  The signed arithmetic `add_underspec`, `sub_underspec`, and `mul_underspec`
  functions have been removed.

  Shifts have a precondition that the shift is less than the bitwidth.

  Existing code may need additional preconditions to verify (for example, see
  a
  [fix to HACL*](https://github.com/mitls/hacl-star/commit/c8a61ab189ce163705f8f9ff51e41cab2869f6d6)).
  Code that relied on undefined behavior is unsafe, but it can be extracted
  using `assume` or
  `admit`.

* Related to the change in implicit generalization of types, is the
  change to the standard libraries for state.

  This program is no longer accepted by F*:

  ```
  module Test
  open FStar.ST
  let f x = !x
  ```

  It fails with:

  ```
  test.fst(4,0-4,12):
        (Error) Failed to resolve implicit argument of type
        'FStar.Preorder.preorder (*?u538*) _'
         in the type of f
         (x:FStar.ST.mref (*?u538*) _ (*?u542*) _ -> FStar.ST.STATE (*?u538*) _)
  ```

  This is because `FStar.ST` is now designed to work with monotonic
  references which are indexed by preorders.

  If you do not intend to use preorders, open `FStar.Ref` instead. The
  program below is accepted.

  ```
  module Test
  open FStar.Ref
  let f x = !x
  ```

## C Extraction

* [PR #1176](https://github.com/FStarLang/FStar/pull/1176)
  `inline_for_extraction` on a type annotation now unfolds it at extraction
  time. This can help to reveal first-order code for C extraction;
  see [FStarLang/kremlin #51](https://github.com/FStarLang/kremlin/issues/51).

## Command line options

* --hint_stats and --check_hints are gone
    b50c88930e3f2655704696902693941525f6cf9f. The former was rarely
    used. The latter may be restored, but the code was too messy to
    retain, given that the feature is also not much used.

* --hint_info and --print_z3_statistics are deprecated. They are
    subsumed by --query_stats.

* --cache_checked_modules: writes out a .checked file from which the
  typechecker can reconstruct its state, instead of re-verifying a
  module every time

* --verify_all, --verify_module, --extract_all, --explicit_deps are
    gone. The behavior of `--dep make` has changed. See the section on
    dependence analysis below.

## Dependence analysis; which files are verified and extracted

* When a file `f` (either an implementation or an interface file)
  refers to a symbol from a module `A`, then `f` depends only on the
  interface of `A` if one exists on the search path. If no interface
  exists for `A` then `f` depends on the implementation of `A`.

* Additionally, an implementation file always depends on its
  interface, if one exists. An interface does not depend on its
  implementation.

* The `--dep full` option:

  Invoking `fstar --dep full f1 ... fn`

     - emits the entire dependence graph D of `f1 ... fn`

     - additionally, for every interface file `a.fsti` in D whose
       implementation `a.fst` is not in D, we also emit the
       dependence graph of `a.fst`.

  This means, for instance, that you can run `fstar --dep full` on all
  the root files of your project and get dependences (in make format)
  for all the files you need to verify in order to be sure that your
  project is fully verified.

* When you invoke `fstar f1 ... fn`, the only files that are verified
  are those that are mentioned on the command line. The dependences of
  those files are computed automatically and are lax-checked.

* Given an invocation of `fstar --codegen OCaml f1 ... fn`, all (and
  only) implementation files in the dependence graph of `f1 ... fn`
  will be extracted.

* The `--expose_interfaces` option:

  In rare cases, we want to verify module `B` against a particular,
  concrete implementation of module `A`, disregarding the abstraction
  imposed by an interface of `A`.

  In such a situation, you can run:
  
     `fstar --expose_interfaces A.fsti A.fst B.fst`

  Note, this explicitly breaks the abstraction of the interface
  `A.fsti`. So use this only if you really know what you're doing.

* We aim to encourage a style in which typical invocations of `fstar`
  take only a single file on the command line. Only that file will be
  verified.

* Only that file will be verified and extracted (if --codegen is
  specified).

* The --cache_checked_modules flag enables incremental, separate
  compilation of F* projects. See examples/sample_project for how this
  is used.

Expected changes in the near future:

* We will make --cache_checked_modules the default so that the cost of
  reloading dependences for each invocation of fstar is mininimized.

* The --extract_namespace and --extract_module flags will be removed.

## Error reporting

* The error reports from SMT query failures have been substantially
  reworked. At least a diagnostic (i.e., an "Info" message) is issued
  for each SMT query failure together with a reason provided by the
  SMT solver. To see that diagnostic message, you at least need to
  have '--debug yes'. Additionally, localized assertion failures will
  be printed as errors. If no localized errors could be recovered
  (e.g., because of a solver timeout) then the dreaded "Unknown
  assertion failed" error is reported.

* --query_stats now reports a reason for a hint failure as well as
  localized errors for sub-proofs that failed to replay. This is
  should provide a faster workflow than using --detail_hint_replay
  (which still exists)

## Miscellaneous

* A file can now contain at most one module or interface

## Tactics

* Let bindings are now part of the reflected syntax (Tv_Let), and can be
  inspected/created in the usual manner.

* New primitive: `launch_process` which runs an external command
  and returns its output. For security reasons, this only works if
  `--unsafe_tactic_exec` is provided (which can only be set externally).

* New primitive: `norm_term` to call the normalizer on a quoted term.

* [commit
  FStar@06948088](https://github.com/FStarLang/FStar/commit/0694808861d2428b2a552e3291c643b2d13b2fcc)
  The tactics normalization interface is now on par with the normalization
  available to the type checker. This included some backwards-incompatible
  changes to how reduction steps are referenced in tactics. See [the changes to
  Normalization.fst](https://github.com/FStarLang/FStar/commit/0694808861d2428b2a552e3291c643b2d13b2fcc#diff-a06134671d813bd28252d8520210edb5)
  for some examples. The biggest breaking change is that `UnfoldOnly` (which
  used to take a `list fv`) has been replaced with `delta_only`, which takes a
  list of fully-qualfied identifiers (eg, `FStar.Map.map`). The other reduction
  steps are nullary and have simply been renamed.

* `clear`, which removed the innermost binder from the context, now takes a binder as
   an argument an will attempt to remove it from any position (given that dependency allows it).
   The old behaviour can be recovered with `clear_top` instead.
