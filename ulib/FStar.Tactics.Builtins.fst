(**
Every tactic primitive, i.e., those built into the compiler
@summary Tactic primitives
*)
module FStar.Tactics.Builtins

open FStar.Tactics.Effect
open FStar.Reflection.Types
open FStar.Tactics.Types

assume private val __fail : a:Type -> string -> __tac a
let fail (#a:Type) (msg:string) : Tac a = TAC?.reflect (__fail a msg)

assume private val __top_env     : __tac env
(** [top_env] returns the environment where the tactic started running.
 * This works even if no goals are present. *)
let top_env () = TAC?.reflect __top_env

assume private val __cur_env     : __tac env
(** [cur_env] returns the current goal's environment *)
let cur_env () = TAC?.reflect __cur_env

(** [push_binder] extends the environment with a single binder.
    This is useful as one traverses the syntax of a term,
    pushing binders as one traverses a binder in a lambda,
    match, etc. Note, the environment here is disconnected to
    (though perhaps derived from) the environment in the proofstate *)
assume val push_binder : env -> binder -> env

assume private val __cur_goal    : __tac term
(** [cur_goal] returns the current goal's type *)
let cur_goal () = TAC?.reflect __cur_goal

assume private val __cur_witness : __tac term
(** [cur_witness] returns the current goal's witness *)
let cur_witness () = TAC?.reflect __cur_witness

assume private val __is_guard   : __tac bool
(** [is_guard] returns whether the current goal arised from a typechecking guard *)
let is_guard () = TAC?.reflect __is_guard

assume private val __refine_intro : __tac unit
(** [refine_intro] will turn a goal of shape [w : x:t{phi}]
into [w : t] and [phi{w/x}] *)
let refine_intro () = TAC?.reflect __refine_intro

assume private val __tc : term -> __tac term
(** [tc] returns the type of a term in the current environment,
or fails if it is untypeable. *)
let tc (t : term) = TAC?.reflect (__tc t)

assume private val __unshelve : term -> __tac unit
(** [unshelve] creates a goal from a term for its given type.
It can be used when the system decided not to present a goal, but
you want one anyway. For example, if you request a uvar through
[uvar_env] or [fresh_uvar], you might want to instantiate it
explicitly. *)
let unshelve (t : term) = TAC?.reflect (__unshelve t)

assume private val __unquote : #a:Type -> term -> __tac a
(** [unquote t] with turn a quoted term [t] into an actual value, of
any type. This will fail at tactic runtime if the quoted term does not
typecheck to type [a]. *)
let unquote (#a:Type) (t:term) : Tac a = TAC?.reflect (__unquote #a t)

assume private val __trytac : #a:Type -> __tac a -> __tac (option a)
(** [trytac t] will attempt to run [t] and allow to recover from a failure.
If [t] succeeds with return value [a], [trytac t] returns [Some a].
On failure, it returns [None]. See also [or_else].
*)
let trytac (t : unit -> Tac 'a) = TAC?.reflect (__trytac (reify (t ())))

assume private val __trivial  : __tac unit
(** [trivial] will discharge the goal if it's exactly [True] after
doing normalization and simplification of it. *)
let trivial () : Tac unit = TAC?.reflect __trivial

assume private val __norm  : list norm_step -> __tac unit
(** [norm steps] will call the normalizer on the current goal's
type and witness, with its reduction behaviour parameterized
by the flags in [steps].
Currently, the flags (provided in Prims) are
[simpl] (do logical simplifications)
[whnf] (only reduce until weak head-normal-form)
[primops] (performing primitive reductions, such as arithmetic and
string operations)
[delta] (unfold names)
[zeta] (inline let bindings)
[iota] (reduce match statements over constructors)
[delta_only] (restrict delta to only unfold this list of fully-qualfied identifiers)
*)
let norm steps : Tac unit = TAC?.reflect (__norm steps)

assume private val __norm_term_env  : env -> list norm_step -> term -> __tac term
(** [norm_term_env e steps t] will call the normalizer on the term [t]
using the list of steps [steps], over environment [e]. The list has the same meaning as for [norm]. *)
let norm_term_env env steps t : Tac term = TAC?.reflect (__norm_term_env env steps t)

assume private val __norm_binder_type  : list norm_step -> binder -> __tac unit
(** [norm_binder_type steps b] will call the normalizer on the type of the [b]
binder for the current goal. Notably, this cannot be done via binder_retype and norm,
because of uvars being resolved to lambda-abstractions. *)
let norm_binder_type steps b : Tac unit = TAC?.reflect (__norm_binder_type steps b)

assume private val __intro  : __tac binder
(** [intro] pushes the first argument of an arrow goal into the
environment, turning [Gamma |- ?u : x:a -> b] into [Gamma, x:a |- ?u' : b].
Note that this does not work for logical implications/forall. See
FStar.Tactics.Logic for that.
*)
let intro () : Tac binder = TAC?.reflect __intro

assume private val __intro_rec  : __tac (binder * binder)
(** Similar to intros, but allows to build a recursive function.
Currently broken (c.f. issue #1103)
*)
let intro_rec () : Tac (binder * binder) = TAC?.reflect __intro_rec

assume private val __rename_to  : binder -> string -> __tac unit
(** [rename_to b nm] will rename the binder [b] to [nm] in
the environment, goal, and witness in a safe manner. The only use of this
is to make goals and terms more user readable. *)
let rename_to bv s : Tac unit = TAC?.reflect (__rename_to bv s)

assume private val __revert  : __tac unit
(** [revert] pushes out a binder from the environment into the goal type,
so a behaviour opposite to [intros].
*)
let revert () : Tac unit = TAC?.reflect __revert

assume private val __binder_retype  : binder -> __tac unit
(** [binder_retype] changes the type of a binder in the context. After calling it
with a binder of type `t`, the user is presented with a goal of the form `t == ?u`
to be filled. The original goal (following that one) has the type of `b` in the
context replaced by `?u`.
*)
let binder_retype (b : binder) : Tac unit = TAC?.reflect (__binder_retype b)

assume private val __clear_top : __tac unit
(** [clear_top] will drop the outermost binder from the environment.
Can only be used if the goal does not at all depend on it.
*)
let clear_top () : Tac unit = TAC?.reflect __clear_top

assume private val __clear : binder -> __tac unit
(** [clear] will drop the given binder from the context, is
nothing depends on it.
*)
let clear (b : binder) : Tac unit = TAC?.reflect (__clear b)

assume private val __rewrite : binder -> __tac unit
(** If [b] is a binder of type [v == r], [rewrite b] will rewrite
the variable [v] for [r] everywhere in the current goal type and witness/
*)
let rewrite (b:binder) : Tac unit = TAC?.reflect (__rewrite b)

assume private val __smt     : __tac unit
(** [smt] will mark the current goal for being solved through the SMT.
This does not immediately run the SMT:  it is a marker.
This tactic never fails, and a goal marked for SMT cannot be brought back. *)
let smt () : Tac unit = TAC?.reflect __smt

assume private val __divide: int -> __tac 'a -> __tac 'b -> __tac ('a * 'b)
(** [divide n t1 t2] will split the current set of goals into the [n]
first ones, and the rest. It then runs [t1] on the first set, and [t2]
on the second, returning both results (and concatenating remaining goals). *)
let divide (n:int) (f:unit -> Tac 'a) (g:unit -> Tac 'b): Tac ('a * 'b) =
    TAC?.reflect (__divide n (reify (f ())) (reify (g ())))

(* could be implemented using divide *)
assume private val __seq : __tac unit -> __tac unit -> __tac unit
(** Runs tactic [t1] on the current goal, and then tactic [t2] on *each*
subgoal produced by [t1]. Each invocation of [t2] runs on a proofstate
with a single goal (they're "focused"). *)
let seq (f:unit -> Tac unit) (g:unit -> Tac unit) : Tac unit =
  TAC?.reflect (__seq (reify (f ())) (reify (g ())))

(** boolean is whether to set the expected type internally.
 * Just use `exact` from FStar.Tactics.Derived if you don't know what that means. *)
assume private val __t_exact : bool -> term -> __tac unit
let t_exact hard (t:term) : Tac unit = TAC?.reflect (__t_exact hard t)

assume private val __apply : term -> __tac unit
(** [apply f] will attempt to produce a solution to the goal by an application
of [f] to any amount of arguments (which need to be solved as further goals).
The amount of arguments introduced is the least such that [f a_i] unifies
with the goal's type. *)
let apply (t:term) : Tac unit = TAC?.reflect (__apply t)

assume private val __apply_raw : term -> __tac unit
(** [apply_raw f] is like [apply], but will ask for all arguments regardless
of whether they appear free in further goals. *)
let apply_raw (t:term) : Tac unit = TAC?.reflect (__apply_raw t)

assume private val __apply_lemma : term -> __tac unit
(** [apply_lemma l] will solve a goal of type [squash phi] when [l] is a Lemma
ensuring [phi]. The arguments to [l] and its requires clause are introduced as new goals.
As a small optimization, [unit] arguments are discharged by the engine. *)
// TODO: do the unit thing too for [apply].
let apply_lemma (t:term) : Tac unit = TAC?.reflect (__apply_lemma t)

assume private val __print : string -> __tac unit
(** [print str] has no effect on the proofstate, but will have the side effect
of printing [str] on the compiler's standard output. *)
let print (msg:string) : Tac unit = TAC?.reflect (__print msg)

assume private val __dump : string -> __tac unit
(** Similar to [print], but will dump a text representation of the proofstate
along with the message. *)
let dump (msg:string) : Tac unit = TAC?.reflect (__dump msg)

assume private val __dump1 : string -> __tac unit
(** Similar to [dump], but only dumping the current goal. *)
let dump1 (msg:string) : Tac unit = TAC?.reflect (__dump1 msg)

assume private val __trefl : __tac unit
(** Solves a goal [Gamma |= squash (l == r)] by attempting to unify
[l] with [r]. This currently only exists because of some universe problems
when trying to [apply] a reflexivity lemma. *)
let trefl () : Tac unit = TAC?.reflect __trefl

assume private val __pointwise : direction -> __tac unit -> __tac unit
(** (TODO: explain bettter) When running [pointwise tau] For every
subterm [t'] of the goal's type [t], the engine will build a goal [Gamma
|= t' == ?u] and run [tau] on it. When the tactic proves the goal,
the engine will rewrite [t'] for [?u] in the original goal type. This
is done for every subterm, bottom-up. This allows to recurse over an
unknown goal type. By inspecting the goal, the [tau] can then decide
what to do (to not do anything, use [trefl]). *)
let pointwise  (tau : unit -> Tac unit) : Tac unit = TAC?.reflect (__pointwise BottomUp (reify (tau ())))
let pointwise' (tau : unit -> Tac unit) : Tac unit = TAC?.reflect (__pointwise TopDown  (reify (tau ())))

assume private val __topdown_rewrite : (term -> __tac (bool * int)) -> __tac unit -> __tac unit

(** [topdown_rewrite ctrl rw] is used to rewrite those sub-terms [t]
    of the goal on which [fst (ctrl t)] returns true.

    On each such sub-term, [rw] is presented with an equality of goal
    of the form [Gamma |= t == ?u]. When [rw] proves the goal,
    the engine will rewrite [t] for [?u] in the original goal
    type.
    
    The goal formula is traversed top-down and the traversal can be
    controlled by [snd (ctrl t)]:
    
    When [snd (ctrl t) = 0], the traversal continues down through the
    position in the goal term.
    
    When [snd (ctrl t) = 1], the traversal continues to the next
    sub-tree of the goal.

    When [snd (ctrl t) = 2], no more rewrites are performed in the
    goal.
*)
let topdown_rewrite
       (ctrl : term -> Tac (bool * int))
       (rw:unit -> Tac unit)
    : Tac unit
    = TAC?.reflect (__topdown_rewrite (fun x -> reify (ctrl x)) (reify (rw ())))

assume private val __later : __tac unit
(** Push the current goal to the back. *)
let later () : Tac unit = TAC?.reflect __later

assume private val __dup : __tac unit
(** Given the current goal [Gamma |- w : t],
[dup] will turn this goal into
[Gamma |- ?u : t] and
[Gamma |= ?u == w]. It can thus be used to change
a goal's witness in any way needed, by choosing
some [?u] (possibly with exact) and then solving the other goal.
*)
let dup () : Tac unit = TAC?.reflect __dup

assume private val __flip : __tac unit
(** Flip the order of the first two goals. *)
let flip () : Tac unit = TAC?.reflect __flip

assume private val __qed : __tac unit
(** Succeed if there are no more goals left, and fail otherwise. *)
let qed () : Tac unit = TAC?.reflect __qed

// Proof namespace management
assume private val __prune : string -> __tac unit
(** [prune "A.B.C"] will mark all top-level definitions in module
[A.B.C] (and submodules of it) to not be encoded to the SMT, for the current goal.
The string is a namespace prefix. [prune ""] will prune everything, but note
that [prune "FStar.S"] will not prune ["FStar.Set"]. *)
let prune ns : Tac unit = TAC?.reflect (__prune ns)

assume private val __addns : string -> __tac unit
(** The opposite operation of [prune]. The latest one takes precedence. *)
let addns ns : Tac unit = TAC?.reflect (__addns ns)

assume private val __cases : term -> __tac (term * term)
(** Given a disjunction [e], destruct it and generate two goals
for each case. Return value is terms representing proofs for each case.
The first one is only valid in the first goal, and likewise for
the second (TODO: change this awful behaviour).
*)
let cases t : Tac (term * term) = TAC?.reflect (__cases t)

assume private val __set_options : string -> __tac unit
(** Set command line options for the current goal. Mostly useful to
change SMT encoding options such as [set_options "--z3rlimit 20"]. *)
let set_options s : Tac unit = TAC?.reflect (__set_options s)

assume private val __uvar_env : env -> option typ -> __tac term
(** Creates a new, unconstrained unification variable in environment
[env]. The type of the uvar can optionally be provided in [o]. If not
provided, a second uvar is created for the type. *)
let uvar_env (e : env) (o : option typ) : Tac term = TAC?.reflect (__uvar_env e o)

assume private val __unify : term -> term -> __tac bool
(** Call the unifier on two terms. The return value is whether
unification was possible. When the tactics returns true, the terms may
have been instantited by unification. When false, there is no effect. *)
let unify (t1 t2 : term) : Tac bool = TAC?.reflect(__unify t1 t2)

assume private val __launch_process : string -> string -> string -> __tac string
(** Launches an external process [prog] with arguments [args] and input
[input] and returns the output. For security reasons, this can only be
performed when the `--unsafe_tactic_exec` options was provided for the
current F* invocation. The tactic will fail if this is not so. *)
let launch_process (prog args input : string) : Tac string = TAC?.reflect (__launch_process prog args input)

(** Get a fresh bv of some name and type. The name is only useful
for pretty-printing, since there is a fresh unaccessible integer within
the bv too. *)
assume val __fresh_bv_named : string -> typ -> __tac bv
let fresh_bv_named nm t : Tac bv = TAC?.reflect (__fresh_bv_named nm t)

(** Change the goal to another type, given that it is convertible
 * to the current type. *)
assume val __change : typ -> __tac unit
let change (t : typ) : Tac unit = TAC?.reflect (__change t)

assume val __get_guard_policy : __tac guard_policy
let get_guard_policy () : Tac guard_policy = TAC?.reflect (__get_guard_policy)

assume val __set_guard_policy : guard_policy -> __tac unit
let set_guard_policy (p : guard_policy) : Tac unit = TAC?.reflect (__set_guard_policy p)

assume val __dismiss : __tac unit
let dismiss () : Tac unit = TAC?.reflect __dismiss
