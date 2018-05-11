#light "off"
module FStar.Tactics.Types

open FStar.All
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
module Options = FStar.Options
module SS = FStar.Syntax.Subst
module N = FStar.TypeChecker.Normalize
module Range = FStar.Range

(*
   f: x:int -> P
   ==================
      P
 *)
//A goal is typically of the form
//    G |- ?u : t
// where context = G
//       witness = ?u, although, more generally, witness is a partial solution and can be any term
//       goal_ty = t
type goal = {
    goal_main_env : env;
    goal_ctx_uvar : ctx_uvar;
    opts    : FStar.Options.optionstate; // option state for this particular goal
    is_guard : bool; // Marks whether this goal arised from a guard during tactic runtime
                     // We make the distinction to be more user-friendly at times
}
let goal_env g = { g.goal_main_env with gamma = g.goal_ctx_uvar.ctx_uvar_gamma }
let goal_witness g =
    FStar.Syntax.Syntax.mk (Tm_uvar (g.goal_ctx_uvar, ([], None))) None Range.dummyRange
let goal_type g = g.goal_ctx_uvar.ctx_uvar_typ
let goal_with_type g t =
    let c = g.goal_ctx_uvar in
    let c' = {c with ctx_uvar_typ = t} in
    { g with goal_ctx_uvar = c' }
let goal_with_env g env =
    let c = g.goal_ctx_uvar in
    let c' = {c with ctx_uvar_gamma = env.gamma} in
    { g with goal_main_env=env; goal_ctx_uvar = c' }

let mk_goal env u o b = {
    goal_main_env=env;
    goal_ctx_uvar=u;
    opts=o;
    is_guard=b
}
let subst_goal subst goal =
    let g = goal.goal_ctx_uvar in
    let ctx_uvar = {
        g with ctx_uvar_gamma=FStar.TypeChecker.Env.rename_gamma subst g.ctx_uvar_gamma;
               ctx_uvar_typ=SS.subst subst g.ctx_uvar_typ
    } in
    { goal with goal_ctx_uvar = ctx_uvar }

type guard_policy =
    | Goal
    | SMT
    | Force
    | Drop // unsound

type proofstate = {
    main_context : env;          //the shared top-level context for all goals
    main_goal    : goal;         //this is read only; it helps keep track of the goal we started working on initially
    all_implicits: implicits ;   //all the implicits currently open, partially resolved (unclear why we really need this)
    goals        : list<goal>;   //all the goals remaining to be solved
    smt_goals    : list<goal>;   //goals that have been deferred to SMT
    depth        : int;          //depth for tracing and debugging
    __dump       : proofstate -> string -> unit; // callback to dump_proofstate, to avoid an annoying ciruluarity

    psc          : N.psc;        //primitive step context where we started execution
    entry_range  : Range.range;  //position of entry, set by the use
    guard_policy : guard_policy; //guard policy: what to do with guards arising during tactic exec
    freshness    : int;          //a simple freshness counter for the fresh tactic
}

let subst_proof_state subst ps =
    if Options.tactic_raw_binders ()
    then ps
    else { ps with main_goal = subst_goal subst ps.main_goal;
                   goals = List.map (subst_goal subst) ps.goals
    }

let decr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth - 1 }

let incr_depth (ps:proofstate) : proofstate =
    { ps with depth = ps.depth + 1 }

let tracepoint ps : unit =
    if Options.tactic_trace () || (ps.depth <= Options.tactic_trace_d ())
    then ps.__dump (subst_proof_state (N.psc_subst ps.psc) ps) "TRACE"
    else ()

let set_ps_psc psc ps = { ps with psc = psc }

let set_proofstate_range ps r =
    { ps with entry_range = Range.set_def_range ps.entry_range (Range.def_range r) }

type direction =
    | TopDown
    | BottomUp
