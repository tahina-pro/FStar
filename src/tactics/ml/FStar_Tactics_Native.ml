open FStar_Range
open FStar_Tactics_Types
open FStar_Tactics_Result
open FStar_Tactics_Basic
open FStar_Syntax_Syntax

module N = FStar_TypeChecker_Normalize
module BU = FStar_Util

(* These definitions are ≡ to the ones generated by F*'s extraction of the
   tactic effect.  We need them here to break a circular dependency between the
   compiler and ulib (cf. tactics meeting of 2017-08-03). *)
type 'a __tac = FStar_Tactics_Types.proofstate -> 'a __result

let r = dummyRange

type itac = FStar_TypeChecker_Normalize.psc -> args -> term option
type native_primitive_step =
    { name: FStar_Ident.lid;
      arity: Prims.int;
      strong_reduction_ok: bool;
      tactic: itac}

let compiled_tactics: native_primitive_step list ref = ref []

let list_all () = !compiled_tactics

let is_native_tactic lid =
    BU.is_some (BU.try_find (fun x -> FStar_Ident.lid_equals lid x.name) !compiled_tactics)

let register_plugin (s: string) (arity: Prims.int) (t: itac) =
    let step =
           { N.name=FStar_Ident.lid_of_str s;
             N.arity=arity;
             N.strong_reduction_ok=false;
             N.requires_binder_substitution = false;
             N.interpretation=t}
    in
    FStar_TypeChecker_Normalize.register_plugin step;
    BU.print1 "Registered plugin %s\n" s

let register_tactic (s: string) (arity: Prims.int) (t: itac)=
    let step =
        { name=FStar_Ident.lid_of_str s;
          arity = arity;
          strong_reduction_ok=false;
          tactic=t } in
    compiled_tactics := step :: !compiled_tactics;
    BU.print1 "Registered tactic %s\n" s

let interpret_tactic (ps: proofstate) (t: proofstate -> 'a __result) = t ps

let from_tactic_0 (t: 'b __tac): ('b tac) =
    (fun (ps: proofstate) ->
        BU.print_string "In compiled code (0)\n";
        interpret_tactic ps t) |> mk_tac

let from_tactic_1 (t: 'a -> 'b __tac): ('a -> 'b tac) =
    fun (x: 'a) ->
        (fun (ps: proofstate) ->
            BU.print_string "In compiled code (1)\n";
            interpret_tactic ps (t x)) |> mk_tac

let from_tactic_2 (t: 'a -> 'b -> 'c __tac): ('a -> 'b -> 'c tac) =
    fun (x: 'a) ->
        fun (y: 'b) ->
            (fun (ps: proofstate) ->
                BU.print_string "In compiled code (2)\n";
                interpret_tactic ps (t x y)) |> mk_tac
