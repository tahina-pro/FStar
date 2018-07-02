open Prims
type goal = FStar_Tactics_Types.goal
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_Interpreter.reflection_primops s e t
  
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> normalize [] e t 
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string 
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g  ->
    let uu____39 =
      let uu____40 = FStar_Tactics_Types.goal_env g  in
      let uu____41 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____40 uu____41  in
    FStar_Tactics_Types.goal_with_type g uu____39
  
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun projectee  ->
    match projectee with | { tac_f = __fname__tac_f;_} -> __fname__tac_f
  
let mk_tac :
  'a .
    (FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result) ->
      'a tac
  = fun f  -> { tac_f = f } 
let run :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun t  -> fun p  -> t.tac_f p 
let run_safe :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t  ->
    fun p  ->
      try (fun uu___350_154  -> match () with | () -> t.tac_f p) ()
      with
      | FStar_Errors.Err (uu____163,msg) ->
          FStar_Tactics_Result.Failed (msg, p)
      | FStar_Errors.Error (uu____165,msg,uu____167) ->
          FStar_Tactics_Result.Failed (msg, p)
      | e ->
          let uu____169 =
            let uu____174 = FStar_Util.message_of_exn e  in (uu____174, p)
             in
          FStar_Tactics_Result.Failed uu____169
  
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
  
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____246 = run t1 p  in
           match uu____246 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____253 = t2 a  in run uu____253 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
  
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let (idtac : unit tac) = ret () 
let (get_uvar_solved :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    let uu____273 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____273 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____291 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____292 =
      let uu____293 = check_goal_solved g  in
      match uu____293 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____297 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____297
       in
    FStar_Util.format2 "%s%s" uu____291 uu____292
  
let (goal_to_string :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> Prims.string)
  =
  fun ps  ->
    fun g  ->
      let uu____308 =
        (FStar_Options.print_implicits ()) ||
          ps.FStar_Tactics_Types.tac_verb_dbg
         in
      if uu____308
      then goal_to_string_verbose g
      else
        (let w =
           let uu____311 =
             get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
           match uu____311 with
           | FStar_Pervasives_Native.None  -> "_"
           | FStar_Pervasives_Native.Some t ->
               let uu____315 = FStar_Tactics_Types.goal_env g  in
               tts uu____315 t
            in
         let uu____316 =
           FStar_Syntax_Print.binders_to_string ", "
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            in
         let uu____317 =
           let uu____318 = FStar_Tactics_Types.goal_env g  in
           tts uu____318
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
            in
         FStar_Util.format3 "%s |- %s : %s" uu____316 w uu____317)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____334 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____334
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____350 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____350
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____371 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____371
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____378) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____388) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____403 =
      let uu____408 =
        let uu____409 = FStar_Tactics_Types.goal_env g  in
        let uu____410 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____409 uu____410  in
      FStar_Syntax_Util.un_squash uu____408  in
    match uu____403 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____416 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____444 =
            let uu____445 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____445  in
          if uu____444 then tacprint msg else ());
         ret ())
  
let (dump_goal :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> unit) =
  fun ps  ->
    fun goal  ->
      let uu____458 = goal_to_string ps goal  in tacprint uu____458
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____470 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____474 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____474))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____483  ->
    match uu____483 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let uu____496 =
          let uu____499 =
            let uu____500 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____500 msg
             in
          let uu____501 =
            let uu____504 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____505 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____505
              else ""  in
            let uu____507 =
              let uu____510 =
                let uu____511 =
                  FStar_TypeChecker_Env.debug
                    ps.FStar_Tactics_Types.main_context
                    (FStar_Options.Other "Imp")
                   in
                if uu____511
                then
                  let uu____512 =
                    FStar_Common.string_of_list p_imp
                      ps.FStar_Tactics_Types.all_implicits
                     in
                  FStar_Util.format1 "Imps: %s\n" uu____512
                else ""  in
              let uu____514 =
                let uu____517 =
                  let uu____518 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.goals)
                     in
                  let uu____519 =
                    let uu____520 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_String.concat "\n" uu____520  in
                  FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____518
                    uu____519
                   in
                let uu____523 =
                  let uu____526 =
                    let uu____527 =
                      FStar_Util.string_of_int
                        (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                       in
                    let uu____528 =
                      let uu____529 =
                        FStar_List.map (goal_to_string ps)
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_String.concat "\n" uu____529  in
                    FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____527
                      uu____528
                     in
                  [uu____526]  in
                uu____517 :: uu____523  in
              uu____510 :: uu____514  in
            uu____504 :: uu____507  in
          uu____499 :: uu____501  in
        FStar_String.concat "" uu____496
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____538 =
        let uu____539 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____539  in
      let uu____540 =
        let uu____545 =
          let uu____546 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____546  in
        FStar_Syntax_Print.binders_to_json uu____545  in
      FStar_All.pipe_right uu____538 uu____540  in
    let uu____547 =
      let uu____554 =
        let uu____561 =
          let uu____566 =
            let uu____567 =
              let uu____574 =
                let uu____579 =
                  let uu____580 =
                    let uu____581 = FStar_Tactics_Types.goal_env g  in
                    let uu____582 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____581 uu____582  in
                  FStar_Util.JsonStr uu____580  in
                ("witness", uu____579)  in
              let uu____583 =
                let uu____590 =
                  let uu____595 =
                    let uu____596 =
                      let uu____597 = FStar_Tactics_Types.goal_env g  in
                      let uu____598 = FStar_Tactics_Types.goal_type g  in
                      tts uu____597 uu____598  in
                    FStar_Util.JsonStr uu____596  in
                  ("type", uu____595)  in
                [uu____590]  in
              uu____574 :: uu____583  in
            FStar_Util.JsonAssoc uu____567  in
          ("goal", uu____566)  in
        [uu____561]  in
      ("hyps", g_binders) :: uu____554  in
    FStar_Util.JsonAssoc uu____547
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____631  ->
    match uu____631 with
    | (msg,ps) ->
        let uu____638 =
          let uu____645 =
            let uu____652 =
              let uu____659 =
                let uu____666 =
                  let uu____671 =
                    let uu____672 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____672  in
                  ("goals", uu____671)  in
                let uu____675 =
                  let uu____682 =
                    let uu____687 =
                      let uu____688 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____688  in
                    ("smt-goals", uu____687)  in
                  [uu____682]  in
                uu____666 :: uu____675  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____659
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____652  in
          let uu____711 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____724 =
                let uu____729 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____729)  in
              [uu____724]
            else []  in
          FStar_List.append uu____645 uu____711  in
        FStar_Util.JsonAssoc uu____638
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____759  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state1 : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____782 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____782 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____800 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____800 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____854 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____854
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____862 . Prims.string -> Prims.string -> 'Auu____862 tac =
  fun msg  ->
    fun x  -> let uu____875 = FStar_Util.format1 msg x  in fail uu____875
  
let fail2 :
  'Auu____884 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____884 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____902 = FStar_Util.format2 msg x y  in fail uu____902
  
let fail3 :
  'Auu____913 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____913 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____936 = FStar_Util.format3 msg x y z  in fail uu____936
  
let fail4 :
  'Auu____949 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____949 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____977 = FStar_Util.format4 msg x y z w  in fail uu____977
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1010 = run t ps  in
         match uu____1010 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___351_1034 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___351_1034.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___351_1034.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___351_1034.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___351_1034.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___351_1034.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___351_1034.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___351_1034.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___351_1034.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___351_1034.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___351_1034.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___351_1034.FStar_Tactics_Types.tac_verb_dbg)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1061 = trytac' t  in
    bind uu____1061
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1088 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___353_1119  ->
              match () with
              | () -> let uu____1124 = trytac t  in run uu____1124 ps) ()
         with
         | FStar_Errors.Err (uu____1140,msg) ->
             (log ps
                (fun uu____1144  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1149,msg,uu____1151) ->
             (log ps
                (fun uu____1154  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1187 = run t ps  in
           match uu____1187 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1206  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1227 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1227
         then
           let uu____1228 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1229 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1228
             uu____1229
         else ());
        (try
           (fun uu___355_1236  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1241 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1241
                    then
                      let uu____1242 = FStar_Util.string_of_bool res  in
                      let uu____1243 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1244 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1242
                        uu____1243 uu____1244
                    else ());
                   ret res)) ()
         with
         | FStar_Errors.Err (uu____1252,msg) ->
             mlog
               (fun uu____1255  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1257  -> ret false)
         | FStar_Errors.Error (uu____1258,msg,r) ->
             mlog
               (fun uu____1263  ->
                  let uu____1264 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1264) (fun uu____1266  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___356_1277 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___356_1277.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___356_1277.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___356_1277.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___357_1280 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___357_1280.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___357_1280.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___357_1280.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___357_1280.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___357_1280.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___357_1280.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___357_1280.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___357_1280.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___357_1280.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___357_1280.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___357_1280.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set ps')
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1303  ->
             (let uu____1305 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1305
              then
                (FStar_Options.push ();
                 (let uu____1307 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1309 = __do_unify env t1 t2  in
              bind uu____1309
                (fun r  ->
                   (let uu____1316 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1316 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1319  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___358_1326 = ps  in
         let uu____1327 =
           FStar_List.filter
             (fun g  ->
                let uu____1333 = check_goal_solved g  in
                FStar_Option.isNone uu____1333) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___358_1326.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___358_1326.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___358_1326.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1327;
           FStar_Tactics_Types.smt_goals =
             (uu___358_1326.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___358_1326.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___358_1326.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___358_1326.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___358_1326.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___358_1326.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___358_1326.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___358_1326.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1350 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1350 with
      | FStar_Pervasives_Native.Some uu____1355 ->
          let uu____1356 =
            let uu____1357 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1357  in
          fail uu____1356
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1373 = FStar_Tactics_Types.goal_env goal  in
      let uu____1374 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1373 solution uu____1374
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1380 =
         let uu___359_1381 = p  in
         let uu____1382 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___359_1381.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___359_1381.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___359_1381.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1382;
           FStar_Tactics_Types.smt_goals =
             (uu___359_1381.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___359_1381.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___359_1381.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___359_1381.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___359_1381.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___359_1381.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___359_1381.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___359_1381.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set uu____1380)
  
let (dismiss : unit -> unit tac) =
  fun uu____1391  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1398 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1419  ->
           let uu____1420 =
             let uu____1421 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1421  in
           let uu____1422 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1420 uu____1422)
        (fun uu____1425  ->
           let uu____1426 = trysolve goal solution  in
           bind uu____1426
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1434  -> remove_solved_goals)
                else
                  (let uu____1436 =
                     let uu____1437 =
                       let uu____1438 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1438 solution  in
                     let uu____1439 =
                       let uu____1440 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1441 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1440 uu____1441  in
                     let uu____1442 =
                       let uu____1443 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1444 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1443 uu____1444  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1437 uu____1439 uu____1442
                      in
                   fail uu____1436)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1459 = set_solution goal solution  in
      bind uu____1459
        (fun uu____1463  ->
           bind __dismiss (fun uu____1465  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___360_1472 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___360_1472.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___360_1472.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___360_1472.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___360_1472.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___360_1472.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___360_1472.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___360_1472.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___360_1472.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___360_1472.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___360_1472.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___360_1472.FStar_Tactics_Types.tac_verb_dbg)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1491 = FStar_Options.defensive ()  in
    if uu____1491
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1496 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1496)
         in
      let b2 =
        b1 &&
          (let uu____1499 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1499)
         in
      let rec aux b3 e =
        let uu____1511 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1511 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1529 =
        (let uu____1532 = aux b2 env  in Prims.op_Negation uu____1532) &&
          (let uu____1534 = FStar_ST.op_Bang nwarn  in
           uu____1534 < (Prims.parse_int "5"))
         in
      (if uu____1529
       then
         ((let uu____1555 =
             let uu____1556 = FStar_Tactics_Types.goal_type g  in
             uu____1556.FStar_Syntax_Syntax.pos  in
           let uu____1559 =
             let uu____1564 =
               let uu____1565 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1565
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1564)  in
           FStar_Errors.log_issue uu____1555 uu____1559);
          (let uu____1566 =
             let uu____1567 = FStar_ST.op_Bang nwarn  in
             uu____1567 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1566))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___361_1627 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___361_1627.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___361_1627.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___361_1627.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___361_1627.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___361_1627.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___361_1627.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___361_1627.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___361_1627.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___361_1627.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___361_1627.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___361_1627.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___362_1647 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___362_1647.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___362_1647.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___362_1647.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___362_1647.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___362_1647.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___362_1647.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___362_1647.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___362_1647.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___362_1647.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___362_1647.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___362_1647.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___363_1667 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___363_1667.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___363_1667.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___363_1667.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___363_1667.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___363_1667.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___363_1667.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___363_1667.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___363_1667.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___363_1667.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___363_1667.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___363_1667.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___364_1687 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___364_1687.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___364_1687.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___364_1687.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___364_1687.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___364_1687.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___364_1687.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___364_1687.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___364_1687.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___364_1687.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___364_1687.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___364_1687.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1698  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___365_1712 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___365_1712.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___365_1712.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___365_1712.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___365_1712.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___365_1712.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___365_1712.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___365_1712.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___365_1712.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___365_1712.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___365_1712.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___365_1712.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar)
          FStar_Pervasives_Native.tuple2 tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1740 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1740 with
        | (u,ctx_uvar,g_u) ->
            let uu____1774 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1774
              (fun uu____1783  ->
                 let uu____1784 =
                   let uu____1789 =
                     let uu____1790 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1790  in
                   (u, uu____1789)  in
                 ret uu____1784)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1808 = FStar_Syntax_Util.un_squash t  in
    match uu____1808 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1818 =
          let uu____1819 = FStar_Syntax_Subst.compress t'  in
          uu____1819.FStar_Syntax_Syntax.n  in
        (match uu____1818 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1823 -> false)
    | uu____1824 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1834 = FStar_Syntax_Util.un_squash t  in
    match uu____1834 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1844 =
          let uu____1845 = FStar_Syntax_Subst.compress t'  in
          uu____1845.FStar_Syntax_Syntax.n  in
        (match uu____1844 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1849 -> false)
    | uu____1850 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1861  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1872 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1872 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1879 = goal_to_string_verbose hd1  in
                    let uu____1880 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1879 uu____1880);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1887  ->
    let uu____1890 =
      bind get
        (fun ps  ->
           let uu____1896 = cur_goal ()  in
           bind uu____1896
             (fun g  ->
                (let uu____1903 =
                   let uu____1904 = FStar_Tactics_Types.goal_type g  in
                   uu____1904.FStar_Syntax_Syntax.pos  in
                 let uu____1907 =
                   let uu____1912 =
                     let uu____1913 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1913
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1912)  in
                 FStar_Errors.log_issue uu____1903 uu____1907);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1890
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1924  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___366_1934 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___366_1934.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___366_1934.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___366_1934.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___366_1934.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___366_1934.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___366_1934.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___366_1934.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___366_1934.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___366_1934.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___366_1934.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___366_1934.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1935 = set ps1  in
         bind uu____1935
           (fun uu____1940  ->
              let uu____1941 = FStar_BigInt.of_int_fs n1  in ret uu____1941))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1948  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1956 = FStar_BigInt.of_int_fs n1  in ret uu____1956)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1969  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1977 = FStar_BigInt.of_int_fs n1  in ret uu____1977)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1990  ->
    let uu____1993 = cur_goal ()  in
    bind uu____1993 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let typ =
            let uu____2025 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2025 phi  in
          let uu____2026 = new_uvar reason env typ  in
          bind uu____2026
            (fun uu____2041  ->
               match uu____2041 with
               | (uu____2048,ctx_uvar) ->
                   let goal =
                     FStar_Tactics_Types.mk_goal env ctx_uvar opts false  in
                   ret goal)
  
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,FStar_Reflection_Data.typ,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple3 tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____2093  ->
                let uu____2094 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2094)
             (fun uu____2097  ->
                let e1 =
                  let uu___367_2099 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___367_2099.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___367_2099.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___367_2099.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___367_2099.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___367_2099.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___367_2099.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___367_2099.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___367_2099.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___367_2099.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___367_2099.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___367_2099.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___367_2099.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___367_2099.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___367_2099.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___367_2099.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___367_2099.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___367_2099.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___367_2099.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___367_2099.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___367_2099.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___367_2099.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___367_2099.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___367_2099.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___367_2099.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___367_2099.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___367_2099.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___367_2099.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___367_2099.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___367_2099.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___367_2099.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___367_2099.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___367_2099.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___367_2099.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___367_2099.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___367_2099.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___367_2099.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___367_2099.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___367_2099.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___367_2099.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___367_2099.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___367_2099.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___369_2110  ->
                     match () with
                     | () ->
                         let uu____2119 =
                           (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                             e1 t
                            in
                         ret uu____2119) ()
                with
                | FStar_Errors.Err (uu____2146,msg) ->
                    let uu____2148 = tts e1 t  in
                    let uu____2149 =
                      let uu____2150 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2150
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2148 uu____2149 msg
                | FStar_Errors.Error (uu____2157,msg,uu____2159) ->
                    let uu____2160 = tts e1 t  in
                    let uu____2161 =
                      let uu____2162 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2162
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2160 uu____2161 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____2189  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___370_2207 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_2207.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_2207.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_2207.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___370_2207.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___370_2207.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_2207.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_2207.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_2207.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_2207.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___370_2207.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_2207.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2231 = get_guard_policy ()  in
      bind uu____2231
        (fun old_pol  ->
           let uu____2237 = set_guard_policy pol  in
           bind uu____2237
             (fun uu____2241  ->
                bind t
                  (fun r  ->
                     let uu____2245 = set_guard_policy old_pol  in
                     bind uu____2245 (fun uu____2249  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2252 = let uu____2257 = cur_goal ()  in trytac uu____2257  in
  bind uu____2252
    (fun uu___341_2264  ->
       match uu___341_2264 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2270 = FStar_Options.peek ()  in ret uu____2270)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2293 =
               let uu____2294 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2294.FStar_TypeChecker_Env.guard_f  in
             match uu____2293 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2298 = istrivial e f  in
                 if uu____2298
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2306 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2306
                              (fun goal  ->
                                 let goal1 =
                                   let uu___371_2313 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___371_2313.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___371_2313.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___371_2313.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2314 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2314
                              (fun goal  ->
                                 let goal1 =
                                   let uu___372_2321 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___372_2321.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___372_2321.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___372_2321.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               (fun uu___374_2326  ->
                                  match () with
                                  | () ->
                                      let uu____2329 =
                                        let uu____2330 =
                                          let uu____2331 =
                                            FStar_TypeChecker_Rel.discharge_guard_no_smt
                                              e g
                                             in
                                          FStar_All.pipe_left
                                            FStar_TypeChecker_Env.is_trivial
                                            uu____2331
                                           in
                                        Prims.op_Negation uu____2330  in
                                      if uu____2329
                                      then
                                        mlog
                                          (fun uu____2336  ->
                                             let uu____2337 =
                                               FStar_TypeChecker_Rel.guard_to_string
                                                 e g
                                                in
                                             FStar_Util.print1 "guard = %s\n"
                                               uu____2337)
                                          (fun uu____2339  ->
                                             fail1
                                               "Forcing the guard failed %s)"
                                               reason)
                                      else ret ()) ()
                             with
                             | uu____2346 ->
                                 mlog
                                   (fun uu____2349  ->
                                      let uu____2350 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2350)
                                   (fun uu____2352  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2362 =
      let uu____2365 = cur_goal ()  in
      bind uu____2365
        (fun goal  ->
           let uu____2371 =
             let uu____2380 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2380 t  in
           bind uu____2371
             (fun uu____2392  ->
                match uu____2392 with
                | (t1,typ,guard) ->
                    let uu____2404 =
                      let uu____2407 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2407 guard  in
                    bind uu____2404 (fun uu____2409  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2362
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2438 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2438 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2449  ->
    let uu____2452 = cur_goal ()  in
    bind uu____2452
      (fun goal  ->
         let uu____2458 =
           let uu____2459 = FStar_Tactics_Types.goal_env goal  in
           let uu____2460 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2459 uu____2460  in
         if uu____2458
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2464 =
              let uu____2465 = FStar_Tactics_Types.goal_env goal  in
              let uu____2466 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2465 uu____2466  in
            fail1 "Not a trivial goal: %s" uu____2464))
  
let (goal_from_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t ->
        FStar_Options.optionstate ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2495 =
            let uu____2496 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2496.FStar_TypeChecker_Env.guard_f  in
          match uu____2495 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2504 = istrivial e f  in
              if uu____2504
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2512 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2512
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___375_2522 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___375_2522.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___375_2522.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___375_2522.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2529  ->
    let uu____2532 = cur_goal ()  in
    bind uu____2532
      (fun g  ->
         let uu____2538 = is_irrelevant g  in
         if uu____2538
         then bind __dismiss (fun uu____2542  -> add_smt_goals [g])
         else
           (let uu____2544 =
              let uu____2545 = FStar_Tactics_Types.goal_env g  in
              let uu____2546 = FStar_Tactics_Types.goal_type g  in
              tts uu____2545 uu____2546  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2544))
  
let divide :
  'a 'b .
    FStar_BigInt.t ->
      'a tac -> 'b tac -> ('a,'b) FStar_Pervasives_Native.tuple2 tac
  =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____2595 =
               try
                 (fun uu___380_2618  ->
                    match () with
                    | () ->
                        let uu____2629 =
                          let uu____2638 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2638
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2629) ()
               with | uu____2660 -> fail "divide: not enough goals"  in
             bind uu____2595
               (fun uu____2686  ->
                  match uu____2686 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___376_2712 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___376_2712.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___376_2712.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___376_2712.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___376_2712.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___376_2712.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___376_2712.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___376_2712.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___376_2712.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___376_2712.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___376_2712.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2713 = set lp  in
                      bind uu____2713
                        (fun uu____2721  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___377_2737 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___377_2737.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___377_2737.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___377_2737.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___377_2737.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___377_2737.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___377_2737.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___377_2737.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___377_2737.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___377_2737.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___377_2737.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2738 = set rp  in
                                     bind uu____2738
                                       (fun uu____2746  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___378_2762 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___378_2762.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___378_2762.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___378_2762.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_List.append
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_List.append
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (uu___378_2762.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___378_2762.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___378_2762.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___378_2762.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___378_2762.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___378_2762.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___378_2762.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2763 = set p'
                                                       in
                                                    bind uu____2763
                                                      (fun uu____2771  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2777 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2798 = divide FStar_BigInt.one f idtac  in
    bind uu____2798
      (fun uu____2811  -> match uu____2811 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2848::uu____2849 ->
             let uu____2852 =
               let uu____2861 = map tau  in
               divide FStar_BigInt.one tau uu____2861  in
             bind uu____2852
               (fun uu____2879  ->
                  match uu____2879 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2920 =
        bind t1
          (fun uu____2925  ->
             let uu____2926 = map t2  in
             bind uu____2926 (fun uu____2934  -> ret ()))
         in
      focus uu____2920
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2943  ->
    let uu____2946 =
      let uu____2949 = cur_goal ()  in
      bind uu____2949
        (fun goal  ->
           let uu____2958 =
             let uu____2965 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2965  in
           match uu____2958 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2974 =
                 let uu____2975 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2975  in
               if uu____2974
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2980 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2980 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2994 = new_uvar "intro" env' typ'  in
                  bind uu____2994
                    (fun uu____3010  ->
                       match uu____3010 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3034 = set_solution goal sol  in
                           bind uu____3034
                             (fun uu____3040  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3042 =
                                  let uu____3045 = bnorm_goal g  in
                                  replace_cur uu____3045  in
                                bind uu____3042 (fun uu____3047  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3052 =
                 let uu____3053 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3054 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3053 uu____3054  in
               fail1 "goal is not an arrow (%s)" uu____3052)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2946
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3069  ->
    let uu____3076 = cur_goal ()  in
    bind uu____3076
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3093 =
            let uu____3100 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3100  in
          match uu____3093 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3113 =
                let uu____3114 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3114  in
              if uu____3113
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3127 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3127
                    in
                 let bs =
                   let uu____3137 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3137; b]  in
                 let env' =
                   let uu____3163 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3163 bs  in
                 let uu____3164 =
                   let uu____3171 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3171  in
                 bind uu____3164
                   (fun uu____3190  ->
                      match uu____3190 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3204 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3207 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3204
                              FStar_Parser_Const.effect_Tot_lid uu____3207 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3225 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3225 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3247 =
                                   let uu____3248 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3248.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3247
                                  in
                               let uu____3261 = set_solution goal tm  in
                               bind uu____3261
                                 (fun uu____3270  ->
                                    let uu____3271 =
                                      let uu____3274 =
                                        bnorm_goal
                                          (let uu___381_3277 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___381_3277.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___381_3277.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___381_3277.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3274  in
                                    bind uu____3271
                                      (fun uu____3284  ->
                                         let uu____3285 =
                                           let uu____3290 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3290, b)  in
                                         ret uu____3285)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3299 =
                let uu____3300 = FStar_Tactics_Types.goal_env goal  in
                let uu____3301 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3300 uu____3301  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3299))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3319 = cur_goal ()  in
    bind uu____3319
      (fun goal  ->
         mlog
           (fun uu____3326  ->
              let uu____3327 =
                let uu____3328 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3328  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3327)
           (fun uu____3333  ->
              let steps =
                let uu____3337 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3337
                 in
              let t =
                let uu____3341 = FStar_Tactics_Types.goal_env goal  in
                let uu____3342 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3341 uu____3342  in
              let uu____3343 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3343))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3367 =
          mlog
            (fun uu____3372  ->
               let uu____3373 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3373)
            (fun uu____3375  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3381 -> g.FStar_Tactics_Types.opts
                      | uu____3384 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3389  ->
                         let uu____3390 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3390)
                      (fun uu____3393  ->
                         let uu____3394 = __tc e t  in
                         bind uu____3394
                           (fun uu____3415  ->
                              match uu____3415 with
                              | (t1,uu____3425,uu____3426) ->
                                  let steps =
                                    let uu____3430 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3430
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3367
  
let (refine_intro : unit -> unit tac) =
  fun uu____3444  ->
    let uu____3447 =
      let uu____3450 = cur_goal ()  in
      bind uu____3450
        (fun g  ->
           let uu____3457 =
             let uu____3468 = FStar_Tactics_Types.goal_env g  in
             let uu____3469 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3468 uu____3469
              in
           match uu____3457 with
           | (uu____3472,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3497 =
                 let uu____3502 =
                   let uu____3507 =
                     let uu____3508 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3508]  in
                   FStar_Syntax_Subst.open_term uu____3507 phi  in
                 match uu____3502 with
                 | (bvs,phi1) ->
                     let uu____3533 =
                       let uu____3534 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3534  in
                     (uu____3533, phi1)
                  in
               (match uu____3497 with
                | (bv1,phi1) ->
                    let uu____3553 =
                      let uu____3556 = FStar_Tactics_Types.goal_env g  in
                      let uu____3557 =
                        let uu____3558 =
                          let uu____3561 =
                            let uu____3562 =
                              let uu____3569 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3569)  in
                            FStar_Syntax_Syntax.NT uu____3562  in
                          [uu____3561]  in
                        FStar_Syntax_Subst.subst uu____3558 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3556
                        uu____3557 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3553
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3577  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3447
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3596 = cur_goal ()  in
      bind uu____3596
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3604 = FStar_Tactics_Types.goal_env goal  in
               let uu____3605 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3604 uu____3605
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3607 = __tc env t  in
           bind uu____3607
             (fun uu____3626  ->
                match uu____3626 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3641  ->
                         let uu____3642 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3643 =
                           let uu____3644 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3644
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3642 uu____3643)
                      (fun uu____3647  ->
                         let uu____3648 =
                           let uu____3651 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3651 guard  in
                         bind uu____3648
                           (fun uu____3653  ->
                              mlog
                                (fun uu____3657  ->
                                   let uu____3658 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3659 =
                                     let uu____3660 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3660
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3658 uu____3659)
                                (fun uu____3663  ->
                                   let uu____3664 =
                                     let uu____3667 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3668 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3667 typ uu____3668  in
                                   bind uu____3664
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3674 =
                                             let uu____3675 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3675 t1  in
                                           let uu____3676 =
                                             let uu____3677 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3677 typ  in
                                           let uu____3678 =
                                             let uu____3679 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3680 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3679 uu____3680  in
                                           let uu____3681 =
                                             let uu____3682 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3683 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3682 uu____3683  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3674 uu____3676 uu____3678
                                             uu____3681)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3698 =
        mlog
          (fun uu____3703  ->
             let uu____3704 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3704)
          (fun uu____3707  ->
             let uu____3708 =
               let uu____3715 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3715  in
             bind uu____3708
               (fun uu___343_3724  ->
                  match uu___343_3724 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3734  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3737  ->
                           let uu____3738 =
                             let uu____3745 =
                               let uu____3748 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3748
                                 (fun uu____3753  ->
                                    let uu____3754 = refine_intro ()  in
                                    bind uu____3754
                                      (fun uu____3758  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3745  in
                           bind uu____3738
                             (fun uu___342_3765  ->
                                match uu___342_3765 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3773 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3698
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3823 = f x  in
          bind uu____3823
            (fun y  ->
               let uu____3831 = mapM f xs  in
               bind uu____3831 (fun ys  -> ret (y :: ys)))
  
let rec (__try_match_by_application :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
            FStar_Pervasives_Native.tuple3 Prims.list tac)
  =
  fun acc  ->
    fun e  ->
      fun ty1  ->
        fun ty2  ->
          let uu____3902 = do_unify e ty1 ty2  in
          bind uu____3902
            (fun uu___344_3914  ->
               if uu___344_3914
               then ret acc
               else
                 (let uu____3933 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3933 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3954 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3955 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3954
                        uu____3955
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3970 =
                        let uu____3971 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3971  in
                      if uu____3970
                      then fail "Codomain is effectful"
                      else
                        (let uu____3991 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3991
                           (fun uu____4017  ->
                              match uu____4017 with
                              | (uvt,uv) ->
                                  let typ = comp_to_typ c  in
                                  let typ' =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT
                                         ((FStar_Pervasives_Native.fst b),
                                           uvt)] typ
                                     in
                                  __try_match_by_application
                                    ((uvt, (FStar_Pervasives_Native.snd b),
                                       uv) :: acc) e typ' ty2))))
  
let (try_match_by_application :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
          FStar_Pervasives_Native.tuple3 Prims.list tac)
  = fun e  -> fun ty1  -> fun ty2  -> __try_match_by_application [] e ty1 ty2 
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4103 =
        mlog
          (fun uu____4108  ->
             let uu____4109 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4109)
          (fun uu____4112  ->
             let uu____4113 = cur_goal ()  in
             bind uu____4113
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4121 = __tc e tm  in
                  bind uu____4121
                    (fun uu____4142  ->
                       match uu____4142 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4155 =
                             let uu____4166 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4166  in
                           bind uu____4155
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4209  ->
                                       fun w  ->
                                         match uu____4209 with
                                         | (uvt,q,uu____4227) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4259 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4276  ->
                                       fun s  ->
                                         match uu____4276 with
                                         | (uu____4288,uu____4289,uv) ->
                                             let uu____4291 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4291) uvs uu____4259
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4300 = solve' goal w  in
                                bind uu____4300
                                  (fun uu____4305  ->
                                     let uu____4306 =
                                       mapM
                                         (fun uu____4323  ->
                                            match uu____4323 with
                                            | (uvt,q,uv) ->
                                                let uu____4335 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4335 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4340 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4341 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4341
                                                     then ret ()
                                                     else
                                                       (let uu____4345 =
                                                          let uu____4348 =
                                                            bnorm_goal
                                                              (let uu___382_4351
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___382_4351.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___382_4351.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4348]  in
                                                        add_goals uu____4345)))
                                         uvs
                                        in
                                     bind uu____4306
                                       (fun uu____4355  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4103
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4380 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4380
    then
      let uu____4387 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4402 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4455 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4387 with
      | (pre,post) ->
          let post1 =
            let uu____4487 =
              let uu____4498 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4498]  in
            FStar_Syntax_Util.mk_app post uu____4487  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4528 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4528
       then
         let uu____4535 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4535
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4568 =
      let uu____4571 =
        mlog
          (fun uu____4576  ->
             let uu____4577 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4577)
          (fun uu____4581  ->
             let is_unit_t t =
               let uu____4588 =
                 let uu____4589 = FStar_Syntax_Subst.compress t  in
                 uu____4589.FStar_Syntax_Syntax.n  in
               match uu____4588 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4593 -> false  in
             let uu____4594 = cur_goal ()  in
             bind uu____4594
               (fun goal  ->
                  let uu____4600 =
                    let uu____4609 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4609 tm  in
                  bind uu____4600
                    (fun uu____4624  ->
                       match uu____4624 with
                       | (tm1,t,guard) ->
                           let uu____4636 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4636 with
                            | (bs,comp) ->
                                let uu____4669 = lemma_or_sq comp  in
                                (match uu____4669 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4688 =
                                       FStar_List.fold_left
                                         (fun uu____4736  ->
                                            fun uu____4737  ->
                                              match (uu____4736, uu____4737)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4850 =
                                                    is_unit_t b_t  in
                                                  if uu____4850
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4888 =
                                                       let uu____4901 =
                                                         let uu____4902 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4902.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4905 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4901
                                                         uu____4905 b_t
                                                        in
                                                     match uu____4888 with
                                                     | (u,uu____4923,g_u) ->
                                                         let uu____4937 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4937,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4688 with
                                      | (uvs,implicits,subst1) ->
                                          let uvs1 = FStar_List.rev uvs  in
                                          let pre1 =
                                            FStar_Syntax_Subst.subst subst1
                                              pre
                                             in
                                          let post1 =
                                            FStar_Syntax_Subst.subst subst1
                                              post
                                             in
                                          let uu____5016 =
                                            let uu____5019 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____5020 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____5021 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____5019 uu____5020
                                              uu____5021
                                             in
                                          bind uu____5016
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____5029 =
                                                   let uu____5030 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____5030 tm1  in
                                                 let uu____5031 =
                                                   let uu____5032 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5033 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____5032 uu____5033
                                                    in
                                                 let uu____5034 =
                                                   let uu____5035 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5036 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____5035 uu____5036
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____5029 uu____5031
                                                   uu____5034
                                               else
                                                 (let uu____5038 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____5038
                                                    (fun uu____5043  ->
                                                       let uu____5044 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____5044
                                                         (fun uu____5052  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____5077
                                                                  =
                                                                  let uu____5080
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____5080
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____5077
                                                                 in
                                                              FStar_List.existsML
                                                                (fun u  ->
                                                                   FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                free_uvars
                                                               in
                                                            let appears uv
                                                              goals =
                                                              FStar_List.existsML
                                                                (fun g'  ->
                                                                   let uu____5115
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____5115)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____5131
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____5131
                                                              with
                                                              | (hd1,uu____5149)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5175)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5192
                                                                    -> false)
                                                               in
                                                            let uu____5193 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun imp 
                                                                    ->
                                                                    let term
                                                                    =
                                                                    imp.FStar_TypeChecker_Env.imp_tm
                                                                     in
                                                                    let ctx_uvar
                                                                    =
                                                                    imp.FStar_TypeChecker_Env.imp_uvar
                                                                     in
                                                                    let uu____5223
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5223
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5245)
                                                                    ->
                                                                    let uu____5270
                                                                    =
                                                                    let uu____5271
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5271.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5270
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5279)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___383_5299
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___383_5299.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___383_5299.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___383_5299.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5302
                                                                    ->
                                                                    let env =
                                                                    let uu___384_5304
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___384_5304.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5306
                                                                    =
                                                                    let uu____5309
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5309
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5306
                                                                    (fun
                                                                    uu____5313
                                                                     ->
                                                                    ret []))))
                                                               in
                                                            bind uu____5193
                                                              (fun sub_goals 
                                                                 ->
                                                                 let sub_goals1
                                                                   =
                                                                   FStar_List.flatten
                                                                    sub_goals
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5375
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5375
                                                                    then
                                                                    let uu____5378
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5378
                                                                    else
                                                                    filter' f
                                                                    xs1
                                                                    in
                                                                 let sub_goals2
                                                                   =
                                                                   filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____5392
                                                                    =
                                                                    let uu____5393
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5393
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5392)
                                                                    sub_goals1
                                                                    in
                                                                 let uu____5394
                                                                   =
                                                                   let uu____5397
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5397
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5394
                                                                   (fun
                                                                    uu____5400
                                                                     ->
                                                                    let uu____5401
                                                                    =
                                                                    let uu____5404
                                                                    =
                                                                    let uu____5405
                                                                    =
                                                                    let uu____5406
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5407
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5406
                                                                    uu____5407
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5405
                                                                     in
                                                                    if
                                                                    uu____5404
                                                                    then
                                                                    let uu____5410
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5410
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5401
                                                                    (fun
                                                                    uu____5413
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____4571  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4568
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5435 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5435 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5445::(e1,uu____5447)::(e2,uu____5449)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5510 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5534 = destruct_eq' typ  in
    match uu____5534 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5564 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5564 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env,FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____5626 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5626 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5674 = aux e'  in
               FStar_Util.map_opt uu____5674
                 (fun uu____5698  ->
                    match uu____5698 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5719 = aux e  in
      FStar_Util.map_opt uu____5719
        (fun uu____5743  ->
           match uu____5743 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
let (push_bvs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list -> FStar_TypeChecker_Env.env)
  =
  fun e  ->
    fun bvs  ->
      FStar_List.fold_left
        (fun e1  -> fun b  -> FStar_TypeChecker_Env.push_bv e1 b) e bvs
  
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Tactics_Types.goal ->
          FStar_Tactics_Types.goal FStar_Pervasives_Native.option)
  =
  fun b1  ->
    fun b2  ->
      fun s  ->
        fun g  ->
          let uu____5810 =
            let uu____5819 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5819  in
          FStar_Util.map_opt uu____5810
            (fun uu____5834  ->
               match uu____5834 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___385_5853 = bv  in
                     let uu____5854 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___385_5853.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___385_5853.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5854
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___386_5862 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5863 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5872 =
                       let uu____5875 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5875  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___386_5862.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5863;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5872;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___386_5862.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___386_5862.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___386_5862.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___387_5876 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___387_5876.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___387_5876.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___387_5876.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5886 =
      let uu____5889 = cur_goal ()  in
      bind uu____5889
        (fun goal  ->
           let uu____5897 = h  in
           match uu____5897 with
           | (bv,uu____5901) ->
               mlog
                 (fun uu____5909  ->
                    let uu____5910 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5911 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5910
                      uu____5911)
                 (fun uu____5914  ->
                    let uu____5915 =
                      let uu____5924 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5924  in
                    match uu____5915 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5945 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5945 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5960 =
                               let uu____5961 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5961.FStar_Syntax_Syntax.n  in
                             (match uu____5960 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___388_5978 = bv1  in
                                    let uu____5979 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___388_5978.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___388_5978.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5979
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___389_5987 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5988 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5997 =
                                      let uu____6000 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6000
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___389_5987.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5988;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5997;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___389_5987.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___389_5987.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___389_5987.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___390_6003 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___390_6003.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___390_6003.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___390_6003.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6004 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6005 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5886
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6030 =
        let uu____6033 = cur_goal ()  in
        bind uu____6033
          (fun goal  ->
             let uu____6044 = b  in
             match uu____6044 with
             | (bv,uu____6048) ->
                 let bv' =
                   let uu____6054 =
                     let uu___391_6055 = bv  in
                     let uu____6056 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6056;
                       FStar_Syntax_Syntax.index =
                         (uu___391_6055.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___391_6055.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6054  in
                 let s1 =
                   let uu____6060 =
                     let uu____6061 =
                       let uu____6068 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6068)  in
                     FStar_Syntax_Syntax.NT uu____6061  in
                   [uu____6060]  in
                 let uu____6073 = subst_goal bv bv' s1 goal  in
                 (match uu____6073 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6030
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6092 =
      let uu____6095 = cur_goal ()  in
      bind uu____6095
        (fun goal  ->
           let uu____6104 = b  in
           match uu____6104 with
           | (bv,uu____6108) ->
               let uu____6113 =
                 let uu____6122 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6122  in
               (match uu____6113 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6143 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6143 with
                     | (ty,u) ->
                         let uu____6152 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6152
                           (fun uu____6170  ->
                              match uu____6170 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___392_6180 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___392_6180.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___392_6180.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6184 =
                                      let uu____6185 =
                                        let uu____6192 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6192)  in
                                      FStar_Syntax_Syntax.NT uu____6185  in
                                    [uu____6184]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___393_6204 = b1  in
                                         let uu____6205 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___393_6204.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___393_6204.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6205
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6212  ->
                                       let new_goal =
                                         let uu____6214 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6215 =
                                           let uu____6216 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6216
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6214 uu____6215
                                          in
                                       let uu____6217 = add_goals [new_goal]
                                          in
                                       bind uu____6217
                                         (fun uu____6222  ->
                                            let uu____6223 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6223
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6092
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6246 =
        let uu____6249 = cur_goal ()  in
        bind uu____6249
          (fun goal  ->
             let uu____6258 = b  in
             match uu____6258 with
             | (bv,uu____6262) ->
                 let uu____6267 =
                   let uu____6276 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6276  in
                 (match uu____6267 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6300 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6300
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___394_6305 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___394_6305.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___394_6305.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6307 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6307))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6246
  
let (revert : unit -> unit tac) =
  fun uu____6318  ->
    let uu____6321 = cur_goal ()  in
    bind uu____6321
      (fun goal  ->
         let uu____6327 =
           let uu____6334 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6334  in
         match uu____6327 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6350 =
                 let uu____6353 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6353  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6350
                in
             let uu____6368 = new_uvar "revert" env' typ'  in
             bind uu____6368
               (fun uu____6383  ->
                  match uu____6383 with
                  | (r,u_r) ->
                      let uu____6392 =
                        let uu____6395 =
                          let uu____6396 =
                            let uu____6397 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6397.FStar_Syntax_Syntax.pos  in
                          let uu____6400 =
                            let uu____6405 =
                              let uu____6406 =
                                let uu____6415 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6415  in
                              [uu____6406]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6405  in
                          uu____6400 FStar_Pervasives_Native.None uu____6396
                           in
                        set_solution goal uu____6395  in
                      bind uu____6392
                        (fun uu____6436  ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                              in
                           replace_cur g)))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____6448 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6448
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6463 = cur_goal ()  in
    bind uu____6463
      (fun goal  ->
         mlog
           (fun uu____6471  ->
              let uu____6472 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6473 =
                let uu____6474 =
                  let uu____6475 =
                    let uu____6484 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6484  in
                  FStar_All.pipe_right uu____6475 FStar_List.length  in
                FStar_All.pipe_right uu____6474 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6472 uu____6473)
           (fun uu____6501  ->
              let uu____6502 =
                let uu____6511 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6511  in
              match uu____6502 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6550 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6550
                        then
                          let uu____6553 =
                            let uu____6554 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6554
                             in
                          fail uu____6553
                        else check1 bvs2
                     in
                  let uu____6556 =
                    let uu____6557 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6557  in
                  if uu____6556
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6561 = check1 bvs  in
                     bind uu____6561
                       (fun uu____6567  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6569 =
                            let uu____6576 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6576  in
                          bind uu____6569
                            (fun uu____6585  ->
                               match uu____6585 with
                               | (ut,uvar_ut) ->
                                   let uu____6594 = set_solution goal ut  in
                                   bind uu____6594
                                     (fun uu____6599  ->
                                        let uu____6600 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6600))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6607  ->
    let uu____6610 = cur_goal ()  in
    bind uu____6610
      (fun goal  ->
         let uu____6616 =
           let uu____6623 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6623  in
         match uu____6616 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6631) ->
             let uu____6636 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6636)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6646 = cur_goal ()  in
    bind uu____6646
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6656 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6656  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6659  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6669 = cur_goal ()  in
    bind uu____6669
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6679 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6679  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6682  -> add_goals [g']))
  
let rec (tac_fold_env :
  FStar_Tactics_Types.direction ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac) ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun d  ->
    fun f  ->
      fun env  ->
        fun t  ->
          let tn =
            let uu____6722 = FStar_Syntax_Subst.compress t  in
            uu____6722.FStar_Syntax_Syntax.n  in
          let uu____6725 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___398_6731 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___398_6731.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___398_6731.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6725
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6747 =
                   let uu____6748 = FStar_Syntax_Subst.compress t1  in
                   uu____6748.FStar_Syntax_Syntax.n  in
                 match uu____6747 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6779 = ff hd1  in
                     bind uu____6779
                       (fun hd2  ->
                          let fa uu____6805 =
                            match uu____6805 with
                            | (a,q) ->
                                let uu____6826 = ff a  in
                                bind uu____6826 (fun a1  -> ret (a1, q))
                             in
                          let uu____6845 = mapM fa args  in
                          bind uu____6845
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6927 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6927 with
                      | (bs1,t') ->
                          let uu____6936 =
                            let uu____6939 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6939 t'  in
                          bind uu____6936
                            (fun t''  ->
                               let uu____6943 =
                                 let uu____6944 =
                                   let uu____6963 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6972 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6963, uu____6972, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6944  in
                               ret uu____6943))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7047 = ff hd1  in
                     bind uu____7047
                       (fun hd2  ->
                          let ffb br =
                            let uu____7062 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7062 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7094 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7094  in
                                let uu____7095 = ff1 e  in
                                bind uu____7095
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7110 = mapM ffb brs  in
                          bind uu____7110
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7154;
                          FStar_Syntax_Syntax.lbtyp = uu____7155;
                          FStar_Syntax_Syntax.lbeff = uu____7156;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7158;
                          FStar_Syntax_Syntax.lbpos = uu____7159;_}::[]),e)
                     ->
                     let lb =
                       let uu____7184 =
                         let uu____7185 = FStar_Syntax_Subst.compress t1  in
                         uu____7185.FStar_Syntax_Syntax.n  in
                       match uu____7184 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7189) -> lb
                       | uu____7202 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7211 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7211
                         (fun def1  ->
                            ret
                              (let uu___395_7217 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___395_7217.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___395_7217.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___395_7217.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___395_7217.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___395_7217.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___395_7217.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7218 = fflb lb  in
                     bind uu____7218
                       (fun lb1  ->
                          let uu____7228 =
                            let uu____7233 =
                              let uu____7234 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7234]  in
                            FStar_Syntax_Subst.open_term uu____7233 e  in
                          match uu____7228 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7264 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7264  in
                              let uu____7265 = ff1 e1  in
                              bind uu____7265
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7306 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7306
                         (fun def  ->
                            ret
                              (let uu___396_7312 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___396_7312.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___396_7312.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___396_7312.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___396_7312.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___396_7312.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___396_7312.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7313 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7313 with
                      | (lbs1,e1) ->
                          let uu____7328 = mapM fflb lbs1  in
                          bind uu____7328
                            (fun lbs2  ->
                               let uu____7340 = ff e1  in
                               bind uu____7340
                                 (fun e2  ->
                                    let uu____7348 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7348 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7416 = ff t2  in
                     bind uu____7416
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7447 = ff t2  in
                     bind uu____7447
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7454 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___397_7461 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___397_7461.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___397_7461.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let (pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    unit tac ->
      FStar_Options.optionstate ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun env  ->
          fun t  ->
            let uu____7498 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___399_7507 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___399_7507.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___399_7507.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___399_7507.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___399_7507.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___399_7507.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___399_7507.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___399_7507.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___399_7507.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___399_7507.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___399_7507.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___399_7507.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___399_7507.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___399_7507.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___399_7507.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___399_7507.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___399_7507.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___399_7507.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___399_7507.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___399_7507.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___399_7507.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___399_7507.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___399_7507.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___399_7507.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___399_7507.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___399_7507.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___399_7507.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___399_7507.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___399_7507.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___399_7507.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___399_7507.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___399_7507.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___399_7507.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___399_7507.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___399_7507.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___399_7507.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___399_7507.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___399_7507.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___399_7507.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___399_7507.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___399_7507.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___399_7507.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7498 with
            | (t1,lcomp,g) ->
                let uu____7513 =
                  (let uu____7516 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7516) ||
                    (let uu____7518 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7518)
                   in
                if uu____7513
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7526 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7526
                       (fun uu____7542  ->
                          match uu____7542 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7555  ->
                                    let uu____7556 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7557 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7556 uu____7557);
                               (let uu____7558 =
                                  let uu____7561 =
                                    let uu____7562 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7562 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7561
                                    opts
                                   in
                                bind uu____7558
                                  (fun uu____7565  ->
                                     let uu____7566 =
                                       bind tau
                                         (fun uu____7572  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7578  ->
                                                 let uu____7579 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7580 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7579 uu____7580);
                                            ret ut1)
                                        in
                                     focus uu____7566))))
                      in
                   let uu____7581 = trytac' rewrite_eq  in
                   bind uu____7581
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
  
type ctrl = FStar_BigInt.t
let (keepGoing : ctrl) = FStar_BigInt.zero 
let (proceedToNextSubtree : FStar_BigInt.bigint) = FStar_BigInt.one 
let (globalStop : FStar_BigInt.bigint) =
  FStar_BigInt.succ_big_int FStar_BigInt.one 
type rewrite_result = Prims.bool
let (skipThisTerm : Prims.bool) = false 
let (rewroteThisTerm : Prims.bool) = true 
type 'a ctrl_tac = ('a,ctrl) FStar_Pervasives_Native.tuple2 tac
let rec (ctrl_tac_fold :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun f  ->
    fun env  ->
      fun ctrl  ->
        fun t  ->
          let keep_going c =
            if c = proceedToNextSubtree then keepGoing else c  in
          let maybe_continue ctrl1 t1 k =
            if ctrl1 = globalStop
            then ret (t1, globalStop)
            else
              if ctrl1 = proceedToNextSubtree
              then ret (t1, keepGoing)
              else k t1
             in
          let uu____7779 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7779
            (fun t1  ->
               let uu____7787 =
                 f env
                   (let uu___402_7796 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___402_7796.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___402_7796.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7787
                 (fun uu____7812  ->
                    match uu____7812 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7835 =
                               let uu____7836 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7836.FStar_Syntax_Syntax.n  in
                             match uu____7835 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7873 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7873
                                   (fun uu____7898  ->
                                      match uu____7898 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7914 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7914
                                            (fun uu____7941  ->
                                               match uu____7941 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___400_7971 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___400_7971.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___400_7971.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8013 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8013 with
                                  | (bs1,t') ->
                                      let uu____8028 =
                                        let uu____8035 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8035 ctrl1 t'
                                         in
                                      bind uu____8028
                                        (fun uu____8053  ->
                                           match uu____8053 with
                                           | (t'',ctrl2) ->
                                               let uu____8068 =
                                                 let uu____8075 =
                                                   let uu___401_8078 = t4  in
                                                   let uu____8081 =
                                                     let uu____8082 =
                                                       let uu____8101 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8110 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8101,
                                                         uu____8110, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8082
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8081;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___401_8078.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___401_8078.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8075, ctrl2)  in
                                               ret uu____8068))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8163 -> ret (t3, ctrl1))))

and (ctrl_tac_fold_args :
  (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac) ->
    env ->
      ctrl ->
        FStar_Syntax_Syntax.arg Prims.list ->
          FStar_Syntax_Syntax.arg Prims.list ctrl_tac)
  =
  fun f  ->
    fun env  ->
      fun ctrl  ->
        fun ts  ->
          match ts with
          | [] -> ret ([], ctrl)
          | (t,q)::ts1 ->
              let uu____8210 = ctrl_tac_fold f env ctrl t  in
              bind uu____8210
                (fun uu____8234  ->
                   match uu____8234 with
                   | (t1,ctrl1) ->
                       let uu____8249 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8249
                         (fun uu____8276  ->
                            match uu____8276 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      unit tac ->
        FStar_Options.optionstate ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun ps  ->
    fun ctrl  ->
      fun rewriter  ->
        fun opts  ->
          fun env  ->
            fun t  ->
              let t1 = FStar_Syntax_Subst.compress t  in
              let uu____8360 =
                let uu____8367 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8367
                  (fun uu____8376  ->
                     let uu____8377 = ctrl t1  in
                     bind uu____8377
                       (fun res  ->
                          let uu____8400 = trivial ()  in
                          bind uu____8400 (fun uu____8408  -> ret res)))
                 in
              bind uu____8360
                (fun uu____8424  ->
                   match uu____8424 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8448 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___403_8457 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___403_8457.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___403_8457.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___403_8457.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___403_8457.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___403_8457.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___403_8457.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___403_8457.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___403_8457.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___403_8457.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___403_8457.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___403_8457.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___403_8457.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___403_8457.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___403_8457.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___403_8457.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___403_8457.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___403_8457.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___403_8457.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___403_8457.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___403_8457.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___403_8457.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___403_8457.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___403_8457.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___403_8457.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___403_8457.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___403_8457.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___403_8457.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___403_8457.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___403_8457.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___403_8457.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___403_8457.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___403_8457.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___403_8457.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___403_8457.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___403_8457.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___403_8457.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___403_8457.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___403_8457.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___403_8457.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___403_8457.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___403_8457.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8448 with
                          | (t2,lcomp,g) ->
                              let uu____8467 =
                                (let uu____8470 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8470) ||
                                  (let uu____8472 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8472)
                                 in
                              if uu____8467
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8485 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8485
                                   (fun uu____8505  ->
                                      match uu____8505 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8522  ->
                                                let uu____8523 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8524 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8523 uu____8524);
                                           (let uu____8525 =
                                              let uu____8528 =
                                                let uu____8529 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8529 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8528 opts
                                               in
                                            bind uu____8525
                                              (fun uu____8536  ->
                                                 let uu____8537 =
                                                   bind rewriter
                                                     (fun uu____8551  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8557  ->
                                                             let uu____8558 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8559 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8558
                                                               uu____8559);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8537)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8600 =
        bind get
          (fun ps  ->
             let uu____8610 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8610 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8647  ->
                       let uu____8648 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8648);
                  bind dismiss_all
                    (fun uu____8651  ->
                       let uu____8652 =
                         let uu____8659 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8659
                           keepGoing gt1
                          in
                       bind uu____8652
                         (fun uu____8671  ->
                            match uu____8671 with
                            | (gt',uu____8679) ->
                                (log ps
                                   (fun uu____8683  ->
                                      let uu____8684 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8684);
                                 (let uu____8685 = push_goals gs  in
                                  bind uu____8685
                                    (fun uu____8690  ->
                                       let uu____8691 =
                                         let uu____8694 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8694]  in
                                       add_goals uu____8691)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8600
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8717 =
        bind get
          (fun ps  ->
             let uu____8727 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8727 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8764  ->
                       let uu____8765 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8765);
                  bind dismiss_all
                    (fun uu____8768  ->
                       let uu____8769 =
                         let uu____8772 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8772 gt1
                          in
                       bind uu____8769
                         (fun gt'  ->
                            log ps
                              (fun uu____8780  ->
                                 let uu____8781 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8781);
                            (let uu____8782 = push_goals gs  in
                             bind uu____8782
                               (fun uu____8787  ->
                                  let uu____8788 =
                                    let uu____8791 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8791]  in
                                  add_goals uu____8788))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8717
  
let (trefl : unit -> unit tac) =
  fun uu____8802  ->
    let uu____8805 =
      let uu____8808 = cur_goal ()  in
      bind uu____8808
        (fun g  ->
           let uu____8826 =
             let uu____8831 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8831  in
           match uu____8826 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8839 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8839 with
                | (hd1,args) ->
                    let uu____8878 =
                      let uu____8891 =
                        let uu____8892 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8892.FStar_Syntax_Syntax.n  in
                      (uu____8891, args)  in
                    (match uu____8878 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8906::(l,uu____8908)::(r,uu____8910)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8957 =
                           let uu____8960 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8960 l r  in
                         bind uu____8957
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____8967 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8967 l
                                    in
                                 let r1 =
                                   let uu____8969 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8969 r
                                    in
                                 let uu____8970 =
                                   let uu____8973 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____8973 l1 r1  in
                                 bind uu____8970
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____8979 =
                                           let uu____8980 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8980 l1  in
                                         let uu____8981 =
                                           let uu____8982 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8982 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____8979 uu____8981))))
                     | (hd2,uu____8984) ->
                         let uu____9001 =
                           let uu____9002 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9002 t  in
                         fail1 "trefl: not an equality (%s)" uu____9001))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8805
  
let (dup : unit -> unit tac) =
  fun uu____9015  ->
    let uu____9018 = cur_goal ()  in
    bind uu____9018
      (fun g  ->
         let uu____9024 =
           let uu____9031 = FStar_Tactics_Types.goal_env g  in
           let uu____9032 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9031 uu____9032  in
         bind uu____9024
           (fun uu____9041  ->
              match uu____9041 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___404_9051 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___404_9051.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___404_9051.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___404_9051.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9054  ->
                       let uu____9055 =
                         let uu____9058 = FStar_Tactics_Types.goal_env g  in
                         let uu____9059 =
                           let uu____9060 =
                             let uu____9061 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9062 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9061
                               uu____9062
                              in
                           let uu____9063 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9064 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9060 uu____9063 u
                             uu____9064
                            in
                         add_irrelevant_goal "dup equation" uu____9058
                           uu____9059 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9055
                         (fun uu____9067  ->
                            let uu____9068 = add_goals [g']  in
                            bind uu____9068 (fun uu____9072  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9079  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___405_9096 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___405_9096.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___405_9096.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___405_9096.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___405_9096.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___405_9096.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___405_9096.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___405_9096.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___405_9096.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___405_9096.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___405_9096.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___405_9096.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____9097 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9106  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___406_9119 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___406_9119.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___406_9119.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___406_9119.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___406_9119.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___406_9119.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___406_9119.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___406_9119.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___406_9119.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___406_9119.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___406_9119.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___406_9119.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9126  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9133 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9153 =
      let uu____9160 = cur_goal ()  in
      bind uu____9160
        (fun g  ->
           let uu____9170 =
             let uu____9179 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9179 t  in
           bind uu____9170
             (fun uu____9207  ->
                match uu____9207 with
                | (t1,typ,guard) ->
                    let uu____9223 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9223 with
                     | (hd1,args) ->
                         let uu____9272 =
                           let uu____9287 =
                             let uu____9288 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9288.FStar_Syntax_Syntax.n  in
                           (uu____9287, args)  in
                         (match uu____9272 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9309)::(q,uu____9311)::[]) when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.or_lid
                              ->
                              let v_p =
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None p
                                 in
                              let v_q =
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None q
                                 in
                              let g1 =
                                let uu____9365 =
                                  let uu____9366 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9366
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9365
                                 in
                              let g2 =
                                let uu____9368 =
                                  let uu____9369 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9369
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9368
                                 in
                              bind __dismiss
                                (fun uu____9376  ->
                                   let uu____9377 = add_goals [g1; g2]  in
                                   bind uu____9377
                                     (fun uu____9386  ->
                                        let uu____9387 =
                                          let uu____9392 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9393 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9392, uu____9393)  in
                                        ret uu____9387))
                          | uu____9398 ->
                              let uu____9413 =
                                let uu____9414 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9414 typ  in
                              fail1 "Not a disjunction: %s" uu____9413))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9153
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9444 =
      let uu____9447 = cur_goal ()  in
      bind uu____9447
        (fun g  ->
           FStar_Options.push ();
           (let uu____9460 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9460);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___407_9467 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___407_9467.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___407_9467.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___407_9467.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9444
  
let (top_env : unit -> env tac) =
  fun uu____9479  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9492  ->
    let uu____9495 = cur_goal ()  in
    bind uu____9495
      (fun g  ->
         let uu____9501 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9501)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9510  ->
    let uu____9513 = cur_goal ()  in
    bind uu____9513
      (fun g  ->
         let uu____9519 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9519)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9528  ->
    let uu____9531 = cur_goal ()  in
    bind uu____9531
      (fun g  ->
         let uu____9537 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9537)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9546  ->
    let uu____9549 = cur_env ()  in
    bind uu____9549
      (fun e  ->
         let uu____9555 =
           (FStar_Options.lax ()) || e.FStar_TypeChecker_Env.lax  in
         ret uu____9555)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9570 =
        mlog
          (fun uu____9575  ->
             let uu____9576 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9576)
          (fun uu____9579  ->
             let uu____9580 = cur_goal ()  in
             bind uu____9580
               (fun goal  ->
                  let env =
                    let uu____9588 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9588 ty  in
                  let uu____9589 = __tc env tm  in
                  bind uu____9589
                    (fun uu____9608  ->
                       match uu____9608 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9622  ->
                                let uu____9623 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9623)
                             (fun uu____9625  ->
                                mlog
                                  (fun uu____9628  ->
                                     let uu____9629 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9629)
                                  (fun uu____9632  ->
                                     let uu____9633 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9633
                                       (fun uu____9637  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9570
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9660 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9666 =
              let uu____9673 =
                let uu____9674 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9674
                 in
              new_uvar "uvar_env.2" env uu____9673  in
            bind uu____9666
              (fun uu____9690  ->
                 match uu____9690 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9660
        (fun typ  ->
           let uu____9702 = new_uvar "uvar_env" env typ  in
           bind uu____9702
             (fun uu____9716  -> match uu____9716 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9734 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9753 -> g.FStar_Tactics_Types.opts
             | uu____9756 -> FStar_Options.peek ()  in
           let uu____9759 = FStar_Syntax_Util.head_and_args t  in
           match uu____9759 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9779);
                FStar_Syntax_Syntax.pos = uu____9780;
                FStar_Syntax_Syntax.vars = uu____9781;_},uu____9782)
               ->
               let env1 =
                 let uu___408_9824 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___408_9824.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___408_9824.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___408_9824.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___408_9824.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___408_9824.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___408_9824.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___408_9824.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___408_9824.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___408_9824.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___408_9824.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___408_9824.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___408_9824.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___408_9824.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___408_9824.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___408_9824.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___408_9824.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___408_9824.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___408_9824.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___408_9824.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___408_9824.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___408_9824.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___408_9824.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___408_9824.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___408_9824.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___408_9824.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___408_9824.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___408_9824.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___408_9824.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___408_9824.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___408_9824.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___408_9824.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___408_9824.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___408_9824.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___408_9824.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___408_9824.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___408_9824.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___408_9824.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___408_9824.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___408_9824.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___408_9824.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___408_9824.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9826 =
                 let uu____9829 = bnorm_goal g  in [uu____9829]  in
               add_goals uu____9826
           | uu____9830 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9734
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9879 = if b then t2 else ret false  in
             bind uu____9879 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9890 = trytac comp  in
      bind uu____9890
        (fun uu___345_9898  ->
           match uu___345_9898 with
           | FStar_Pervasives_Native.Some (true ) -> ret true
           | FStar_Pervasives_Native.Some (false ) -> failwith "impossible"
           | FStar_Pervasives_Native.None  -> ret false)
  
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun e  ->
    fun t1  ->
      fun t2  ->
        let uu____9924 =
          bind get
            (fun ps  ->
               let uu____9930 = __tc e t1  in
               bind uu____9930
                 (fun uu____9950  ->
                    match uu____9950 with
                    | (t11,ty1,g1) ->
                        let uu____9962 = __tc e t2  in
                        bind uu____9962
                          (fun uu____9982  ->
                             match uu____9982 with
                             | (t21,ty2,g2) ->
                                 let uu____9994 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____9994
                                   (fun uu____9999  ->
                                      let uu____10000 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10000
                                        (fun uu____10006  ->
                                           let uu____10007 =
                                             do_unify e ty1 ty2  in
                                           let uu____10010 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10007 uu____10010)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9924
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10043  ->
             let uu____10044 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10044
             then
               let s =
                 FStar_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input)
                  in
               ret s
             else
               fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
  
let (fresh_bv_named :
  Prims.string -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.bv tac) =
  fun nm  ->
    fun t  ->
      bind idtac
        (fun uu____10065  ->
           let uu____10066 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10066)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10076 =
      mlog
        (fun uu____10081  ->
           let uu____10082 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10082)
        (fun uu____10085  ->
           let uu____10086 = cur_goal ()  in
           bind uu____10086
             (fun g  ->
                let uu____10092 =
                  let uu____10101 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10101 ty  in
                bind uu____10092
                  (fun uu____10113  ->
                     match uu____10113 with
                     | (ty1,uu____10123,guard) ->
                         let uu____10125 =
                           let uu____10128 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10128 guard  in
                         bind uu____10125
                           (fun uu____10131  ->
                              let uu____10132 =
                                let uu____10135 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10136 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10135 uu____10136 ty1  in
                              bind uu____10132
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10142 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10142
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.Reify;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.Primops;
                                        FStar_TypeChecker_Env.Simplify;
                                        FStar_TypeChecker_Env.UnfoldTac;
                                        FStar_TypeChecker_Env.Unmeta]  in
                                      let ng =
                                        let uu____10148 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10149 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10148
                                          uu____10149
                                         in
                                      let nty =
                                        let uu____10151 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10151 ty1  in
                                      let uu____10152 =
                                        let uu____10155 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10155 ng nty  in
                                      bind uu____10152
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10161 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10161
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10076
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10224 =
      let uu____10233 = cur_goal ()  in
      bind uu____10233
        (fun g  ->
           let uu____10245 =
             let uu____10254 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10254 s_tm  in
           bind uu____10245
             (fun uu____10272  ->
                match uu____10272 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10290 =
                      let uu____10293 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10293 guard  in
                    bind uu____10290
                      (fun uu____10305  ->
                         let uu____10306 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10306 with
                         | (h,args) ->
                             let uu____10351 =
                               let uu____10358 =
                                 let uu____10359 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10359.FStar_Syntax_Syntax.n  in
                               match uu____10358 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10374;
                                      FStar_Syntax_Syntax.vars = uu____10375;_},us)
                                   -> ret (fv, us)
                               | uu____10385 -> fail "type is not an fv"  in
                             bind uu____10351
                               (fun uu____10405  ->
                                  match uu____10405 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10421 =
                                        let uu____10424 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10424 t_lid
                                         in
                                      (match uu____10421 with
                                       | FStar_Pervasives_Native.None  ->
                                           fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid,t_us,t_ps,t_ty,mut,c_lids)
                                                ->
                                                failwhen
                                                  ((FStar_List.length a_us)
                                                     <>
                                                     (FStar_List.length t_us))
                                                  "t_us don't match?"
                                                  (fun uu____10473  ->
                                                     let uu____10474 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10474 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10489 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10517
                                                                  =
                                                                  let uu____10520
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10520
                                                                    c_lid
                                                                   in
                                                                match uu____10517
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail
                                                                    "ctor not found?"
                                                                | FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (
                                                                    match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    (_c_lid,c_us,c_ty,_t_lid,nparam,mut1)
                                                                    ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor)
                                                                     in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____10590
                                                                     ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us
                                                                     in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty
                                                                     in
                                                                    let uu____10595
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10595
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10618
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10618
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____10661
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____10661
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____10734
                                                                    =
                                                                    let uu____10735
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____10735
                                                                     in
                                                                    failwhen
                                                                    uu____10734
                                                                    "not total?"
                                                                    (fun
                                                                    uu____10752
                                                                     ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    }  in
                                                                    let is_imp
                                                                    uu___346_10768
                                                                    =
                                                                    match uu___346_10768
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____10771)
                                                                    -> true
                                                                    | 
                                                                    uu____10772
                                                                    -> false
                                                                     in
                                                                    let uu____10775
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____10775
                                                                    with
                                                                    | 
                                                                    (a_ps,a_is)
                                                                    ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____10908
                                                                     ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____10970
                                                                     ->
                                                                    match uu____10970
                                                                    with
                                                                    | 
                                                                    ((bv,uu____10990),
                                                                    (t,uu____10992))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let bs2 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs1  in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11060
                                                                     ->
                                                                    match uu____11060
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11086),
                                                                    (t,uu____11088))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11143
                                                                     ->
                                                                    match uu____11143
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs2
                                                                     in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2
                                                                     in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats))
                                                                     in
                                                                    let env =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g  in
                                                                    let equ =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env s_ty
                                                                     in
                                                                    let uu____11193
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___409_11210
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___409_11210.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11193
                                                                    with
                                                                    | 
                                                                    (uu____11223,uu____11224,uu____11225,pat_t,uu____11227,uu____11228)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11234
                                                                    =
                                                                    let uu____11235
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11235
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11234
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11239
                                                                    =
                                                                    let uu____11248
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11248]
                                                                     in
                                                                    let uu____11267
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11239
                                                                    uu____11267
                                                                     in
                                                                    let nty =
                                                                    let uu____11273
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11273
                                                                     in
                                                                    let uu____11276
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11276
                                                                    (fun
                                                                    uu____11305
                                                                     ->
                                                                    match uu____11305
                                                                    with
                                                                    | 
                                                                    (uvt,uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false  in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs2
                                                                     in
                                                                    let brt1
                                                                    =
                                                                    let uu____11331
                                                                    =
                                                                    let uu____11342
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11342]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11331
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11378
                                                                    =
                                                                    let uu____11389
                                                                    =
                                                                    let uu____11394
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11394)
                                                                     in
                                                                    (g', br,
                                                                    uu____11389)
                                                                     in
                                                                    ret
                                                                    uu____11378))))))
                                                                    | 
                                                                    uu____11415
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10489
                                                           (fun goal_brs  ->
                                                              let uu____11464
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11464
                                                              with
                                                              | (goals,brs,infos)
                                                                  ->
                                                                  let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
                                                                  let uu____11537
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11537
                                                                    (
                                                                    fun
                                                                    uu____11548
                                                                     ->
                                                                    let uu____11549
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____11549
                                                                    (fun
                                                                    uu____11559
                                                                     ->
                                                                    ret infos))))
                                            | uu____11566 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10224
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11611::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____11639 = init xs  in x :: uu____11639
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____11651 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____11659) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____11724 = last args  in
          (match uu____11724 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____11754 =
                 let uu____11755 =
                   let uu____11760 =
                     let uu____11761 =
                       let uu____11766 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____11766  in
                     uu____11761 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____11760, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____11755  in
               FStar_All.pipe_left ret uu____11754)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____11779,uu____11780) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____11832 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____11832 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____11873 =
                      let uu____11874 =
                        let uu____11879 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____11879)  in
                      FStar_Reflection_Data.Tv_Abs uu____11874  in
                    FStar_All.pipe_left ret uu____11873))
      | FStar_Syntax_Syntax.Tm_type uu____11882 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____11906 ->
          let uu____11921 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____11921 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____11951 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____11951 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12004 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12016 =
            let uu____12017 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12017  in
          FStar_All.pipe_left ret uu____12016
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12038 =
            let uu____12039 =
              let uu____12044 =
                let uu____12045 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12045  in
              (uu____12044, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12039  in
          FStar_All.pipe_left ret uu____12038
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12079 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12084 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12084 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12137 ->
                            failwith
                              "impossible: open_term returned different amount of binders"
                         in
                      FStar_All.pipe_left ret
                        (FStar_Reflection_Data.Tv_Let
                           (false, (FStar_Pervasives_Native.fst b1),
                             (lb.FStar_Syntax_Syntax.lbdef), t22))))
      | FStar_Syntax_Syntax.Tm_let ((true ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12171 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12175 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12175 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12195 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12199 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12253 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12253
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12272 =
                  let uu____12279 =
                    FStar_List.map
                      (fun uu____12291  ->
                         match uu____12291 with
                         | (p1,uu____12299) -> inspect_pat p1) ps
                     in
                  (fv, uu____12279)  in
                FStar_Reflection_Data.Pat_Cons uu____12272
            | FStar_Syntax_Syntax.Pat_var bv ->
                FStar_Reflection_Data.Pat_Var bv
            | FStar_Syntax_Syntax.Pat_wild bv ->
                FStar_Reflection_Data.Pat_Wild bv
            | FStar_Syntax_Syntax.Pat_dot_term (bv,t4) ->
                FStar_Reflection_Data.Pat_Dot_Term (bv, t4)
             in
          let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
          let brs2 =
            FStar_List.map
              (fun uu___347_12393  ->
                 match uu___347_12393 with
                 | (pat,uu____12415,t4) ->
                     let uu____12433 = inspect_pat pat  in (uu____12433, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12442 ->
          ((let uu____12444 =
              let uu____12449 =
                let uu____12450 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____12451 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12450 uu____12451
                 in
              (FStar_Errors.Warning_CantInspect, uu____12449)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____12444);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____11651
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12464 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12464
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12468 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12468
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12472 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12472
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12479 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12479
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12504 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12504
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12521 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12521
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12540 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12540
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12544 =
          let uu____12545 =
            let uu____12552 =
              let uu____12553 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12553  in
            FStar_Syntax_Syntax.mk uu____12552  in
          uu____12545 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12544
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12561 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12561
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12570 =
          let uu____12571 =
            let uu____12578 =
              let uu____12579 =
                let uu____12592 =
                  let uu____12595 =
                    let uu____12596 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____12596]  in
                  FStar_Syntax_Subst.close uu____12595 t2  in
                ((false, [lb]), uu____12592)  in
              FStar_Syntax_Syntax.Tm_let uu____12579  in
            FStar_Syntax_Syntax.mk uu____12578  in
          uu____12571 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12570
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12636 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____12636 with
         | (lbs,body) ->
             let uu____12651 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____12651)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____12685 =
                let uu____12686 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____12686  in
              FStar_All.pipe_left wrap uu____12685
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____12693 =
                let uu____12694 =
                  let uu____12707 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____12723 = pack_pat p1  in
                         (uu____12723, false)) ps
                     in
                  (fv, uu____12707)  in
                FStar_Syntax_Syntax.Pat_cons uu____12694  in
              FStar_All.pipe_left wrap uu____12693
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv,t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1))
           in
        let brs1 =
          FStar_List.map
            (fun uu___348_12769  ->
               match uu___348_12769 with
               | (pat,t1) ->
                   let uu____12786 = pack_pat pat  in
                   (uu____12786, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____12834 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12834
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____12862 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12862
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____12908 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12908
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____12947 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12947
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____12968 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____12968 with
      | (u,ctx_uvars,g_u) ->
          let uu____13000 = FStar_List.hd ctx_uvars  in
          (match uu____13000 with
           | (ctx_uvar,uu____13014) ->
               let g =
                 let uu____13016 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13016 false
                  in
               (g, g_u))
  
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun rng  ->
    fun env  ->
      fun typ  ->
        let uu____13036 = goal_of_goal_ty env typ  in
        match uu____13036 with
        | (g,g_u) ->
            let ps =
              let uu____13048 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              {
                FStar_Tactics_Types.main_context = env;
                FStar_Tactics_Types.main_goal = g;
                FStar_Tactics_Types.all_implicits =
                  (g_u.FStar_TypeChecker_Env.implicits);
                FStar_Tactics_Types.goals = [g];
                FStar_Tactics_Types.smt_goals = [];
                FStar_Tactics_Types.depth = (Prims.parse_int "0");
                FStar_Tactics_Types.__dump =
                  (fun ps  -> fun msg  -> dump_proofstate ps msg);
                FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = (Prims.parse_int "0");
                FStar_Tactics_Types.tac_verb_dbg = uu____13048
              }  in
            let uu____13053 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13053)
  