open Prims
type step =
  | Beta
  | Iota
  | Zeta
  | Exclude of step
  | Weak
  | HNF
  | Primops
  | Eager_unfolding
  | Inlining
  | NoDeltaSteps
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth
  | UnfoldOnly of FStar_Ident.lid Prims.list
  | UnfoldTac
  | PureSubtermsWithinComputations
  | Simplify
  | EraseUniverses
  | AllowUnboundUniverses
  | Reify
  | CompressUvars
  | NoFullNorm
  | CheckNoUvars
  | Unmeta[@@deriving show]
let uu___is_Beta: step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____18 -> false
let uu___is_Iota: step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____22 -> false
let uu___is_Zeta: step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____26 -> false
let uu___is_Exclude: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____31 -> false
let __proj__Exclude__item___0: step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0
let uu___is_Weak: step -> Prims.bool =
  fun projectee  -> match projectee with | Weak  -> true | uu____42 -> false
let uu___is_HNF: step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____46 -> false
let uu___is_Primops: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____50 -> false
let uu___is_Eager_unfolding: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____54 -> false
let uu___is_Inlining: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____58 -> false
let uu___is_NoDeltaSteps: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____62 -> false
let uu___is_UnfoldUntil: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____67 -> false
let __proj__UnfoldUntil__item___0: step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0
let uu___is_UnfoldOnly: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____81 -> false
let __proj__UnfoldOnly__item___0: step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0
let uu___is_UnfoldTac: step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____98 -> false
let uu___is_PureSubtermsWithinComputations: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____102 -> false
let uu___is_Simplify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____106 -> false
let uu___is_EraseUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____110 -> false
let uu___is_AllowUnboundUniverses: step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____114 -> false
let uu___is_Reify: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____118 -> false
let uu___is_CompressUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____122 -> false
let uu___is_NoFullNorm: step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____126 -> false
let uu___is_CheckNoUvars: step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____130 -> false
let uu___is_Unmeta: step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____134 -> false
type steps = step Prims.list[@@deriving show]
type psc =
  {
  psc_range: FStar_Range.range;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t;}[@@deriving show]
let __proj__Mkpsc__item__psc_range: psc -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
let __proj__Mkpsc__item__psc_subst:
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
let null_psc: psc =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____168  -> []) }
let psc_range: psc -> FStar_Range.range = fun psc  -> psc.psc_range
let psc_subst: psc -> FStar_Syntax_Syntax.subst_t =
  fun psc  -> psc.psc_subst ()
type primitive_step =
  {
  name: FStar_Ident.lid;
  arity: Prims.int;
  strong_reduction_ok: Prims.bool;
  requires_binder_substitution: Prims.bool;
  interpretation:
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option;}[@@deriving
                                                                   show]
let __proj__Mkprimitive_step__item__name: primitive_step -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
let __proj__Mkprimitive_step__item__arity: primitive_step -> Prims.int =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
let __proj__Mkprimitive_step__item__strong_reduction_ok:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
let __proj__Mkprimitive_step__item__requires_binder_substitution:
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
let __proj__Mkprimitive_step__item__interpretation:
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__interpretation
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
  FStar_Pervasives_Native.tuple4
  | Univ of FStar_Syntax_Syntax.universe
  | Dummy[@@deriving show]
let uu___is_Clos: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____369 -> false
let __proj__Clos__item___0:
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Clos _0 -> _0
let uu___is_Univ: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____471 -> false
let __proj__Univ__item___0: closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0
let uu___is_Dummy: closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____482 -> false
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy:
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy)
let closure_to_string: closure -> Prims.string =
  fun uu___72_501  ->
    match uu___72_501 with
    | Clos (uu____502,t,uu____504,uu____505) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____550 -> "Univ"
    | Dummy  -> "dummy"
type cfg =
  {
  steps: steps;
  tcenv: FStar_TypeChecker_Env.env;
  delta_level: FStar_TypeChecker_Env.delta_level Prims.list;
  primitive_steps: primitive_step Prims.list;
  strong: Prims.bool;
  memoize_lazy: Prims.bool;
  normalize_pure_lets: Prims.bool;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__primitive_steps
let __proj__Mkcfg__item__strong: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__strong
let __proj__Mkcfg__item__memoize_lazy: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__memoize_lazy
let __proj__Mkcfg__item__normalize_pure_lets: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__normalize_pure_lets
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list[@@deriving show]
type stack_elt =
  | Arg of (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | MemoLazy of (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  FStar_Syntax_Syntax.memo
  | Match of (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4
  | Cfg of cfg
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_Arg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____830 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____866 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____902 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____971 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____1013 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1069 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1109 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1141 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Cfg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1177 -> false
let __proj__Cfg__item___0: stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1193 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1218 .
    'Auu____1218 ->
      FStar_Range.range -> 'Auu____1218 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1272 = FStar_ST.op_Bang r in
          match uu____1272 with
          | FStar_Pervasives_Native.Some uu____1320 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1374 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1374 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___73_1381  ->
    match uu___73_1381 with
    | Arg (c,uu____1383,uu____1384) ->
        let uu____1385 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1385
    | MemoLazy uu____1386 -> "MemoLazy"
    | Abs (uu____1393,bs,uu____1395,uu____1396,uu____1397) ->
        let uu____1402 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1402
    | UnivArgs uu____1407 -> "UnivArgs"
    | Match uu____1414 -> "Match"
    | App (uu____1421,t,uu____1423,uu____1424) ->
        let uu____1425 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1425
    | Meta (m,uu____1427) -> "Meta"
    | Let uu____1428 -> "Let"
    | Cfg uu____1437 -> "Cfg"
    | Debug (t,uu____1439) ->
        let uu____1440 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1440
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1448 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1448 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1464 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1464 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1477 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1477 then f () else ()
let is_empty: 'Auu____1481 . 'Auu____1481 Prims.list -> Prims.bool =
  fun uu___74_1487  ->
    match uu___74_1487 with | [] -> true | uu____1490 -> false
let lookup_bvar:
  'Auu____1497 'Auu____1498 .
    ('Auu____1498,'Auu____1497) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1497
  =
  fun env  ->
    fun x  ->
      try
        let uu____1522 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1522
      with
      | uu____1535 ->
          let uu____1536 =
            let uu____1537 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1537 in
          failwith uu____1536
let downgrade_ghost_effect_name:
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
let norm_universe:
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu____1574 =
            FStar_List.fold_left
              (fun uu____1600  ->
                 fun u1  ->
                   match uu____1600 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1625 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1625 with
                        | (k_u,n1) ->
                            let uu____1640 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1640
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1574 with
          | (uu____1658,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1683 =
                   let uu____1684 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1684 in
                 match uu____1683 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1702 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1711 ->
                   let uu____1712 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1712
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1718 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1727 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1736 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1743 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1743 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1760 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1760 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1768 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1776 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1776 with
                                  | (uu____1781,m) -> n1 <= m)) in
                        if uu____1768 then rest1 else us1
                    | uu____1786 -> us1)
               | uu____1791 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1795 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1795 in
        let uu____1798 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1798
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1800 = aux u in
           match uu____1800 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
let rec closure_as_term:
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____1904  ->
             let uu____1905 = FStar_Syntax_Print.tag_of_term t in
             let uu____1906 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1905
               uu____1906);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1913 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1915 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1940 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1941 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1942 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1943 ->
                  let uu____1960 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1960
                  then
                    let uu____1961 =
                      let uu____1962 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1963 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1962 uu____1963 in
                    failwith uu____1961
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1966 =
                    let uu____1967 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1967 in
                  mk uu____1966 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1974 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1974
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1976 = lookup_bvar env x in
                  (match uu____1976 with
                   | Univ uu____1979 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____1982,uu____1983) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2095 = closures_as_binders_delayed cfg env bs in
                  (match uu____2095 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2123 =
                         let uu____2124 =
                           let uu____2141 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2141) in
                         FStar_Syntax_Syntax.Tm_abs uu____2124 in
                       mk uu____2123 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2172 = closures_as_binders_delayed cfg env bs in
                  (match uu____2172 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2214 =
                    let uu____2225 =
                      let uu____2232 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2232] in
                    closures_as_binders_delayed cfg env uu____2225 in
                  (match uu____2214 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2250 =
                         let uu____2251 =
                           let uu____2258 =
                             let uu____2259 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2259
                               FStar_Pervasives_Native.fst in
                           (uu____2258, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2251 in
                       mk uu____2250 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2350 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2350
                    | FStar_Util.Inr c ->
                        let uu____2364 = close_comp cfg env c in
                        FStar_Util.Inr uu____2364 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2380 =
                    let uu____2381 =
                      let uu____2408 = closure_as_term_delayed cfg env t11 in
                      (uu____2408, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2381 in
                  mk uu____2380 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2459 =
                    let uu____2460 =
                      let uu____2467 = closure_as_term_delayed cfg env t' in
                      let uu____2470 =
                        let uu____2471 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2471 in
                      (uu____2467, uu____2470) in
                    FStar_Syntax_Syntax.Tm_meta uu____2460 in
                  mk uu____2459 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2531 =
                    let uu____2532 =
                      let uu____2539 = closure_as_term_delayed cfg env t' in
                      let uu____2542 =
                        let uu____2543 =
                          let uu____2550 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2550) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2543 in
                      (uu____2539, uu____2542) in
                    FStar_Syntax_Syntax.Tm_meta uu____2532 in
                  mk uu____2531 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2569 =
                    let uu____2570 =
                      let uu____2577 = closure_as_term_delayed cfg env t' in
                      let uu____2580 =
                        let uu____2581 =
                          let uu____2590 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2590) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2581 in
                      (uu____2577, uu____2580) in
                    FStar_Syntax_Syntax.Tm_meta uu____2570 in
                  mk uu____2569 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2603 =
                    let uu____2604 =
                      let uu____2611 = closure_as_term_delayed cfg env t' in
                      (uu____2611, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2604 in
                  mk uu____2603 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2651  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2670 =
                    let uu____2681 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2681
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2700 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___93_2712 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___93_2712.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___93_2712.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2700)) in
                  (match uu____2670 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___94_2728 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_2728.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_2728.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2739,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2798  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2823 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2823
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2843  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2865 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2865
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___95_2877 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___95_2877.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___95_2877.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___96_2878 = lb in
                    let uu____2879 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___96_2878.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___96_2878.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2879
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2909  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____2998 =
                    match uu____2998 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3053 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3074 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3134  ->
                                        fun uu____3135  ->
                                          match (uu____3134, uu____3135) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3226 =
                                                norm_pat env3 p1 in
                                              (match uu____3226 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3074 with
                               | (pats1,env3) ->
                                   ((let uu___97_3308 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___97_3308.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___98_3327 = x in
                                let uu____3328 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___98_3327.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___98_3327.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3328
                                } in
                              ((let uu___99_3342 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___99_3342.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___100_3353 = x in
                                let uu____3354 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___100_3353.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___100_3353.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3354
                                } in
                              ((let uu___101_3368 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___101_3368.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___102_3384 = x in
                                let uu____3385 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3384.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3384.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3385
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___103_3392 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3392.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3395 = norm_pat env1 pat in
                        (match uu____3395 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3424 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3424 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3430 =
                    let uu____3431 =
                      let uu____3454 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3454) in
                    FStar_Syntax_Syntax.Tm_match uu____3431 in
                  mk uu____3430 t1.FStar_Syntax_Syntax.pos))
and closure_as_term_delayed:
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> t
        | uu____3540 -> closure_as_term cfg env t
and closures_as_args_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> args
        | uu____3566 ->
            FStar_List.map
              (fun uu____3583  ->
                 match uu____3583 with
                 | (x,imp) ->
                     let uu____3602 = closure_as_term_delayed cfg env x in
                     (uu____3602, imp)) args
and closures_as_binders_delayed:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____3616 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3665  ->
                  fun uu____3666  ->
                    match (uu____3665, uu____3666) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___104_3736 = b in
                          let uu____3737 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___104_3736.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___104_3736.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3737
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3616 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
and close_comp:
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains CompressUvars cfg.steps)
            -> c
        | uu____3830 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3843 = closure_as_term_delayed cfg env t in
                 let uu____3844 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3843 uu____3844
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3857 = closure_as_term_delayed cfg env t in
                 let uu____3858 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3857 uu____3858
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___75_3884  ->
                           match uu___75_3884 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3888 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3888
                           | f -> f)) in
                 let uu____3892 =
                   let uu___105_3893 = c1 in
                   let uu____3894 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3894;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___105_3893.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3892)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___76_3904  ->
            match uu___76_3904 with
            | FStar_Syntax_Syntax.DECREASES uu____3905 -> false
            | uu____3908 -> true))
and close_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___77_3926  ->
                      match uu___77_3926 with
                      | FStar_Syntax_Syntax.DECREASES uu____3927 -> false
                      | uu____3930 -> true)) in
            let rc1 =
              let uu___106_3932 = rc in
              let uu____3933 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___106_3932.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3933;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3940 -> lopt
let built_in_primitive_steps: primitive_step Prims.list =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe in
  let arg_as_list a u a =
    let uu____4025 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4025 in
  let arg_as_bounded_int uu____4053 =
    match uu____4053 with
    | (a,uu____4065) ->
        let uu____4072 =
          let uu____4073 = FStar_Syntax_Subst.compress a in
          uu____4073.FStar_Syntax_Syntax.n in
        (match uu____4072 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4083;
                FStar_Syntax_Syntax.vars = uu____4084;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4086;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4087;_},uu____4088)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4127 =
               let uu____4132 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4132) in
             FStar_Pervasives_Native.Some uu____4127
         | uu____4137 -> FStar_Pervasives_Native.None) in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4177 = f a in FStar_Pervasives_Native.Some uu____4177
    | uu____4178 -> FStar_Pervasives_Native.None in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4226 = f a0 a1 in FStar_Pervasives_Native.Some uu____4226
    | uu____4227 -> FStar_Pervasives_Native.None in
  let unary_op a413 a414 a415 a416 a417 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4269 = FStar_List.map as_a args in
                  lift_unary () ()
                    (fun a412  -> (Obj.magic (f res.psc_range)) a412)
                    uu____4269)) a413 a414 a415 a416 a417 in
  let binary_op a420 a421 a422 a423 a424 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4318 = FStar_List.map as_a args in
                  lift_binary () ()
                    (fun a418  ->
                       fun a419  -> (Obj.magic (f res.psc_range)) a418 a419)
                    uu____4318)) a420 a421 a422 a423 a424 in
  let as_primitive_step uu____4342 =
    match uu____4342 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        } in
  let unary_int_op f =
    unary_op () (fun a425  -> (Obj.magic arg_as_int) a425)
      (fun a426  ->
         fun a427  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4390 = f x in
                   FStar_Syntax_Embeddings.embed_int r uu____4390)) a426 a427) in
  let binary_int_op f =
    binary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           fun a431  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4418 = f x y in
                       FStar_Syntax_Embeddings.embed_int r uu____4418)) a429
               a430 a431) in
  let unary_bool_op f =
    unary_op () (fun a432  -> (Obj.magic arg_as_bool) a432)
      (fun a433  ->
         fun a434  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4439 = f x in
                   FStar_Syntax_Embeddings.embed_bool r uu____4439)) a433
             a434) in
  let binary_bool_op f =
    binary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           fun a438  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4467 = f x y in
                       FStar_Syntax_Embeddings.embed_bool r uu____4467)) a436
               a437 a438) in
  let binary_string_op f =
    binary_op () (fun a439  -> (Obj.magic arg_as_string) a439)
      (fun a440  ->
         fun a441  ->
           fun a442  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4495 = f x y in
                       FStar_Syntax_Embeddings.embed_string r uu____4495))
               a440 a441 a442) in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4603 =
          let uu____4612 = as_a a in
          let uu____4615 = as_b b in (uu____4612, uu____4615) in
        (match uu____4603 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4630 =
               let uu____4631 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4631 in
             FStar_Pervasives_Native.Some uu____4630
         | uu____4632 -> FStar_Pervasives_Native.None)
    | uu____4641 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4655 =
        let uu____4656 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4656 in
      mk uu____4655 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4666 =
      let uu____4669 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4669 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4666 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4701 =
      let uu____4702 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4702 in
    FStar_Syntax_Embeddings.embed_int rng uu____4701 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4720 = arg_as_string a1 in
        (match uu____4720 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4726 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2) in
             (match uu____4726 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4739 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4739
              | uu____4740 -> FStar_Pervasives_Native.None)
         | uu____4745 -> FStar_Pervasives_Native.None)
    | uu____4748 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4758 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4758 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4782 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4793 =
          let uu____4814 = arg_as_string fn in
          let uu____4817 = arg_as_int from_line in
          let uu____4820 = arg_as_int from_col in
          let uu____4823 = arg_as_int to_line in
          let uu____4826 = arg_as_int to_col in
          (uu____4814, uu____4817, uu____4820, uu____4823, uu____4826) in
        (match uu____4793 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4857 =
                 let uu____4858 = FStar_BigInt.to_int_fs from_l in
                 let uu____4859 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4858 uu____4859 in
               let uu____4860 =
                 let uu____4861 = FStar_BigInt.to_int_fs to_l in
                 let uu____4862 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4861 uu____4862 in
               FStar_Range.mk_range fn1 uu____4857 uu____4860 in
             let uu____4863 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4863
         | uu____4868 -> FStar_Pervasives_Native.None)
    | uu____4889 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4916)::(a1,uu____4918)::(a2,uu____4920)::[] ->
        let uu____4957 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4957 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4970 -> FStar_Pervasives_Native.None)
    | uu____4971 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4998)::[] -> FStar_Pervasives_Native.Some a1
    | uu____5007 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5031 =
      let uu____5046 =
        let uu____5061 =
          let uu____5076 =
            let uu____5091 =
              let uu____5106 =
                let uu____5121 =
                  let uu____5136 =
                    let uu____5151 =
                      let uu____5166 =
                        let uu____5181 =
                          let uu____5196 =
                            let uu____5211 =
                              let uu____5226 =
                                let uu____5241 =
                                  let uu____5256 =
                                    let uu____5271 =
                                      let uu____5286 =
                                        let uu____5301 =
                                          let uu____5316 =
                                            let uu____5331 =
                                              let uu____5346 =
                                                let uu____5359 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____5359,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a443  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a443)
                                                     (fun a444  ->
                                                        fun a445  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a444 a445))) in
                                              let uu____5366 =
                                                let uu____5381 =
                                                  let uu____5394 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____5394,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a446  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a446)
                                                       (fun a447  ->
                                                          fun a448  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a447 a448))) in
                                                let uu____5401 =
                                                  let uu____5416 =
                                                    let uu____5431 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____5431,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____5440 =
                                                    let uu____5457 =
                                                      let uu____5472 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____5472,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    let uu____5481 =
                                                      let uu____5498 =
                                                        let uu____5517 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"] in
                                                        (uu____5517,
                                                          (Prims.parse_int
                                                             "1"), idstep) in
                                                      [uu____5498] in
                                                    uu____5457 :: uu____5481 in
                                                  uu____5416 :: uu____5440 in
                                                uu____5381 :: uu____5401 in
                                              uu____5346 :: uu____5366 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5331 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5316 in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a449  ->
                                                (Obj.magic arg_as_string)
                                                  a449)
                                             (fun a450  ->
                                                fun a451  ->
                                                  fun a452  ->
                                                    (Obj.magic
                                                       string_compare') a450
                                                      a451 a452)))
                                          :: uu____5301 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a453  ->
                                              (Obj.magic arg_as_bool) a453)
                                           (fun a454  ->
                                              fun a455  ->
                                                (Obj.magic string_of_bool1)
                                                  a454 a455)))
                                        :: uu____5286 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a456  ->
                                            (Obj.magic arg_as_int) a456)
                                         (fun a457  ->
                                            fun a458  ->
                                              (Obj.magic string_of_int1) a457
                                                a458)))
                                      :: uu____5271 in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a459  ->
                                          (Obj.magic arg_as_int) a459)
                                       (fun a460  ->
                                          (Obj.magic arg_as_char) a460)
                                       (fun a461  ->
                                          fun a462  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a461 a462)
                                       (fun a463  ->
                                          fun a464  ->
                                            fun a465  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____5734 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu____5734 y)) a463
                                                a464 a465)))
                                    :: uu____5256 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5241 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5226 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5211 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5196 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5181 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5166 in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a466  -> (Obj.magic arg_as_int) a466)
                         (fun a467  ->
                            fun a468  ->
                              fun a469  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____5901 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____5901)) a467 a468 a469)))
                      :: uu____5151 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a470  -> (Obj.magic arg_as_int) a470)
                       (fun a471  ->
                          fun a472  ->
                            fun a473  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____5927 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____5927)) a471 a472 a473)))
                    :: uu____5136 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a474  -> (Obj.magic arg_as_int) a474)
                     (fun a475  ->
                        fun a476  ->
                          fun a477  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____5953 =
                                        FStar_BigInt.le_big_int x y in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____5953)) a475 a476 a477)))
                  :: uu____5121 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a478  -> (Obj.magic arg_as_int) a478)
                   (fun a479  ->
                      fun a480  ->
                        fun a481  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____5979 =
                                      FStar_BigInt.lt_big_int x y in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____5979)) a479 a480 a481)))
                :: uu____5106 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5091 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5076 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5061 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5046 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5031 in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6132 =
        let uu____6133 =
          let uu____6134 = FStar_Syntax_Syntax.as_arg c in [uu____6134] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6133 in
      uu____6132 FStar_Pervasives_Native.None r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____6184 =
                let uu____6197 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                (uu____6197, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                     (fun a483  ->
                        fun a484  ->
                          fun a485  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6213  ->
                                    fun uu____6214  ->
                                      match (uu____6213, uu____6214) with
                                      | ((int_to_t1,x),(uu____6233,y)) ->
                                          let uu____6243 =
                                            FStar_BigInt.add_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6243)) a483 a484 a485))) in
              let uu____6244 =
                let uu____6259 =
                  let uu____6272 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  (uu____6272, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a486  -> (Obj.magic arg_as_bounded_int) a486)
                       (fun a487  ->
                          fun a488  ->
                            fun a489  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6288  ->
                                      fun uu____6289  ->
                                        match (uu____6288, uu____6289) with
                                        | ((int_to_t1,x),(uu____6308,y)) ->
                                            let uu____6318 =
                                              FStar_BigInt.sub_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6318)) a487 a488 a489))) in
                let uu____6319 =
                  let uu____6334 =
                    let uu____6347 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    (uu____6347, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a490  -> (Obj.magic arg_as_bounded_int) a490)
                         (fun a491  ->
                            fun a492  ->
                              fun a493  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6363  ->
                                        fun uu____6364  ->
                                          match (uu____6363, uu____6364) with
                                          | ((int_to_t1,x),(uu____6383,y)) ->
                                              let uu____6393 =
                                                FStar_BigInt.mult_big_int x y in
                                              int_as_bounded r int_to_t1
                                                uu____6393)) a491 a492 a493))) in
                  let uu____6394 =
                    let uu____6409 =
                      let uu____6422 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      (uu____6422, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a494  -> (Obj.magic arg_as_bounded_int) a494)
                           (fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6434  ->
                                        match uu____6434 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a495 a496))) in
                    [uu____6409] in
                  uu____6334 :: uu____6394 in
                uu____6259 :: uu____6319 in
              uu____6184 :: uu____6244)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____6548 =
                let uu____6561 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                (uu____6561, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                     (fun a498  ->
                        fun a499  ->
                          fun a500  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6577  ->
                                    fun uu____6578  ->
                                      match (uu____6577, uu____6578) with
                                      | ((int_to_t1,x),(uu____6597,y)) ->
                                          let uu____6607 =
                                            FStar_BigInt.div_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6607)) a498 a499 a500))) in
              let uu____6608 =
                let uu____6623 =
                  let uu____6636 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  (uu____6636, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a501  -> (Obj.magic arg_as_bounded_int) a501)
                       (fun a502  ->
                          fun a503  ->
                            fun a504  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6652  ->
                                      fun uu____6653  ->
                                        match (uu____6652, uu____6653) with
                                        | ((int_to_t1,x),(uu____6672,y)) ->
                                            let uu____6682 =
                                              FStar_BigInt.mod_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6682)) a502 a503 a504))) in
                [uu____6623] in
              uu____6548 :: uu____6608)) in
    FStar_List.append add_sub_mul_v div_mod_unsigned in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6772)::(a1,uu____6774)::(a2,uu____6776)::[] ->
        let uu____6813 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6813 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6819 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6819.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6819.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6823 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6823.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6823.FStar_Syntax_Syntax.vars)
                })
         | uu____6824 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6826)::uu____6827::(a1,uu____6829)::(a2,uu____6831)::[] ->
        let uu____6880 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6880 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6886 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6886.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6886.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6890 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6890.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6890.FStar_Syntax_Syntax.vars)
                })
         | uu____6891 -> FStar_Pervasives_Native.None)
    | uu____6892 -> failwith "Unexpected number of arguments" in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    } in
  [propositional_equality; hetero_propositional_equality]
let unembed_binder:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option
  =
  fun t  ->
    try
      let uu____6911 =
        let uu____6912 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6912 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6911
    with | uu____6918 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6922 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6922) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6982  ->
           fun subst1  ->
             match uu____6982 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____7023,uu____7024)) ->
                      let uu____7083 = b in
                      (match uu____7083 with
                       | (bv,uu____7091) ->
                           let uu____7092 =
                             let uu____7093 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____7093 in
                           if uu____7092
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____7098 = unembed_binder term1 in
                              match uu____7098 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____7105 =
                                      let uu___111_7106 = bv in
                                      let uu____7107 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___111_7106.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___111_7106.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____7107
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____7105 in
                                  let b_for_x =
                                    let uu____7111 =
                                      let uu____7118 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____7118) in
                                    FStar_Syntax_Syntax.NT uu____7111 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___78_7127  ->
                                         match uu___78_7127 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____7128,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7130;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7131;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____7136 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____7137 -> subst1)) env []
let reduce_primops:
  'Auu____7154 'Auu____7155 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7155) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7154 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____7196 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7196
          then tm
          else
            (let uu____7198 = FStar_Syntax_Util.head_and_args tm in
             match uu____7198 with
             | (head1,args) ->
                 let uu____7235 =
                   let uu____7236 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7236.FStar_Syntax_Syntax.n in
                 (match uu____7235 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7240 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7240 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7257  ->
                                   let uu____7258 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7259 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7266 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7258 uu____7259 uu____7266);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7271  ->
                                   let uu____7272 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7272);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7275  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7277 =
                                 prim_step.interpretation psc args in
                               match uu____7277 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7283  ->
                                         let uu____7284 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7284);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7290  ->
                                         let uu____7291 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7292 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7291 uu____7292);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7293 ->
                           (log_primops cfg
                              (fun uu____7297  ->
                                 let uu____7298 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7298);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7302  ->
                            let uu____7303 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7303);
                       (match args with
                        | (a1,uu____7305)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7322 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7334  ->
                            let uu____7335 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7335);
                       (match args with
                        | (t,uu____7337)::(r,uu____7339)::[] ->
                            let uu____7366 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7366 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___112_7370 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___112_7370.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___112_7370.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7373 -> tm))
                  | uu____7382 -> tm))
let reduce_equality:
  'Auu____7387 'Auu____7388 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7388) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7387 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___113_7426 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___113_7426.tcenv);
           delta_level = (uu___113_7426.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___113_7426.strong);
           memoize_lazy = (uu___113_7426.memoize_lazy);
           normalize_pure_lets = (uu___113_7426.normalize_pure_lets)
         }) tm
let maybe_simplify_aux:
  'Auu____7433 'Auu____7434 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7434) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7433 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7476 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7476
          then tm1
          else
            (let w t =
               let uu___114_7488 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_7488.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_7488.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____7505 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7510 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7510
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7531 =
                 match uu____7531 with
                 | (t1,q) ->
                     let uu____7544 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7544 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7572 -> (t1, q)) in
               let uu____7581 = FStar_Syntax_Util.head_and_args t in
               match uu____7581 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg) in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____7678;
                         FStar_Syntax_Syntax.vars = uu____7679;_},uu____7680);
                    FStar_Syntax_Syntax.pos = uu____7681;
                    FStar_Syntax_Syntax.vars = uu____7682;_},args)
                 ->
                 let uu____7708 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7708
                 then
                   let uu____7709 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7709 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7764)::
                        (uu____7765,(arg,uu____7767))::[] ->
                        maybe_auto_squash arg
                    | (uu____7832,(arg,uu____7834))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7835)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7900)::uu____7901::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7964::(FStar_Pervasives_Native.Some (false
                                   ),uu____7965)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8028 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____8044 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8044
                    then
                      let uu____8045 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8045 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8100)::uu____8101::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8164::(FStar_Pervasives_Native.Some (true
                                     ),uu____8165)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8228)::
                          (uu____8229,(arg,uu____8231))::[] ->
                          maybe_auto_squash arg
                      | (uu____8296,(arg,uu____8298))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8299)::[]
                          -> maybe_auto_squash arg
                      | uu____8364 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8380 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8380
                       then
                         let uu____8381 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8381 with
                         | uu____8436::(FStar_Pervasives_Native.Some (true
                                        ),uu____8437)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8500)::uu____8501::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8564)::
                             (uu____8565,(arg,uu____8567))::[] ->
                             maybe_auto_squash arg
                         | (uu____8632,(p,uu____8634))::(uu____8635,(q,uu____8637))::[]
                             ->
                             let uu____8702 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8702
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8704 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8720 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8720
                          then
                            let uu____8721 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8721 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8776)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8815)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8854 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8870 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8870
                             then
                               match args with
                               | (t,uu____8872)::[] ->
                                   let uu____8889 =
                                     let uu____8890 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8890.FStar_Syntax_Syntax.n in
                                   (match uu____8889 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8893::[],body,uu____8895) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8922 -> tm1)
                                    | uu____8925 -> tm1)
                               | (uu____8926,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8927))::
                                   (t,uu____8929)::[] ->
                                   let uu____8968 =
                                     let uu____8969 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8969.FStar_Syntax_Syntax.n in
                                   (match uu____8968 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8972::[],body,uu____8974) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____9001 -> tm1)
                                    | uu____9004 -> tm1)
                               | uu____9005 -> tm1
                             else
                               (let uu____9015 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____9015
                                then
                                  match args with
                                  | (t,uu____9017)::[] ->
                                      let uu____9034 =
                                        let uu____9035 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9035.FStar_Syntax_Syntax.n in
                                      (match uu____9034 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9038::[],body,uu____9040)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9067 -> tm1)
                                       | uu____9070 -> tm1)
                                  | (uu____9071,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9072))::(t,uu____9074)::[] ->
                                      let uu____9113 =
                                        let uu____9114 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9114.FStar_Syntax_Syntax.n in
                                      (match uu____9113 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9117::[],body,uu____9119)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9146 -> tm1)
                                       | uu____9149 -> tm1)
                                  | uu____9150 -> tm1
                                else
                                  (let uu____9160 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____9160
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9161;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9162;_},uu____9163)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9180;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9181;_},uu____9182)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____9199 -> tm1
                                   else
                                     (let uu____9209 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____9209 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____9229 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9239;
                    FStar_Syntax_Syntax.vars = uu____9240;_},args)
                 ->
                 let uu____9262 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9262
                 then
                   let uu____9263 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9263 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9318)::
                        (uu____9319,(arg,uu____9321))::[] ->
                        maybe_auto_squash arg
                    | (uu____9386,(arg,uu____9388))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9389)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9454)::uu____9455::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9518::(FStar_Pervasives_Native.Some (false
                                   ),uu____9519)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9582 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9598 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9598
                    then
                      let uu____9599 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9599 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9654)::uu____9655::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9718::(FStar_Pervasives_Native.Some (true
                                     ),uu____9719)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9782)::
                          (uu____9783,(arg,uu____9785))::[] ->
                          maybe_auto_squash arg
                      | (uu____9850,(arg,uu____9852))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9853)::[]
                          -> maybe_auto_squash arg
                      | uu____9918 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9934 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9934
                       then
                         let uu____9935 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9935 with
                         | uu____9990::(FStar_Pervasives_Native.Some (true
                                        ),uu____9991)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10054)::uu____10055::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10118)::
                             (uu____10119,(arg,uu____10121))::[] ->
                             maybe_auto_squash arg
                         | (uu____10186,(p,uu____10188))::(uu____10189,
                                                           (q,uu____10191))::[]
                             ->
                             let uu____10256 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10256
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10258 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10274 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10274
                          then
                            let uu____10275 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10275 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10330)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10369)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10408 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10424 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10424
                             then
                               match args with
                               | (t,uu____10426)::[] ->
                                   let uu____10443 =
                                     let uu____10444 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10444.FStar_Syntax_Syntax.n in
                                   (match uu____10443 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10447::[],body,uu____10449) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10476 -> tm1)
                                    | uu____10479 -> tm1)
                               | (uu____10480,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10481))::
                                   (t,uu____10483)::[] ->
                                   let uu____10522 =
                                     let uu____10523 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10523.FStar_Syntax_Syntax.n in
                                   (match uu____10522 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10526::[],body,uu____10528) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10555 -> tm1)
                                    | uu____10558 -> tm1)
                               | uu____10559 -> tm1
                             else
                               (let uu____10569 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10569
                                then
                                  match args with
                                  | (t,uu____10571)::[] ->
                                      let uu____10588 =
                                        let uu____10589 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10589.FStar_Syntax_Syntax.n in
                                      (match uu____10588 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10592::[],body,uu____10594)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10621 -> tm1)
                                       | uu____10624 -> tm1)
                                  | (uu____10625,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10626))::(t,uu____10628)::[] ->
                                      let uu____10667 =
                                        let uu____10668 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10668.FStar_Syntax_Syntax.n in
                                      (match uu____10667 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10671::[],body,uu____10673)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10700 -> tm1)
                                       | uu____10703 -> tm1)
                                  | uu____10704 -> tm1
                                else
                                  (let uu____10714 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10714
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10715;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10716;_},uu____10717)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10734;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10735;_},uu____10736)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10753 -> tm1
                                   else
                                     (let uu____10763 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10763 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10783 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10792 -> tm1)
let maybe_simplify:
  'Auu____10799 'Auu____10800 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10800) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10799 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10843 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10843
           then
             let uu____10844 = FStar_Syntax_Print.term_to_string tm in
             let uu____10845 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10844 uu____10845
           else ());
          tm'
let is_norm_request:
  'Auu____10851 .
    FStar_Syntax_Syntax.term -> 'Auu____10851 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10864 =
        let uu____10871 =
          let uu____10872 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10872.FStar_Syntax_Syntax.n in
        (uu____10871, args) in
      match uu____10864 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10878::uu____10879::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10883::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10888::uu____10889::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10892 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___79_10903  ->
    match uu___79_10903 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10909 =
          let uu____10912 =
            let uu____10913 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10913 in
          [uu____10912] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10909
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10928 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10928) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10966 =
          let uu____10969 =
            let uu____10974 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10974 s in
          FStar_All.pipe_right uu____10969 FStar_Util.must in
        FStar_All.pipe_right uu____10966 tr_norm_steps in
      match args with
      | uu____10999::(tm,uu____11001)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____11024)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____11039)::uu____11040::(tm,uu____11042)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____11082 =
              let uu____11085 = full_norm steps in parse_steps uu____11085 in
            Beta :: uu____11082 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____11094 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___80_11111  ->
    match uu___80_11111 with
    | (App
        (uu____11114,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11115;
                       FStar_Syntax_Syntax.vars = uu____11116;_},uu____11117,uu____11118))::uu____11119
        -> true
    | uu____11126 -> false
let firstn:
  'Auu____11132 .
    Prims.int ->
      'Auu____11132 Prims.list ->
        ('Auu____11132 Prims.list,'Auu____11132 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let should_reify: cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____11168,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11169;
                         FStar_Syntax_Syntax.vars = uu____11170;_},uu____11171,uu____11172))::uu____11173
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____11180 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11327  ->
               let uu____11328 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11329 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11330 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11337 =
                 let uu____11338 =
                   let uu____11341 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11341 in
                 stack_to_string uu____11338 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11328 uu____11329 uu____11330 uu____11337);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11364 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11389 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11406 =
                 let uu____11407 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11408 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11407 uu____11408 in
               failwith uu____11406
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11409 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11426 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11427 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11428;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11429;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11432;
                 FStar_Syntax_Syntax.fv_delta = uu____11433;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11434;
                 FStar_Syntax_Syntax.fv_delta = uu____11435;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11436);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11444 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11444 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11450  ->
                     let uu____11451 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11452 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11451 uu____11452);
                if b
                then
                  (let uu____11453 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11453 t1 fv)
                else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((FStar_Syntax_Util.is_fstar_tactics_embed hd1) ||
                  ((FStar_Syntax_Util.is_fstar_tactics_quote hd1) &&
                     (FStar_List.contains NoDeltaSteps cfg.steps)))
                 || (FStar_Syntax_Util.is_fstar_tactics_by_tactic hd1)
               ->
               let args1 = closures_as_args_delayed cfg env args in
               let hd2 = closure_as_term cfg env hd1 in
               let t2 =
                 let uu___115_11492 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___115_11492.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___115_11492.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11525 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11525) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___116_11533 = cfg in
                 let uu____11534 =
                   FStar_List.filter
                     (fun uu___81_11537  ->
                        match uu___81_11537 with
                        | UnfoldOnly uu____11538 -> false
                        | NoDeltaSteps  -> false
                        | uu____11541 -> true) cfg.steps in
                 {
                   steps = uu____11534;
                   tcenv = (uu___116_11533.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___116_11533.primitive_steps);
                   strong = (uu___116_11533.strong);
                   memoize_lazy = (uu___116_11533.memoize_lazy);
                   normalize_pure_lets = (uu___116_11533.normalize_pure_lets)
                 } in
               let uu____11542 = get_norm_request (norm cfg' env []) args in
               (match uu____11542 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11558 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___82_11563  ->
                                match uu___82_11563 with
                                | UnfoldUntil uu____11564 -> true
                                | UnfoldOnly uu____11565 -> true
                                | uu____11568 -> false)) in
                      if uu____11558
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___117_11573 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___117_11573.tcenv);
                        delta_level;
                        primitive_steps = (uu___117_11573.primitive_steps);
                        strong = (uu___117_11573.strong);
                        memoize_lazy = (uu___117_11573.memoize_lazy);
                        normalize_pure_lets =
                          (uu___117_11573.normalize_pure_lets)
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11580 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11580
                      then
                        let uu____11583 =
                          let uu____11584 =
                            let uu____11589 = FStar_Util.now () in
                            (t1, uu____11589) in
                          Debug uu____11584 in
                        uu____11583 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11593 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11593
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11600 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11600
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11603 =
                      let uu____11610 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11610, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11603 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___83_11623  ->
                         match uu___83_11623 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11626 =
                   (FStar_List.mem FStar_TypeChecker_Env.UnfoldTac
                      cfg.delta_level)
                     &&
                     ((((((((((FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Parser_Const.and_lid)
                                ||
                                (FStar_Syntax_Syntax.fv_eq_lid f
                                   FStar_Parser_Const.or_lid))
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid f
                                  FStar_Parser_Const.imp_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid f
                                 FStar_Parser_Const.forall_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid f
                                FStar_Parser_Const.squash_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid f
                               FStar_Parser_Const.exists_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid f
                              FStar_Parser_Const.eq2_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid f
                             FStar_Parser_Const.eq3_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid f
                            FStar_Parser_Const.true_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid f
                           FStar_Parser_Const.false_lid)) in
                 if uu____11626
                 then false
                 else
                   (let uu____11628 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___84_11635  ->
                              match uu___84_11635 with
                              | UnfoldOnly uu____11636 -> true
                              | uu____11639 -> false)) in
                    match uu____11628 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11643 -> should_delta) in
               (log cfg
                  (fun uu____11651  ->
                     let uu____11652 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11653 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11654 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11652 uu____11653 uu____11654);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11657 = lookup_bvar env x in
               (match uu____11657 with
                | Univ uu____11660 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11709 = FStar_ST.op_Bang r in
                      (match uu____11709 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11827  ->
                                 let uu____11828 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11829 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11828
                                   uu____11829);
                            (let uu____11830 =
                               let uu____11831 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11831.FStar_Syntax_Syntax.n in
                             match uu____11830 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11834 ->
                                 norm cfg env2 stack t'
                             | uu____11851 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11921)::uu____11922 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11931)::uu____11932 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11942,uu____11943))::stack_rest ->
                    (match c with
                     | Univ uu____11947 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11956 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11977  ->
                                    let uu____11978 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11978);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12018  ->
                                    let uu____12019 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12019);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     log cfg
                       (fun uu____12097  ->
                          let uu____12098 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12098);
                     norm cfg env stack1 t1)
                | (Debug uu____12099)::uu____12100 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12107 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12107
                    else
                      (let uu____12109 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12109 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12151  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12179 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12179
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12189 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12189)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12194 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12194.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12194.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12195 -> lopt in
                           (log cfg
                              (fun uu____12201  ->
                                 let uu____12202 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12202);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12211 = cfg in
                               {
                                 steps = (uu___119_12211.steps);
                                 tcenv = (uu___119_12211.tcenv);
                                 delta_level = (uu___119_12211.delta_level);
                                 primitive_steps =
                                   (uu___119_12211.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12211.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12211.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12222)::uu____12223 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12230 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12230
                    else
                      (let uu____12232 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12232 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12274  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12302 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12302
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12312 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12312)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12317 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12317.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12317.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12318 -> lopt in
                           (log cfg
                              (fun uu____12324  ->
                                 let uu____12325 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12325);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12334 = cfg in
                               {
                                 steps = (uu___119_12334.steps);
                                 tcenv = (uu___119_12334.tcenv);
                                 delta_level = (uu___119_12334.delta_level);
                                 primitive_steps =
                                   (uu___119_12334.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12334.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12334.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12345)::uu____12346 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12357 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12357
                    else
                      (let uu____12359 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12359 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12401  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12429 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12429
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12439 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12439)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12444 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12444.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12444.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12445 -> lopt in
                           (log cfg
                              (fun uu____12451  ->
                                 let uu____12452 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12452);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12461 = cfg in
                               {
                                 steps = (uu___119_12461.steps);
                                 tcenv = (uu___119_12461.tcenv);
                                 delta_level = (uu___119_12461.delta_level);
                                 primitive_steps =
                                   (uu___119_12461.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12461.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12461.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12472)::uu____12473 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12484 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12484
                    else
                      (let uu____12486 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12486 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12528  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12556 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12556
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12566 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12566)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12571 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12571.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12571.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12572 -> lopt in
                           (log cfg
                              (fun uu____12578  ->
                                 let uu____12579 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12579);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12588 = cfg in
                               {
                                 steps = (uu___119_12588.steps);
                                 tcenv = (uu___119_12588.tcenv);
                                 delta_level = (uu___119_12588.delta_level);
                                 primitive_steps =
                                   (uu___119_12588.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12588.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12588.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12599)::uu____12600 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12615 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12615
                    else
                      (let uu____12617 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12617 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12659  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12687 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12687
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12697 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12697)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12702 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12702.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12702.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12703 -> lopt in
                           (log cfg
                              (fun uu____12709  ->
                                 let uu____12710 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12710);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12719 = cfg in
                               {
                                 steps = (uu___119_12719.steps);
                                 tcenv = (uu___119_12719.tcenv);
                                 delta_level = (uu___119_12719.delta_level);
                                 primitive_steps =
                                   (uu___119_12719.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12719.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12719.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12730 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12730
                    else
                      (let uu____12732 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12732 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12774  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12802 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12802
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12812 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12812)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12817 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12817.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12817.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12818 -> lopt in
                           (log cfg
                              (fun uu____12824  ->
                                 let uu____12825 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12825);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12834 = cfg in
                               {
                                 steps = (uu___119_12834.steps);
                                 tcenv = (uu___119_12834.tcenv);
                                 delta_level = (uu___119_12834.delta_level);
                                 primitive_steps =
                                   (uu___119_12834.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12834.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___119_12834.normalize_pure_lets)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____12883  ->
                         fun stack1  ->
                           match uu____12883 with
                           | (a,aq) ->
                               let uu____12895 =
                                 let uu____12896 =
                                   let uu____12903 =
                                     let uu____12904 =
                                       let uu____12935 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12935, false) in
                                     Clos uu____12904 in
                                   (uu____12903, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12896 in
                               uu____12895 :: stack1) args) in
               (log cfg
                  (fun uu____13019  ->
                     let uu____13020 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13020);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if FStar_List.contains Weak cfg.steps
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___120_13056 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_13056.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_13056.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13057 ->
                      let uu____13062 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13062)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13065 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13065 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13096 =
                          let uu____13097 =
                            let uu____13104 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___121_13106 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_13106.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_13106.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13104) in
                          FStar_Syntax_Syntax.Tm_refine uu____13097 in
                        mk uu____13096 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13125 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____13125
               else
                 (let uu____13127 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13127 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13135 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13159  -> dummy :: env1) env) in
                        norm_comp cfg uu____13135 c1 in
                      let t2 =
                        let uu____13181 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13181 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13240)::uu____13241 ->
                    (log cfg
                       (fun uu____13252  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13253)::uu____13254 ->
                    (log cfg
                       (fun uu____13265  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13266,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13267;
                                   FStar_Syntax_Syntax.vars = uu____13268;_},uu____13269,uu____13270))::uu____13271
                    ->
                    (log cfg
                       (fun uu____13280  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13281)::uu____13282 ->
                    (log cfg
                       (fun uu____13293  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13294 ->
                    (log cfg
                       (fun uu____13297  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13301  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13318 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13318
                         | FStar_Util.Inr c ->
                             let uu____13326 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13326 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13339 =
                               let uu____13340 =
                                 let uu____13367 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13367, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13340 in
                             mk uu____13339 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13386 ->
                           let uu____13387 =
                             let uu____13388 =
                               let uu____13389 =
                                 let uu____13416 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13416, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13389 in
                             mk uu____13388 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13387))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (FStar_List.contains CompressUvars cfg.steps)
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____13526 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13526 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___122_13546 = cfg in
                               let uu____13547 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___122_13546.steps);
                                 tcenv = uu____13547;
                                 delta_level = (uu___122_13546.delta_level);
                                 primitive_steps =
                                   (uu___122_13546.primitive_steps);
                                 strong = (uu___122_13546.strong);
                                 memoize_lazy = (uu___122_13546.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___122_13546.normalize_pure_lets)
                               } in
                             let norm1 t2 =
                               let uu____13552 =
                                 let uu____13553 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13553 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13552 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___123_13556 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___123_13556.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___123_13556.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13557 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13557
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13568,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13569;
                               FStar_Syntax_Syntax.lbunivs = uu____13570;
                               FStar_Syntax_Syntax.lbtyp = uu____13571;
                               FStar_Syntax_Syntax.lbeff = uu____13572;
                               FStar_Syntax_Syntax.lbdef = uu____13573;_}::uu____13574),uu____13575)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13611 =
                 (let uu____13614 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13614) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) &&
                       cfg.normalize_pure_lets)
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (let uu____13616 =
                            FStar_All.pipe_right cfg.steps
                              (FStar_List.contains
                                 PureSubtermsWithinComputations) in
                          Prims.op_Negation uu____13616))) in
               if uu____13611
               then
                 let binder =
                   let uu____13618 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13618 in
                 let env1 =
                   let uu____13628 =
                     let uu____13635 =
                       let uu____13636 =
                         let uu____13667 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13667,
                           false) in
                       Clos uu____13636 in
                     ((FStar_Pervasives_Native.Some binder), uu____13635) in
                   uu____13628 :: env in
                 (log cfg
                    (fun uu____13760  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13762 =
                    let uu____13767 =
                      let uu____13768 =
                        let uu____13769 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13769
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13768] in
                    FStar_Syntax_Subst.open_term uu____13767 body in
                  match uu____13762 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13778  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13786 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13786 in
                          FStar_Util.Inl
                            (let uu___124_13796 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_13796.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_13796.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13799  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___125_13801 = lb in
                           let uu____13802 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___125_13801.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___125_13801.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13802
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13837  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___126_13860 = cfg in
                           {
                             steps = (uu___126_13860.steps);
                             tcenv = (uu___126_13860.tcenv);
                             delta_level = (uu___126_13860.delta_level);
                             primitive_steps =
                               (uu___126_13860.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___126_13860.memoize_lazy);
                             normalize_pure_lets =
                               (uu___126_13860.normalize_pure_lets)
                           } in
                         log cfg1
                           (fun uu____13863  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- body\n");
                         norm cfg1 env'
                           ((Let (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                           :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (FStar_List.contains CompressUvars cfg.steps) ||
                 ((FStar_List.contains (Exclude Zeta) cfg.steps) &&
                    (FStar_List.contains PureSubtermsWithinComputations
                       cfg.steps))
               ->
               let uu____13880 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13880 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13916 =
                               let uu___127_13917 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___127_13917.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___127_13917.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13916 in
                           let uu____13918 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13918 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13944 =
                                   FStar_List.map (fun uu____13960  -> dummy)
                                     lbs1 in
                                 let uu____13961 =
                                   let uu____13970 =
                                     FStar_List.map
                                       (fun uu____13990  -> dummy) xs1 in
                                   FStar_List.append uu____13970 env in
                                 FStar_List.append uu____13944 uu____13961 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14014 =
                                       let uu___128_14015 = rc in
                                       let uu____14016 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___128_14015.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14016;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___128_14015.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____14014
                                 | uu____14023 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___129_14027 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___129_14027.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___129_14027.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14037 =
                        FStar_List.map (fun uu____14053  -> dummy) lbs2 in
                      FStar_List.append uu____14037 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14061 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14061 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___130_14077 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___130_14077.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___130_14077.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14104 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14104
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14123 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14199  ->
                        match uu____14199 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___131_14320 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___131_14320.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___131_14320.FStar_Syntax_Syntax.sort)
                              } in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env in
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0")) in
               (match uu____14123 with
                | (rec_env,memos,uu____14533) ->
                    let uu____14586 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____14897 =
                               let uu____14904 =
                                 let uu____14905 =
                                   let uu____14936 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14936, false) in
                                 Clos uu____14905 in
                               (FStar_Pervasives_Native.None, uu____14904) in
                             uu____14897 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15046  ->
                     let uu____15047 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15047);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15069 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15071::uu____15072 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15077) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____15078 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____15109 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15123 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15123
                              | uu____15134 -> m in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env stack t2))))
and do_unfold_fv:
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun f  ->
            let r_env =
              let uu____15146 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15146 in
            let uu____15147 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15147 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15160  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15171  ->
                      let uu____15172 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15173 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15172
                        uu____15173);
                 (let t1 =
                    let uu____15175 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____15177 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____15177) in
                    if uu____15175
                    then t
                    else
                      FStar_Syntax_Subst.set_use_range
                        (FStar_Ident.range_of_lid
                           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                        t in
                  let n1 = FStar_List.length us in
                  if n1 > (Prims.parse_int "0")
                  then
                    match stack with
                    | (UnivArgs (us',uu____15187))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____15242 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15245 ->
                        let uu____15248 =
                          let uu____15249 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15249 in
                        failwith uu____15248
                  else norm cfg env stack t1))
and reduce_impure_comp:
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t in
              let stack1 = (Cfg cfg) :: stack in
              let cfg1 =
                let uu____15270 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____15270
                then
                  let uu___132_15271 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___132_15271.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___132_15271.primitive_steps);
                    strong = (uu___132_15271.strong);
                    memoize_lazy = (uu___132_15271.memoize_lazy);
                    normalize_pure_lets =
                      (uu___132_15271.normalize_pure_lets)
                  }
                else
                  (let uu___133_15273 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___133_15273.tcenv);
                     delta_level = (uu___133_15273.delta_level);
                     primitive_steps = (uu___133_15273.primitive_steps);
                     strong = (uu___133_15273.strong);
                     memoize_lazy = (uu___133_15273.memoize_lazy);
                     normalize_pure_lets =
                       (uu___133_15273.normalize_pure_lets)
                   }) in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1) in
              norm cfg1 env
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1
and do_reify_monadic:
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun head1  ->
            fun m  ->
              fun t  ->
                let head2 = FStar_Syntax_Util.unascribe head1 in
                log cfg
                  (fun uu____15302  ->
                     let uu____15303 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15304 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15303
                       uu____15304);
                (let uu____15305 =
                   let uu____15306 = FStar_Syntax_Subst.compress head2 in
                   uu____15306.FStar_Syntax_Syntax.n in
                 match uu____15305 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15324 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15324 with
                      | (uu____15325,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15331 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15339 =
                                   let uu____15340 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15340.FStar_Syntax_Syntax.n in
                                 match uu____15339 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15346,uu____15347))
                                     ->
                                     let uu____15356 =
                                       let uu____15357 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15357.FStar_Syntax_Syntax.n in
                                     (match uu____15356 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15363,msrc,uu____15365))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15374 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15374
                                      | uu____15375 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15376 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15377 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15377 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___134_15382 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___134_15382.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___134_15382.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___134_15382.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15383 = FStar_List.tl stack in
                                    let uu____15384 =
                                      let uu____15385 =
                                        let uu____15388 =
                                          let uu____15389 =
                                            let uu____15402 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15402) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15389 in
                                        FStar_Syntax_Syntax.mk uu____15388 in
                                      uu____15385
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15383 uu____15384
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15418 =
                                      let uu____15419 = is_return body in
                                      match uu____15419 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15423;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15424;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15429 -> false in
                                    if uu____15418
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head2.FStar_Syntax_Syntax.pos in
                                       let head3 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify
                                           lb.FStar_Syntax_Syntax.lbdef in
                                       let body1 =
                                         FStar_All.pipe_left
                                           FStar_Syntax_Util.mk_reify body in
                                       let body_rc =
                                         {
                                           FStar_Syntax_Syntax.residual_effect
                                             = m;
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         } in
                                       let body2 =
                                         let uu____15452 =
                                           let uu____15455 =
                                             let uu____15456 =
                                               let uu____15473 =
                                                 let uu____15476 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15476] in
                                               (uu____15473, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15456 in
                                           FStar_Syntax_Syntax.mk uu____15455 in
                                         uu____15452
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15492 =
                                           let uu____15493 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15493.FStar_Syntax_Syntax.n in
                                         match uu____15492 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15499::uu____15500::[])
                                             ->
                                             let uu____15507 =
                                               let uu____15510 =
                                                 let uu____15511 =
                                                   let uu____15518 =
                                                     let uu____15521 =
                                                       let uu____15522 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15522 in
                                                     let uu____15523 =
                                                       let uu____15526 =
                                                         let uu____15527 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15527 in
                                                       [uu____15526] in
                                                     uu____15521 ::
                                                       uu____15523 in
                                                   (bind1, uu____15518) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15511 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15510 in
                                             uu____15507
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15535 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15541 =
                                           let uu____15544 =
                                             let uu____15545 =
                                               let uu____15560 =
                                                 let uu____15563 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15564 =
                                                   let uu____15567 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15568 =
                                                     let uu____15571 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15572 =
                                                       let uu____15575 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15576 =
                                                         let uu____15579 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15580 =
                                                           let uu____15583 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15583] in
                                                         uu____15579 ::
                                                           uu____15580 in
                                                       uu____15575 ::
                                                         uu____15576 in
                                                     uu____15571 ::
                                                       uu____15572 in
                                                   uu____15567 :: uu____15568 in
                                                 uu____15563 :: uu____15564 in
                                               (bind_inst, uu____15560) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15545 in
                                           FStar_Syntax_Syntax.mk uu____15544 in
                                         uu____15541
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15594  ->
                                            let uu____15595 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15595);
                                       (let uu____15596 = FStar_List.tl stack in
                                        norm cfg env uu____15596 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15620 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15620 with
                      | (uu____15621,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15656 =
                                  let uu____15657 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15657.FStar_Syntax_Syntax.n in
                                match uu____15656 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15663) -> t2
                                | uu____15668 -> head3 in
                              let uu____15669 =
                                let uu____15670 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15670.FStar_Syntax_Syntax.n in
                              match uu____15669 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15676 -> FStar_Pervasives_Native.None in
                            let uu____15677 = maybe_extract_fv head3 in
                            match uu____15677 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15687 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15687
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15692 = maybe_extract_fv head4 in
                                  match uu____15692 with
                                  | FStar_Pervasives_Native.Some uu____15697
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15698 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15703 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15718 =
                              match uu____15718 with
                              | (e,q) ->
                                  let uu____15725 =
                                    let uu____15726 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15726.FStar_Syntax_Syntax.n in
                                  (match uu____15725 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15741 -> false) in
                            let uu____15742 =
                              let uu____15743 =
                                let uu____15750 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15750 :: args in
                              FStar_Util.for_some is_arg_impure uu____15743 in
                            if uu____15742
                            then
                              let uu____15755 =
                                let uu____15756 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15756 in
                              failwith uu____15755
                            else ());
                           (let uu____15758 = maybe_unfold_action head_app in
                            match uu____15758 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args)) in
                                let body1 =
                                  match found_action with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Syntax_Util.mk_reify body
                                  | FStar_Pervasives_Native.Some (false ) ->
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_meta
                                           (body,
                                             (FStar_Syntax_Syntax.Meta_monadic
                                                (m, t))))
                                  | FStar_Pervasives_Native.Some (true ) ->
                                      body in
                                let uu____15795 = FStar_List.tl stack in
                                norm cfg env uu____15795 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15797) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15821 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15821 in
                     (log cfg
                        (fun uu____15825  ->
                           let uu____15826 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15826);
                      (let uu____15827 = FStar_List.tl stack in
                       norm cfg env uu____15827 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15829) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15954  ->
                               match uu____15954 with
                               | (pat,wopt,tm) ->
                                   let uu____16002 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____16002))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____16034 = FStar_List.tl stack in
                     norm cfg env uu____16034 tm
                 | uu____16035 -> fallback ())
and reify_lift:
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv in
            log cfg
              (fun uu____16049  ->
                 let uu____16050 = FStar_Ident.string_of_lid msrc in
                 let uu____16051 = FStar_Ident.string_of_lid mtgt in
                 let uu____16052 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16050
                   uu____16051 uu____16052);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____16054 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____16054 with
               | (uu____16055,return_repr) ->
                   let return_inst =
                     let uu____16064 =
                       let uu____16065 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____16065.FStar_Syntax_Syntax.n in
                     match uu____16064 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16071::[]) ->
                         let uu____16078 =
                           let uu____16081 =
                             let uu____16082 =
                               let uu____16089 =
                                 let uu____16092 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____16092] in
                               (return_tm, uu____16089) in
                             FStar_Syntax_Syntax.Tm_uinst uu____16082 in
                           FStar_Syntax_Syntax.mk uu____16081 in
                         uu____16078 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16100 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____16103 =
                     let uu____16106 =
                       let uu____16107 =
                         let uu____16122 =
                           let uu____16125 = FStar_Syntax_Syntax.as_arg t in
                           let uu____16126 =
                             let uu____16129 = FStar_Syntax_Syntax.as_arg e in
                             [uu____16129] in
                           uu____16125 :: uu____16126 in
                         (return_inst, uu____16122) in
                       FStar_Syntax_Syntax.Tm_app uu____16107 in
                     FStar_Syntax_Syntax.mk uu____16106 in
                   uu____16103 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____16138 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16138 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16141 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16141
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16142;
                     FStar_TypeChecker_Env.mtarget = uu____16143;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16144;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16159;
                     FStar_TypeChecker_Env.mtarget = uu____16160;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16161;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16185 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16186 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16185 t FStar_Syntax_Syntax.tun uu____16186)
and norm_pattern_args:
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____16242  ->
                   match uu____16242 with
                   | (a,imp) ->
                       let uu____16253 = norm cfg env [] a in
                       (uu____16253, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___135_16267 = comp in
            let uu____16268 =
              let uu____16269 =
                let uu____16278 = norm cfg env [] t in
                let uu____16279 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16278, uu____16279) in
              FStar_Syntax_Syntax.Total uu____16269 in
            {
              FStar_Syntax_Syntax.n = uu____16268;
              FStar_Syntax_Syntax.pos =
                (uu___135_16267.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___135_16267.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___136_16294 = comp in
            let uu____16295 =
              let uu____16296 =
                let uu____16305 = norm cfg env [] t in
                let uu____16306 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16305, uu____16306) in
              FStar_Syntax_Syntax.GTotal uu____16296 in
            {
              FStar_Syntax_Syntax.n = uu____16295;
              FStar_Syntax_Syntax.pos =
                (uu___136_16294.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___136_16294.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16358  ->
                      match uu____16358 with
                      | (a,i) ->
                          let uu____16369 = norm cfg env [] a in
                          (uu____16369, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___85_16380  ->
                      match uu___85_16380 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16384 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16384
                      | f -> f)) in
            let uu___137_16388 = comp in
            let uu____16389 =
              let uu____16390 =
                let uu___138_16391 = ct in
                let uu____16392 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16393 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16396 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16392;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___138_16391.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16393;
                  FStar_Syntax_Syntax.effect_args = uu____16396;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16390 in
            {
              FStar_Syntax_Syntax.n = uu____16389;
              FStar_Syntax_Syntax.pos =
                (uu___137_16388.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16388.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16407  ->
        match uu____16407 with
        | (x,imp) ->
            let uu____16410 =
              let uu___139_16411 = x in
              let uu____16412 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___139_16411.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___139_16411.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16412
              } in
            (uu____16410, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16418 =
          FStar_List.fold_left
            (fun uu____16436  ->
               fun b  ->
                 match uu____16436 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16418 with | (nbs,uu____16476) -> FStar_List.rev nbs
and norm_lcomp_opt:
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu____16492 =
              let uu___140_16493 = rc in
              let uu____16494 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_16493.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16494;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___140_16493.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16492
        | uu____16501 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16514  ->
               let uu____16515 = FStar_Syntax_Print.tag_of_term t in
               let uu____16516 = FStar_Syntax_Print.term_to_string t in
               let uu____16517 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16524 =
                 let uu____16525 =
                   let uu____16528 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16528 in
                 stack_to_string uu____16525 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16515 uu____16516 uu____16517 uu____16524);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16557 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16557
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16559 =
                     let uu____16560 =
                       let uu____16561 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16561 in
                     FStar_Util.string_of_int uu____16560 in
                   let uu____16566 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16567 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16559 uu____16566 uu____16567
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____16621  ->
                     let uu____16622 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16622);
                rebuild cfg env stack1 t)
           | (Let (env',bs,lb,r))::stack1 ->
               let body = FStar_Syntax_Subst.close bs t in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                   FStar_Pervasives_Native.None r in
               rebuild cfg env' stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let bs1 = norm_binders cfg env' bs in
               let lopt1 = norm_lcomp_opt cfg env'' lopt in
               let uu____16658 =
                 let uu___141_16659 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___141_16659.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___141_16659.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16658
           | (Arg (Univ uu____16660,uu____16661,uu____16662))::uu____16663 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16666,uu____16667))::uu____16668 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16684),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16737  ->
                     let uu____16738 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16738);
                if FStar_List.contains (Exclude Iota) cfg.steps
                then
                  (if FStar_List.contains HNF cfg.steps
                   then
                     let arg = closure_as_term cfg env_arg tm in
                     let t1 =
                       FStar_Syntax_Syntax.extend_app t (arg, aq)
                         FStar_Pervasives_Native.None r in
                     rebuild cfg env_arg stack1 t1
                   else
                     (let stack2 = (App (env, t, aq, r)) :: stack1 in
                      norm cfg env_arg stack2 tm))
                else
                  (let uu____16748 = FStar_ST.op_Bang m in
                   match uu____16748 with
                   | FStar_Pervasives_Native.None  ->
                       if FStar_List.contains HNF cfg.steps
                       then
                         let arg = closure_as_term cfg env_arg tm in
                         let t1 =
                           FStar_Syntax_Syntax.extend_app t (arg, aq)
                             FStar_Pervasives_Native.None r in
                         rebuild cfg env_arg stack1 t1
                       else
                         (let stack2 = (MemoLazy m) :: (App (env, t, aq, r))
                            :: stack1 in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____16885,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____16932 =
                 log cfg
                   (fun uu____16936  ->
                      let uu____16937 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16937);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____16941 =
                 let uu____16942 = FStar_Syntax_Subst.compress t in
                 uu____16942.FStar_Syntax_Syntax.n in
               (match uu____16941 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16969 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____16969 in
                    (log cfg
                       (fun uu____16973  ->
                          let uu____16974 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____16974);
                     (let uu____16975 = FStar_List.tl stack in
                      norm cfg env1 uu____16975 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16976);
                       FStar_Syntax_Syntax.pos = uu____16977;
                       FStar_Syntax_Syntax.vars = uu____16978;_},(e,uu____16980)::[])
                    -> norm cfg env1 stack' e
                | uu____17009 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____17020 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____17020
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17032  ->
                     let uu____17033 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17033);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17038 =
                   log cfg
                     (fun uu____17043  ->
                        let uu____17044 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17045 =
                          let uu____17046 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17063  ->
                                    match uu____17063 with
                                    | (p,uu____17073,uu____17074) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17046
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17044 uu____17045);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___86_17091  ->
                                match uu___86_17091 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17092 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___142_17096 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___142_17096.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___142_17096.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___142_17096.memoize_lazy);
                        normalize_pure_lets =
                          (uu___142_17096.normalize_pure_lets)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17128 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17149 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17209  ->
                                    fun uu____17210  ->
                                      match (uu____17209, uu____17210) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17301 = norm_pat env3 p1 in
                                          (match uu____17301 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17149 with
                           | (pats1,env3) ->
                               ((let uu___143_17383 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___143_17383.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___144_17402 = x in
                            let uu____17403 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___144_17402.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___144_17402.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17403
                            } in
                          ((let uu___145_17417 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___145_17417.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___146_17428 = x in
                            let uu____17429 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_17428.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_17428.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17429
                            } in
                          ((let uu___147_17443 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___147_17443.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___148_17459 = x in
                            let uu____17460 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17459.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17459.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17460
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___149_17467 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___149_17467.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17477 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17491 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17491 with
                                  | (p,wopt,e) ->
                                      let uu____17511 = norm_pat env1 p in
                                      (match uu____17511 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17536 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17536 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17542 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17542) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17552) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17557 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17558;
                         FStar_Syntax_Syntax.fv_delta = uu____17559;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17560;
                         FStar_Syntax_Syntax.fv_delta = uu____17561;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17562);_}
                       -> true
                   | uu____17569 -> false in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig in
                   let uu____17714 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17714 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17801 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17840 ->
                                 let uu____17841 =
                                   let uu____17842 = is_cons head1 in
                                   Prims.op_Negation uu____17842 in
                                 FStar_Util.Inr uu____17841)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17867 =
                              let uu____17868 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17868.FStar_Syntax_Syntax.n in
                            (match uu____17867 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17886 ->
                                 let uu____17887 =
                                   let uu____17888 = is_cons head1 in
                                   Prims.op_Negation uu____17888 in
                                 FStar_Util.Inr uu____17887))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17957)::rest_a,(p1,uu____17960)::rest_p) ->
                       let uu____18004 = matches_pat t1 p1 in
                       (match uu____18004 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18053 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18159 = matches_pat scrutinee1 p1 in
                       (match uu____18159 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18199  ->
                                  let uu____18200 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18201 =
                                    let uu____18202 =
                                      FStar_List.map
                                        (fun uu____18212  ->
                                           match uu____18212 with
                                           | (uu____18217,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18202
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18200 uu____18201);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18248  ->
                                       match uu____18248 with
                                       | (bv,t1) ->
                                           let uu____18271 =
                                             let uu____18278 =
                                               let uu____18281 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18281 in
                                             let uu____18282 =
                                               let uu____18283 =
                                                 let uu____18314 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18314, false) in
                                               Clos uu____18283 in
                                             (uu____18278, uu____18282) in
                                           uu____18271 :: env2) env1 s in
                              let uu____18431 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18431))) in
                 let uu____18432 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18432
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___87_18453  ->
                match uu___87_18453 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18457 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18463 -> d in
      let uu____18466 =
        (FStar_Options.normalize_pure_terms_for_extraction ()) ||
          (let uu____18468 =
             FStar_All.pipe_right s
               (FStar_List.contains PureSubtermsWithinComputations) in
           Prims.op_Negation uu____18468) in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true;
        normalize_pure_lets = uu____18466
      }
let normalize_with_primitive_steps:
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = config s e in
          let c1 =
            let uu___150_18493 = config s e in
            {
              steps = (uu___150_18493.steps);
              tcenv = (uu___150_18493.tcenv);
              delta_level = (uu___150_18493.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___150_18493.strong);
              memoize_lazy = (uu___150_18493.memoize_lazy);
              normalize_pure_lets = (uu___150_18493.normalize_pure_lets)
            } in
          norm c1 [] [] t
let normalize:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t
let normalize_comp:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____18518 = config s e in norm_comp uu____18518 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18531 = config [] env in norm_universe uu____18531 [] u
let ghost_to_pure:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env in
      let non_info t =
        let uu____18549 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18549 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18556 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___151_18575 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___151_18575.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___151_18575.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18582 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18582
          then
            let ct1 =
              match downgrade_ghost_effect_name
                      ct.FStar_Syntax_Syntax.effect_name
              with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    if
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags in
                  let uu___152_18591 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___152_18591.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___152_18591.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___152_18591.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___153_18593 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___153_18593.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___153_18593.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___153_18593.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___153_18593.FStar_Syntax_Syntax.flags)
                  } in
            let uu___154_18594 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___154_18594.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___154_18594.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18596 -> c
let ghost_to_pure_lcomp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env in
      let non_info t =
        let uu____18608 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18608 in
      let uu____18615 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18615
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18619  ->
                 let uu____18620 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18620)
        | FStar_Pervasives_Native.None  -> lc
      else lc
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____18637 =
                let uu____18642 =
                  let uu____18643 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18643 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18642) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18637);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18654 = config [AllowUnboundUniverses] env in
          norm_comp uu____18654 [] c
        with
        | e ->
            ((let uu____18667 =
                let uu____18672 =
                  let uu____18673 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18673 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18672) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18667);
             c) in
      FStar_Syntax_Print.comp_to_string c1
let normalize_refinement:
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t = normalize (FStar_List.append steps [Beta]) env t0 in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1 in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____18710 =
                     let uu____18711 =
                       let uu____18718 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18718) in
                     FStar_Syntax_Syntax.Tm_refine uu____18711 in
                   mk uu____18710 t01.FStar_Syntax_Syntax.pos
               | uu____18723 -> t2)
          | uu____18724 -> t2 in
        aux t
let unfold_whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize
        [Weak; HNF; UnfoldUntil FStar_Syntax_Syntax.Delta_constant; Beta] env
        t
let reduce_or_remove_uvar_solutions:
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append (if remove then [CheckNoUvars] else [])
             [Beta;
             NoDeltaSteps;
             CompressUvars;
             Exclude Zeta;
             Exclude Iota;
             NoFullNorm]) env t
let reduce_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t
let remove_uvar_solutions:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t
let eta_expand_with_type:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____18764 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18764 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18793 ->
                 let uu____18800 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18800 with
                  | (actuals,uu____18810,uu____18811) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18825 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18825 with
                         | (binders,args) ->
                             let uu____18842 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18842
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let eta_expand:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____18850 ->
          let uu____18851 = FStar_Syntax_Util.head_and_args t in
          (match uu____18851 with
           | (head1,args) ->
               let uu____18888 =
                 let uu____18889 = FStar_Syntax_Subst.compress head1 in
                 uu____18889.FStar_Syntax_Syntax.n in
               (match uu____18888 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18892,thead) ->
                    let uu____18918 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18918 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18960 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___159_18968 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___159_18968.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___159_18968.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___159_18968.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___159_18968.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___159_18968.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___159_18968.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___159_18968.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___159_18968.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___159_18968.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___159_18968.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___159_18968.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___159_18968.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___159_18968.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___159_18968.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___159_18968.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___159_18968.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___159_18968.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___159_18968.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___159_18968.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___159_18968.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___159_18968.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___159_18968.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___159_18968.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___159_18968.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___159_18968.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___159_18968.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___159_18968.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___159_18968.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___159_18968.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___159_18968.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___159_18968.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18960 with
                            | (uu____18969,ty,uu____18971) ->
                                eta_expand_with_type env t ty))
                | uu____18972 ->
                    let uu____18973 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___160_18981 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___160_18981.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___160_18981.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___160_18981.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___160_18981.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___160_18981.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___160_18981.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___160_18981.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___160_18981.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___160_18981.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___160_18981.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___160_18981.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___160_18981.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___160_18981.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___160_18981.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___160_18981.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___160_18981.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___160_18981.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___160_18981.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___160_18981.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___160_18981.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___160_18981.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___160_18981.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___160_18981.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___160_18981.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___160_18981.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___160_18981.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___160_18981.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___160_18981.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___160_18981.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___160_18981.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___160_18981.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18973 with
                     | (uu____18982,ty,uu____18984) ->
                         eta_expand_with_type env t ty)))
let elim_uvars_aux_tc:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term,
                                                         FStar_Syntax_Syntax.comp'
                                                           FStar_Syntax_Syntax.syntax)
                                                         FStar_Util.either)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____19058,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19064,FStar_Util.Inl t) ->
                let uu____19070 =
                  let uu____19073 =
                    let uu____19074 =
                      let uu____19087 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19087) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19074 in
                  FStar_Syntax_Syntax.mk uu____19073 in
                uu____19070 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19091 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19091 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19118 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19173 ->
                    let uu____19174 =
                      let uu____19183 =
                        let uu____19184 = FStar_Syntax_Subst.compress t3 in
                        uu____19184.FStar_Syntax_Syntax.n in
                      (uu____19183, tc) in
                    (match uu____19174 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19209) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19246) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19285,FStar_Util.Inl uu____19286) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19309 -> failwith "Impossible") in
              (match uu____19118 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
let elim_uvars_aux_t:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____19414 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19414 with
          | (univ_names1,binders1,tc) ->
              let uu____19472 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19472)
let elim_uvars_aux_c:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____19507 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19507 with
          | (univ_names1,binders1,tc) ->
              let uu____19567 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19567)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19600 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19600 with
           | (univ_names1,binders1,typ1) ->
               let uu___161_19628 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_19628.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_19628.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_19628.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___161_19628.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___162_19649 = s in
          let uu____19650 =
            let uu____19651 =
              let uu____19660 = FStar_List.map (elim_uvars env) sigs in
              (uu____19660, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19651 in
          {
            FStar_Syntax_Syntax.sigel = uu____19650;
            FStar_Syntax_Syntax.sigrng =
              (uu___162_19649.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___162_19649.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___162_19649.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___162_19649.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19677 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19677 with
           | (univ_names1,uu____19695,typ1) ->
               let uu___163_19709 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___163_19709.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___163_19709.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___163_19709.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___163_19709.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19715 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19715 with
           | (univ_names1,uu____19733,typ1) ->
               let uu___164_19747 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_19747.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_19747.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_19747.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___164_19747.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19781 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19781 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19804 =
                            let uu____19805 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19805 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19804 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___165_19808 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___165_19808.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___165_19808.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___166_19809 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___166_19809.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___166_19809.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___166_19809.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___166_19809.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___167_19821 = s in
          let uu____19822 =
            let uu____19823 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19823 in
          {
            FStar_Syntax_Syntax.sigel = uu____19822;
            FStar_Syntax_Syntax.sigrng =
              (uu___167_19821.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_19821.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_19821.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_19821.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19827 = elim_uvars_aux_t env us [] t in
          (match uu____19827 with
           | (us1,uu____19845,t1) ->
               let uu___168_19859 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_19859.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_19859.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_19859.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_19859.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19860 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19862 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19862 with
           | (univs1,binders,signature) ->
               let uu____19890 =
                 let uu____19899 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19899 with
                 | (univs_opening,univs2) ->
                     let uu____19926 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19926) in
               (match uu____19890 with
                | (univs_opening,univs_closing) ->
                    let uu____19943 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19949 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19950 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19949, uu____19950) in
                    (match uu____19943 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19972 =
                           match uu____19972 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19990 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19990 with
                                | (us1,t1) ->
                                    let uu____20001 =
                                      let uu____20006 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____20013 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____20006, uu____20013) in
                                    (match uu____20001 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____20026 =
                                           let uu____20031 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20040 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20031, uu____20040) in
                                         (match uu____20026 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20056 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20056 in
                                              let uu____20057 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20057 with
                                               | (uu____20078,uu____20079,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20094 =
                                                       let uu____20095 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20095 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20094 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20100 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20100 with
                           | (uu____20113,uu____20114,t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Util.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____20174 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20191 =
                               let uu____20192 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20192.FStar_Syntax_Syntax.n in
                             match uu____20191 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20251 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20280 =
                               let uu____20281 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20281.FStar_Syntax_Syntax.n in
                             match uu____20280 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20302) ->
                                 let uu____20323 = destruct_action_body body in
                                 (match uu____20323 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20368 ->
                                 let uu____20369 = destruct_action_body t in
                                 (match uu____20369 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20418 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20418 with
                           | (action_univs,t) ->
                               let uu____20427 = destruct_action_typ_templ t in
                               (match uu____20427 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___169_20468 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___169_20468.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___169_20468.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      } in
                                    a') in
                         let ed1 =
                           let uu___170_20470 = ed in
                           let uu____20471 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20472 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20473 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20474 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20475 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20476 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20477 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20478 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20479 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20480 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20481 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20482 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20483 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20484 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___170_20470.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___170_20470.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20471;
                             FStar_Syntax_Syntax.bind_wp = uu____20472;
                             FStar_Syntax_Syntax.if_then_else = uu____20473;
                             FStar_Syntax_Syntax.ite_wp = uu____20474;
                             FStar_Syntax_Syntax.stronger = uu____20475;
                             FStar_Syntax_Syntax.close_wp = uu____20476;
                             FStar_Syntax_Syntax.assert_p = uu____20477;
                             FStar_Syntax_Syntax.assume_p = uu____20478;
                             FStar_Syntax_Syntax.null_wp = uu____20479;
                             FStar_Syntax_Syntax.trivial = uu____20480;
                             FStar_Syntax_Syntax.repr = uu____20481;
                             FStar_Syntax_Syntax.return_repr = uu____20482;
                             FStar_Syntax_Syntax.bind_repr = uu____20483;
                             FStar_Syntax_Syntax.actions = uu____20484
                           } in
                         let uu___171_20487 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___171_20487.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___171_20487.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___171_20487.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___171_20487.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___88_20504 =
            match uu___88_20504 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20531 = elim_uvars_aux_t env us [] t in
                (match uu____20531 with
                 | (us1,uu____20555,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___172_20574 = sub_eff in
            let uu____20575 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20578 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___172_20574.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___172_20574.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20575;
              FStar_Syntax_Syntax.lift = uu____20578
            } in
          let uu___173_20581 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___173_20581.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___173_20581.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___173_20581.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___173_20581.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20591 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20591 with
           | (univ_names1,binders1,comp1) ->
               let uu___174_20625 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20625.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20625.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20625.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20625.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20636 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t