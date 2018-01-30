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
  memoize_lazy: Prims.bool;}[@@deriving show]
let __proj__Mkcfg__item__steps: cfg -> steps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__steps
let __proj__Mkcfg__item__tcenv: cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__tcenv
let __proj__Mkcfg__item__delta_level:
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__delta_level
let __proj__Mkcfg__item__primitive_steps: cfg -> primitive_step Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__primitive_steps
let __proj__Mkcfg__item__strong: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__strong
let __proj__Mkcfg__item__memoize_lazy: cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;_} -> __fname__memoize_lazy
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
    match projectee with | Arg _0 -> true | uu____806 -> false
let __proj__Arg__item___0:
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0
let uu___is_UnivArgs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____842 -> false
let __proj__UnivArgs__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0
let uu___is_MemoLazy: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____878 -> false
let __proj__MemoLazy__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0
let uu___is_Match: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____947 -> false
let __proj__Match__item___0:
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Match _0 -> _0
let uu___is_Abs: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____989 -> false
let __proj__Abs__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0
let uu___is_App: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1045 -> false
let __proj__App__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0
let uu___is_Meta: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1085 -> false
let __proj__Meta__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Meta _0 -> _0
let uu___is_Let: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1117 -> false
let __proj__Let__item___0:
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0
let uu___is_Cfg: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1153 -> false
let __proj__Cfg__item___0: stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0
let uu___is_Debug: stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1169 -> false
let __proj__Debug__item___0:
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0
type stack = stack_elt Prims.list[@@deriving show]
let mk:
  'Auu____1194 .
    'Auu____1194 ->
      FStar_Range.range -> 'Auu____1194 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r
let set_memo: 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____1248 = FStar_ST.op_Bang r in
          match uu____1248 with
          | FStar_Pervasives_Native.Some uu____1296 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let env_to_string: closure Prims.list -> Prims.string =
  fun env  ->
    let uu____1350 = FStar_List.map closure_to_string env in
    FStar_All.pipe_right uu____1350 (FStar_String.concat "; ")
let stack_elt_to_string: stack_elt -> Prims.string =
  fun uu___73_1357  ->
    match uu___73_1357 with
    | Arg (c,uu____1359,uu____1360) ->
        let uu____1361 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu____1361
    | MemoLazy uu____1362 -> "MemoLazy"
    | Abs (uu____1369,bs,uu____1371,uu____1372,uu____1373) ->
        let uu____1378 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu____1378
    | UnivArgs uu____1383 -> "UnivArgs"
    | Match uu____1390 -> "Match"
    | App (uu____1397,t,uu____1399,uu____1400) ->
        let uu____1401 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu____1401
    | Meta (m,uu____1403) -> "Meta"
    | Let uu____1404 -> "Let"
    | Cfg uu____1413 -> "Cfg"
    | Debug (t,uu____1415) ->
        let uu____1416 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "Debug %s" uu____1416
let stack_to_string: stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____1424 = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu____1424 (FStar_String.concat "; ")
let log: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1440 =
        FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm") in
      if uu____1440 then f () else ()
let log_primops: cfg -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun cfg  ->
    fun f  ->
      let uu____1453 =
        (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other "Norm"))
          ||
          (FStar_TypeChecker_Env.debug cfg.tcenv
             (FStar_Options.Other "Primops")) in
      if uu____1453 then f () else ()
let is_empty: 'Auu____1457 . 'Auu____1457 Prims.list -> Prims.bool =
  fun uu___74_1463  ->
    match uu___74_1463 with | [] -> true | uu____1466 -> false
let lookup_bvar:
  'Auu____1473 'Auu____1474 .
    ('Auu____1474,'Auu____1473) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____1473
  =
  fun env  ->
    fun x  ->
      try
        let uu____1498 = FStar_List.nth env x.FStar_Syntax_Syntax.index in
        FStar_Pervasives_Native.snd uu____1498
      with
      | uu____1511 ->
          let uu____1512 =
            let uu____1513 = FStar_Syntax_Print.db_to_string x in
            FStar_Util.format1 "Failed to find %s\n" uu____1513 in
          failwith uu____1512
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
          let uu____1550 =
            FStar_List.fold_left
              (fun uu____1576  ->
                 fun u1  ->
                   match uu____1576 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1601 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu____1601 with
                        | (k_u,n1) ->
                            let uu____1616 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu____1616
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu____1550 with
          | (uu____1634,u1,out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1659 =
                   let uu____1660 = FStar_List.nth env x in
                   FStar_Pervasives_Native.snd uu____1660 in
                 match uu____1659 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____1678 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1687 ->
                   let uu____1688 =
                     FStar_All.pipe_right cfg.steps
                       (FStar_List.contains AllowUnboundUniverses) in
                   if uu____1688
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1694 when
              FStar_All.pipe_right cfg.steps
                (FStar_List.contains CheckNoUvars)
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1703 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1712 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1719 = FStar_List.collect aux us in
                FStar_All.pipe_right uu____1719 norm_univs in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest in
                   let uu____1736 = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu____1736 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1744 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1752 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu____1752 with
                                  | (uu____1757,m) -> n1 <= m)) in
                        if uu____1744 then rest1 else us1
                    | uu____1762 -> us1)
               | uu____1767 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1771 = aux u3 in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____1771 in
        let uu____1774 =
          FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses) in
        if uu____1774
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1776 = aux u in
           match uu____1776 with
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
          (fun uu____1880  ->
             let uu____1881 = FStar_Syntax_Print.tag_of_term t in
             let uu____1882 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____1881
               uu____1882);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation
               (FStar_List.contains CompressUvars cfg.steps)
             -> t
         | uu____1889 ->
             let t1 = FStar_Syntax_Subst.compress t in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____1891 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____1916 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____1917 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____1918 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____1919 ->
                  let uu____1936 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains CheckNoUvars) in
                  if uu____1936
                  then
                    let uu____1937 =
                      let uu____1938 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos in
                      let uu____1939 = FStar_Syntax_Print.term_to_string t1 in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____1938 uu____1939 in
                    failwith uu____1937
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____1942 =
                    let uu____1943 = norm_universe cfg env u in
                    FStar_Syntax_Syntax.Tm_type uu____1943 in
                  mk uu____1942 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____1950 = FStar_List.map (norm_universe cfg env) us in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1950
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____1952 = lookup_bvar env x in
                  (match uu____1952 with
                   | Univ uu____1955 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____1958,uu____1959) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1 in
                  let args1 = closures_as_args_delayed cfg env args in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____2071 = closures_as_binders_delayed cfg env bs in
                  (match uu____2071 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body in
                       let uu____2099 =
                         let uu____2100 =
                           let uu____2117 = close_lcomp_opt cfg env1 lopt in
                           (bs1, body1, uu____2117) in
                         FStar_Syntax_Syntax.Tm_abs uu____2100 in
                       mk uu____2099 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____2148 = closures_as_binders_delayed cfg env bs in
                  (match uu____2148 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____2190 =
                    let uu____2201 =
                      let uu____2208 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____2208] in
                    closures_as_binders_delayed cfg env uu____2201 in
                  (match uu____2190 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi in
                       let uu____2226 =
                         let uu____2227 =
                           let uu____2234 =
                             let uu____2235 = FStar_List.hd x1 in
                             FStar_All.pipe_right uu____2235
                               FStar_Pervasives_Native.fst in
                           (uu____2234, phi1) in
                         FStar_Syntax_Syntax.Tm_refine uu____2227 in
                       mk uu____2226 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____2326 = closure_as_term_delayed cfg env t2 in
                        FStar_Util.Inl uu____2326
                    | FStar_Util.Inr c ->
                        let uu____2340 = close_comp cfg env c in
                        FStar_Util.Inr uu____2340 in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env) in
                  let uu____2356 =
                    let uu____2357 =
                      let uu____2384 = closure_as_term_delayed cfg env t11 in
                      (uu____2384, (annot1, tacopt1), lopt) in
                    FStar_Syntax_Syntax.Tm_ascribed uu____2357 in
                  mk uu____2356 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____2435 =
                    let uu____2436 =
                      let uu____2443 = closure_as_term_delayed cfg env t' in
                      let uu____2446 =
                        let uu____2447 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env)) in
                        FStar_Syntax_Syntax.Meta_pattern uu____2447 in
                      (uu____2443, uu____2446) in
                    FStar_Syntax_Syntax.Tm_meta uu____2436 in
                  mk uu____2435 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____2507 =
                    let uu____2508 =
                      let uu____2515 = closure_as_term_delayed cfg env t' in
                      let uu____2518 =
                        let uu____2519 =
                          let uu____2526 =
                            closure_as_term_delayed cfg env tbody in
                          (m, uu____2526) in
                        FStar_Syntax_Syntax.Meta_monadic uu____2519 in
                      (uu____2515, uu____2518) in
                    FStar_Syntax_Syntax.Tm_meta uu____2508 in
                  mk uu____2507 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____2545 =
                    let uu____2546 =
                      let uu____2553 = closure_as_term_delayed cfg env t' in
                      let uu____2556 =
                        let uu____2557 =
                          let uu____2566 =
                            closure_as_term_delayed cfg env tbody in
                          (m1, m2, uu____2566) in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____2557 in
                      (uu____2553, uu____2556) in
                    FStar_Syntax_Syntax.Tm_meta uu____2546 in
                  mk uu____2545 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____2579 =
                    let uu____2580 =
                      let uu____2587 = closure_as_term_delayed cfg env t' in
                      (uu____2587, m) in
                    FStar_Syntax_Syntax.Tm_meta uu____2580 in
                  mk uu____2579 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____2627  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef in
                  let uu____2646 =
                    let uu____2657 = FStar_Syntax_Syntax.is_top_level [lb] in
                    if uu____2657
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                       let uu____2676 =
                         closure_as_term cfg (dummy :: env0) body in
                       ((FStar_Util.Inl
                           (let uu___93_2688 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___93_2688.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___93_2688.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____2676)) in
                  (match uu____2646 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___94_2704 = lb in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_2704.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_2704.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def
                         } in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____2715,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____2774  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1 in
                    let env2 =
                      let uu____2799 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2799
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____2819  -> fun env2  -> dummy :: env2) lbs
                          env_univs in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let nm =
                      let uu____2841 = FStar_Syntax_Syntax.is_top_level lbs in
                      if uu____2841
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         FStar_All.pipe_right
                           (let uu___95_2853 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___95_2853.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___95_2853.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41)) in
                    let uu___96_2854 = lb in
                    let uu____2855 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___96_2854.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___96_2854.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____2855
                    } in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env)) in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____2885  -> fun env1  -> dummy :: env1) lbs1
                        env in
                    closure_as_term cfg body_env body in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1 in
                  let norm_one_branch env1 uu____2974 =
                    match uu____2974 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____3029 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____3050 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____3110  ->
                                        fun uu____3111  ->
                                          match (uu____3110, uu____3111) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____3202 =
                                                norm_pat env3 p1 in
                                              (match uu____3202 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2)) in
                              (match uu____3050 with
                               | (pats1,env3) ->
                                   ((let uu___97_3284 = p in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___97_3284.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___98_3303 = x in
                                let uu____3304 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___98_3303.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___98_3303.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3304
                                } in
                              ((let uu___99_3318 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___99_3318.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___100_3329 = x in
                                let uu____3330 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___100_3329.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___100_3329.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3330
                                } in
                              ((let uu___101_3344 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___101_3344.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___102_3360 = x in
                                let uu____3361 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___102_3360.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___102_3360.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____3361
                                } in
                              let t3 = closure_as_term cfg env2 t2 in
                              ((let uu___103_3368 = p in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___103_3368.FStar_Syntax_Syntax.p)
                                }), env2) in
                        let uu____3371 = norm_pat env1 pat in
                        (match uu____3371 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____3400 =
                                     closure_as_term cfg env2 w in
                                   FStar_Pervasives_Native.Some uu____3400 in
                             let tm1 = closure_as_term cfg env2 tm in
                             (pat1, w_opt1, tm1)) in
                  let uu____3406 =
                    let uu____3407 =
                      let uu____3430 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env)) in
                      (head2, uu____3430) in
                    FStar_Syntax_Syntax.Tm_match uu____3407 in
                  mk uu____3406 t1.FStar_Syntax_Syntax.pos))
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
        | uu____3516 -> closure_as_term cfg env t
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
        | uu____3542 ->
            FStar_List.map
              (fun uu____3559  ->
                 match uu____3559 with
                 | (x,imp) ->
                     let uu____3578 = closure_as_term_delayed cfg env x in
                     (uu____3578, imp)) args
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
        let uu____3592 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____3641  ->
                  fun uu____3642  ->
                    match (uu____3641, uu____3642) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___104_3712 = b in
                          let uu____3713 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___104_3712.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___104_3712.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____3713
                          } in
                        let env2 = dummy :: env1 in
                        (env2, ((b1, imp) :: out))) (env, [])) in
        match uu____3592 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)
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
        | uu____3806 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____3819 = closure_as_term_delayed cfg env t in
                 let uu____3820 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu____3819 uu____3820
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____3833 = closure_as_term_delayed cfg env t in
                 let uu____3834 =
                   FStar_Option.map (norm_universe cfg env) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu____3833 uu____3834
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
                        (fun uu___75_3860  ->
                           match uu___75_3860 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____3864 =
                                 closure_as_term_delayed cfg env t in
                               FStar_Syntax_Syntax.DECREASES uu____3864
                           | f -> f)) in
                 let uu____3868 =
                   let uu___105_3869 = c1 in
                   let uu____3870 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____3870;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___105_3869.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu____3868)
and filter_out_lcomp_cflags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___76_3880  ->
            match uu___76_3880 with
            | FStar_Syntax_Syntax.DECREASES uu____3881 -> false
            | uu____3884 -> true))
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
                   (fun uu___77_3902  ->
                      match uu___77_3902 with
                      | FStar_Syntax_Syntax.DECREASES uu____3903 -> false
                      | uu____3906 -> true)) in
            let rc1 =
              let uu___106_3908 = rc in
              let uu____3909 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___106_3908.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____3909;
                FStar_Syntax_Syntax.residual_flags = flags1
              } in
            FStar_Pervasives_Native.Some rc1
        | uu____3916 -> lopt
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
    let uu____4001 = FStar_Syntax_Embeddings.unembed_list_safe u in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4001 in
  let arg_as_bounded_int uu____4029 =
    match uu____4029 with
    | (a,uu____4041) ->
        let uu____4048 =
          let uu____4049 = FStar_Syntax_Subst.compress a in
          uu____4049.FStar_Syntax_Syntax.n in
        (match uu____4048 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____4059;
                FStar_Syntax_Syntax.vars = uu____4060;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____4062;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____4063;_},uu____4064)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____4103 =
               let uu____4108 = FStar_BigInt.big_int_of_string i in
               (fv1, uu____4108) in
             FStar_Pervasives_Native.Some uu____4103
         | uu____4113 -> FStar_Pervasives_Native.None) in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____4153 = f a in FStar_Pervasives_Native.Some uu____4153
    | uu____4154 -> FStar_Pervasives_Native.None in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____4202 = f a0 a1 in FStar_Pervasives_Native.Some uu____4202
    | uu____4203 -> FStar_Pervasives_Native.None in
  let unary_op a413 a414 a415 a416 a417 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4245 = FStar_List.map as_a args in
                  lift_unary () ()
                    (fun a412  -> (Obj.magic (f res.psc_range)) a412)
                    uu____4245)) a413 a414 a415 a416 a417 in
  let binary_op a420 a421 a422 a423 a424 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____4294 = FStar_List.map as_a args in
                  lift_binary () ()
                    (fun a418  ->
                       fun a419  -> (Obj.magic (f res.psc_range)) a418 a419)
                    uu____4294)) a420 a421 a422 a423 a424 in
  let as_primitive_step uu____4318 =
    match uu____4318 with
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
                   let uu____4366 = f x in
                   FStar_Syntax_Embeddings.embed_int r uu____4366)) a426 a427) in
  let binary_int_op f =
    binary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           fun a431  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____4394 = f x y in
                       FStar_Syntax_Embeddings.embed_int r uu____4394)) a429
               a430 a431) in
  let unary_bool_op f =
    unary_op () (fun a432  -> (Obj.magic arg_as_bool) a432)
      (fun a433  ->
         fun a434  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____4415 = f x in
                   FStar_Syntax_Embeddings.embed_bool r uu____4415)) a433
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
                       let uu____4443 = f x y in
                       FStar_Syntax_Embeddings.embed_bool r uu____4443)) a436
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
                       let uu____4471 = f x y in
                       FStar_Syntax_Embeddings.embed_string r uu____4471))
               a440 a441 a442) in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____4579 =
          let uu____4588 = as_a a in
          let uu____4591 = as_b b in (uu____4588, uu____4591) in
        (match uu____4579 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____4606 =
               let uu____4607 = f res.psc_range a1 b1 in
               embed_c res.psc_range uu____4607 in
             FStar_Pervasives_Native.Some uu____4606
         | uu____4608 -> FStar_Pervasives_Native.None)
    | uu____4617 -> FStar_Pervasives_Native.None in
  let list_of_string' rng s =
    let name l =
      let uu____4631 =
        let uu____4632 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu____4632 in
      mk uu____4631 rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu____4642 =
      let uu____4645 = FStar_String.list_of_string s in
      FStar_List.map charterm uu____4645 in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____4642 in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2 in
    let uu____4677 =
      let uu____4678 = FStar_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu____4678 in
    FStar_Syntax_Embeddings.embed_int rng uu____4677 in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____4696 = arg_as_string a1 in
        (match uu____4696 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4702 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2) in
             (match uu____4702 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2 in
                  let uu____4715 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r in
                  FStar_Pervasives_Native.Some uu____4715
              | uu____4716 -> FStar_Pervasives_Native.None)
         | uu____4721 -> FStar_Pervasives_Native.None)
    | uu____4724 -> FStar_Pervasives_Native.None in
  let string_of_int1 rng i =
    let uu____4734 = FStar_BigInt.string_of_big_int i in
    FStar_Syntax_Embeddings.embed_string rng uu____4734 in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false") in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r in
  let mk_range1 uu____4758 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____4769 =
          let uu____4790 = arg_as_string fn in
          let uu____4793 = arg_as_int from_line in
          let uu____4796 = arg_as_int from_col in
          let uu____4799 = arg_as_int to_line in
          let uu____4802 = arg_as_int to_col in
          (uu____4790, uu____4793, uu____4796, uu____4799, uu____4802) in
        (match uu____4769 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____4833 =
                 let uu____4834 = FStar_BigInt.to_int_fs from_l in
                 let uu____4835 = FStar_BigInt.to_int_fs from_c in
                 FStar_Range.mk_pos uu____4834 uu____4835 in
               let uu____4836 =
                 let uu____4837 = FStar_BigInt.to_int_fs to_l in
                 let uu____4838 = FStar_BigInt.to_int_fs to_c in
                 FStar_Range.mk_pos uu____4837 uu____4838 in
               FStar_Range.mk_range fn1 uu____4833 uu____4836 in
             let uu____4839 = term_of_range r in
             FStar_Pervasives_Native.Some uu____4839
         | uu____4844 -> FStar_Pervasives_Native.None)
    | uu____4865 -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc args =
    let r = psc.psc_range in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ,uu____4892)::(a1,uu____4894)::(a2,uu____4896)::[] ->
        let uu____4933 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____4933 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____4946 -> FStar_Pervasives_Native.None)
    | uu____4947 -> failwith "Unexpected number of arguments" in
  let idstep psc args =
    match args with
    | (a1,uu____4974)::[] -> FStar_Pervasives_Native.Some a1
    | uu____4983 -> failwith "Unexpected number of arguments" in
  let basic_ops =
    let uu____5007 =
      let uu____5022 =
        let uu____5037 =
          let uu____5052 =
            let uu____5067 =
              let uu____5082 =
                let uu____5097 =
                  let uu____5112 =
                    let uu____5127 =
                      let uu____5142 =
                        let uu____5157 =
                          let uu____5172 =
                            let uu____5187 =
                              let uu____5202 =
                                let uu____5217 =
                                  let uu____5232 =
                                    let uu____5247 =
                                      let uu____5262 =
                                        let uu____5277 =
                                          let uu____5292 =
                                            let uu____5307 =
                                              let uu____5322 =
                                                let uu____5335 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"] in
                                                (uu____5335,
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
                                              let uu____5342 =
                                                let uu____5357 =
                                                  let uu____5370 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"] in
                                                  (uu____5370,
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
                                                let uu____5377 =
                                                  let uu____5392 =
                                                    let uu____5407 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"] in
                                                    (uu____5407,
                                                      (Prims.parse_int "2"),
                                                      string_concat') in
                                                  let uu____5416 =
                                                    let uu____5433 =
                                                      let uu____5448 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"] in
                                                      (uu____5448,
                                                        (Prims.parse_int "5"),
                                                        mk_range1) in
                                                    let uu____5457 =
                                                      let uu____5474 =
                                                        let uu____5493 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"] in
                                                        (uu____5493,
                                                          (Prims.parse_int
                                                             "1"), idstep) in
                                                      [uu____5474] in
                                                    uu____5433 :: uu____5457 in
                                                  uu____5392 :: uu____5416 in
                                                uu____5357 :: uu____5377 in
                                              uu____5322 :: uu____5342 in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____5307 in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____5292 in
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
                                          :: uu____5277 in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a453  ->
                                              (Obj.magic arg_as_bool) a453)
                                           (fun a454  ->
                                              fun a455  ->
                                                (Obj.magic string_of_bool1)
                                                  a454 a455)))
                                        :: uu____5262 in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a456  ->
                                            (Obj.magic arg_as_int) a456)
                                         (fun a457  ->
                                            fun a458  ->
                                              (Obj.magic string_of_int1) a457
                                                a458)))
                                      :: uu____5247 in
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
                                                        let uu____5710 =
                                                          FStar_BigInt.to_int_fs
                                                            x in
                                                        FStar_String.make
                                                          uu____5710 y)) a463
                                                a464 a465)))
                                    :: uu____5232 in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____5217 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____5202 in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____5187 in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____5172 in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____5157 in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____5142 in
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
                                          let uu____5877 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____5877)) a467 a468 a469)))
                      :: uu____5127 in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a470  -> (Obj.magic arg_as_int) a470)
                       (fun a471  ->
                          fun a472  ->
                            fun a473  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____5903 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____5903)) a471 a472 a473)))
                    :: uu____5112 in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a474  -> (Obj.magic arg_as_int) a474)
                     (fun a475  ->
                        fun a476  ->
                          fun a477  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____5929 =
                                        FStar_BigInt.le_big_int x y in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____5929)) a475 a476 a477)))
                  :: uu____5097 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a478  -> (Obj.magic arg_as_int) a478)
                   (fun a479  ->
                      fun a480  ->
                        fun a481  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____5955 =
                                      FStar_BigInt.lt_big_int x y in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____5955)) a479 a480 a481)))
                :: uu____5082 in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____5067 in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____5052 in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____5037 in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____5022 in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____5007 in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"] in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"] in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1 in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1 in
      let uu____6108 =
        let uu____6109 =
          let uu____6110 = FStar_Syntax_Syntax.as_arg c in [uu____6110] in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____6109 in
      uu____6108 FStar_Pervasives_Native.None r in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____6160 =
                let uu____6173 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                (uu____6173, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                     (fun a483  ->
                        fun a484  ->
                          fun a485  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6189  ->
                                    fun uu____6190  ->
                                      match (uu____6189, uu____6190) with
                                      | ((int_to_t1,x),(uu____6209,y)) ->
                                          let uu____6219 =
                                            FStar_BigInt.add_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6219)) a483 a484 a485))) in
              let uu____6220 =
                let uu____6235 =
                  let uu____6248 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                  (uu____6248, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a486  -> (Obj.magic arg_as_bounded_int) a486)
                       (fun a487  ->
                          fun a488  ->
                            fun a489  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6264  ->
                                      fun uu____6265  ->
                                        match (uu____6264, uu____6265) with
                                        | ((int_to_t1,x),(uu____6284,y)) ->
                                            let uu____6294 =
                                              FStar_BigInt.sub_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6294)) a487 a488 a489))) in
                let uu____6295 =
                  let uu____6310 =
                    let uu____6323 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                    (uu____6323, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a490  -> (Obj.magic arg_as_bounded_int) a490)
                         (fun a491  ->
                            fun a492  ->
                              fun a493  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6339  ->
                                        fun uu____6340  ->
                                          match (uu____6339, uu____6340) with
                                          | ((int_to_t1,x),(uu____6359,y)) ->
                                              let uu____6369 =
                                                FStar_BigInt.mult_big_int x y in
                                              int_as_bounded r int_to_t1
                                                uu____6369)) a491 a492 a493))) in
                  let uu____6370 =
                    let uu____6385 =
                      let uu____6398 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                      (uu____6398, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a494  -> (Obj.magic arg_as_bounded_int) a494)
                           (fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____6410  ->
                                        match uu____6410 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a495 a496))) in
                    [uu____6385] in
                  uu____6310 :: uu____6370 in
                uu____6235 :: uu____6295 in
              uu____6160 :: uu____6220)) in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____6524 =
                let uu____6537 = FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                (uu____6537, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                     (fun a498  ->
                        fun a499  ->
                          fun a500  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____6553  ->
                                    fun uu____6554  ->
                                      match (uu____6553, uu____6554) with
                                      | ((int_to_t1,x),(uu____6573,y)) ->
                                          let uu____6583 =
                                            FStar_BigInt.div_big_int x y in
                                          int_as_bounded r int_to_t1
                                            uu____6583)) a498 a499 a500))) in
              let uu____6584 =
                let uu____6599 =
                  let uu____6612 = FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                  (uu____6612, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a501  -> (Obj.magic arg_as_bounded_int) a501)
                       (fun a502  ->
                          fun a503  ->
                            fun a504  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____6628  ->
                                      fun uu____6629  ->
                                        match (uu____6628, uu____6629) with
                                        | ((int_to_t1,x),(uu____6648,y)) ->
                                            let uu____6658 =
                                              FStar_BigInt.mod_big_int x y in
                                            int_as_bounded r int_to_t1
                                              uu____6658)) a502 a503 a504))) in
                [uu____6599] in
              uu____6524 :: uu____6584)) in
    FStar_List.append add_sub_mul_v div_mod_unsigned in
  FStar_List.map as_primitive_step
    (FStar_List.append basic_ops bounded_arith_ops)
let equality_ops: primitive_step Prims.list =
  let interp_prop psc args =
    let r = psc.psc_range in
    match args with
    | (_typ,uu____6748)::(a1,uu____6750)::(a2,uu____6752)::[] ->
        let uu____6789 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6789 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6795 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6795.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6795.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6799 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6799.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6799.FStar_Syntax_Syntax.vars)
                })
         | uu____6800 -> FStar_Pervasives_Native.None)
    | (_typ,uu____6802)::uu____6803::(a1,uu____6805)::(a2,uu____6807)::[] ->
        let uu____6856 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu____6856 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___107_6862 = FStar_Syntax_Util.t_true in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___107_6862.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___107_6862.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___108_6866 = FStar_Syntax_Util.t_false in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___108_6866.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___108_6866.FStar_Syntax_Syntax.vars)
                })
         | uu____6867 -> FStar_Pervasives_Native.None)
    | uu____6868 -> failwith "Unexpected number of arguments" in
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
      let uu____6887 =
        let uu____6888 = FStar_Syntax_Util.un_alien t in
        FStar_All.pipe_right uu____6888 FStar_Dyn.undyn in
      FStar_Pervasives_Native.Some uu____6887
    with | uu____6894 -> FStar_Pervasives_Native.None
let mk_psc_subst:
  'Auu____6898 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____6898) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____6958  ->
           fun subst1  ->
             match uu____6958 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____6999,uu____7000)) ->
                      let uu____7059 = b in
                      (match uu____7059 with
                       | (bv,uu____7067) ->
                           let uu____7068 =
                             let uu____7069 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.fstar_reflection_types_binder_lid in
                             Prims.op_Negation uu____7069 in
                           if uu____7068
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term in
                              let uu____7074 = unembed_binder term1 in
                              match uu____7074 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____7081 =
                                      let uu___111_7082 = bv in
                                      let uu____7083 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___111_7082.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___111_7082.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____7083
                                      } in
                                    FStar_Syntax_Syntax.freshen_bv uu____7081 in
                                  let b_for_x =
                                    let uu____7087 =
                                      let uu____7094 =
                                        FStar_Syntax_Syntax.bv_to_name b1 in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____7094) in
                                    FStar_Syntax_Syntax.NT uu____7087 in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___78_7103  ->
                                         match uu___78_7103 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____7104,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____7106;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____7107;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____7112 -> true) subst1 in
                                  b_for_x :: subst2))
                  | uu____7113 -> subst1)) env []
let reduce_primops:
  'Auu____7130 'Auu____7131 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7131) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7130 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let uu____7172 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Primops cfg.steps) in
          if uu____7172
          then tm
          else
            (let uu____7174 = FStar_Syntax_Util.head_and_args tm in
             match uu____7174 with
             | (head1,args) ->
                 let uu____7211 =
                   let uu____7212 = FStar_Syntax_Util.un_uinst head1 in
                   uu____7212.FStar_Syntax_Syntax.n in
                 (match uu____7211 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____7216 =
                        FStar_List.tryFind
                          (fun ps  ->
                             FStar_Syntax_Syntax.fv_eq_lid fv ps.name)
                          cfg.primitive_steps in
                      (match uu____7216 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____7233  ->
                                   let uu____7234 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name in
                                   let uu____7235 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args) in
                                   let uu____7242 =
                                     FStar_Util.string_of_int prim_step.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____7234 uu____7235 uu____7242);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____7247  ->
                                   let uu____7248 =
                                     FStar_Syntax_Print.term_to_string tm in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____7248);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____7251  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 } in
                               let uu____7253 =
                                 prim_step.interpretation psc args in
                               match uu____7253 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____7259  ->
                                         let uu____7260 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____7260);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____7266  ->
                                         let uu____7267 =
                                           FStar_Syntax_Print.term_to_string
                                             tm in
                                         let uu____7268 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____7267 uu____7268);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____7269 ->
                           (log_primops cfg
                              (fun uu____7273  ->
                                 let uu____7274 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____7274);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7278  ->
                            let uu____7279 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7279);
                       (match args with
                        | (a1,uu____7281)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____7298 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____7310  ->
                            let uu____7311 =
                              FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____7311);
                       (match args with
                        | (t,uu____7313)::(r,uu____7315)::[] ->
                            let uu____7342 =
                              FStar_Syntax_Embeddings.unembed_range r in
                            (match uu____7342 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___112_7346 = t in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___112_7346.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___112_7346.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____7349 -> tm))
                  | uu____7358 -> tm))
let reduce_equality:
  'Auu____7363 'Auu____7364 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7364) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7363 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___113_7402 = cfg in
         {
           steps = [Primops];
           tcenv = (uu___113_7402.tcenv);
           delta_level = (uu___113_7402.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___113_7402.strong);
           memoize_lazy = (uu___113_7402.memoize_lazy)
         }) tm
let maybe_simplify_aux:
  'Auu____7409 'Auu____7410 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____7410) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____7409 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm in
          let uu____7452 =
            FStar_All.pipe_left Prims.op_Negation
              (FStar_List.contains Simplify cfg.steps) in
          if uu____7452
          then tm1
          else
            (let w t =
               let uu___114_7464 = t in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_7464.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_7464.FStar_Syntax_Syntax.vars)
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
               | uu____7481 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu____7486 = FStar_Syntax_Util.is_sub_singleton t in
               if uu____7486
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____7507 =
                 match uu____7507 with
                 | (t1,q) ->
                     let uu____7520 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu____7520 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____7548 -> (t1, q)) in
               let uu____7557 = FStar_Syntax_Util.head_and_args t in
               match uu____7557 with
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
                         FStar_Syntax_Syntax.pos = uu____7654;
                         FStar_Syntax_Syntax.vars = uu____7655;_},uu____7656);
                    FStar_Syntax_Syntax.pos = uu____7657;
                    FStar_Syntax_Syntax.vars = uu____7658;_},args)
                 ->
                 let uu____7684 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____7684
                 then
                   let uu____7685 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____7685 with
                    | (FStar_Pervasives_Native.Some (true ),uu____7740)::
                        (uu____7741,(arg,uu____7743))::[] ->
                        maybe_auto_squash arg
                    | (uu____7808,(arg,uu____7810))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____7811)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____7876)::uu____7877::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____7940::(FStar_Pervasives_Native.Some (false
                                   ),uu____7941)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____8004 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____8020 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____8020
                    then
                      let uu____8021 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____8021 with
                      | (FStar_Pervasives_Native.Some (true ),uu____8076)::uu____8077::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____8140::(FStar_Pervasives_Native.Some (true
                                     ),uu____8141)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____8204)::
                          (uu____8205,(arg,uu____8207))::[] ->
                          maybe_auto_squash arg
                      | (uu____8272,(arg,uu____8274))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____8275)::[]
                          -> maybe_auto_squash arg
                      | uu____8340 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____8356 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____8356
                       then
                         let uu____8357 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____8357 with
                         | uu____8412::(FStar_Pervasives_Native.Some (true
                                        ),uu____8413)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____8476)::uu____8477::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____8540)::
                             (uu____8541,(arg,uu____8543))::[] ->
                             maybe_auto_squash arg
                         | (uu____8608,(p,uu____8610))::(uu____8611,(q,uu____8613))::[]
                             ->
                             let uu____8678 = FStar_Syntax_Util.term_eq p q in
                             (if uu____8678
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____8680 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____8696 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____8696
                          then
                            let uu____8697 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____8697 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____8752)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____8791)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____8830 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____8846 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____8846
                             then
                               match args with
                               | (t,uu____8848)::[] ->
                                   let uu____8865 =
                                     let uu____8866 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8866.FStar_Syntax_Syntax.n in
                                   (match uu____8865 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8869::[],body,uu____8871) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8898 -> tm1)
                                    | uu____8901 -> tm1)
                               | (uu____8902,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____8903))::
                                   (t,uu____8905)::[] ->
                                   let uu____8944 =
                                     let uu____8945 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____8945.FStar_Syntax_Syntax.n in
                                   (match uu____8944 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____8948::[],body,uu____8950) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____8977 -> tm1)
                                    | uu____8980 -> tm1)
                               | uu____8981 -> tm1
                             else
                               (let uu____8991 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____8991
                                then
                                  match args with
                                  | (t,uu____8993)::[] ->
                                      let uu____9010 =
                                        let uu____9011 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9011.FStar_Syntax_Syntax.n in
                                      (match uu____9010 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9014::[],body,uu____9016)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9043 -> tm1)
                                       | uu____9046 -> tm1)
                                  | (uu____9047,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____9048))::(t,uu____9050)::[] ->
                                      let uu____9089 =
                                        let uu____9090 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____9090.FStar_Syntax_Syntax.n in
                                      (match uu____9089 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____9093::[],body,uu____9095)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____9122 -> tm1)
                                       | uu____9125 -> tm1)
                                  | uu____9126 -> tm1
                                else
                                  (let uu____9136 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____9136
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9137;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9138;_},uu____9139)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____9156;
                                          FStar_Syntax_Syntax.vars =
                                            uu____9157;_},uu____9158)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____9175 -> tm1
                                   else
                                     (let uu____9185 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____9185 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____9205 ->
                                          reduce_equality cfg env stack tm1)))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____9215;
                    FStar_Syntax_Syntax.vars = uu____9216;_},args)
                 ->
                 let uu____9238 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid in
                 if uu____9238
                 then
                   let uu____9239 =
                     FStar_All.pipe_right args (FStar_List.map simplify1) in
                   (match uu____9239 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9294)::
                        (uu____9295,(arg,uu____9297))::[] ->
                        maybe_auto_squash arg
                    | (uu____9362,(arg,uu____9364))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9365)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9430)::uu____9431::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9494::(FStar_Pervasives_Native.Some (false
                                   ),uu____9495)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9558 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9574 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid in
                    if uu____9574
                    then
                      let uu____9575 =
                        FStar_All.pipe_right args (FStar_List.map simplify1) in
                      match uu____9575 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9630)::uu____9631::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9694::(FStar_Pervasives_Native.Some (true
                                     ),uu____9695)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9758)::
                          (uu____9759,(arg,uu____9761))::[] ->
                          maybe_auto_squash arg
                      | (uu____9826,(arg,uu____9828))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9829)::[]
                          -> maybe_auto_squash arg
                      | uu____9894 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9910 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid in
                       if uu____9910
                       then
                         let uu____9911 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1) in
                         match uu____9911 with
                         | uu____9966::(FStar_Pervasives_Native.Some (true
                                        ),uu____9967)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____10030)::uu____10031::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____10094)::
                             (uu____10095,(arg,uu____10097))::[] ->
                             maybe_auto_squash arg
                         | (uu____10162,(p,uu____10164))::(uu____10165,
                                                           (q,uu____10167))::[]
                             ->
                             let uu____10232 = FStar_Syntax_Util.term_eq p q in
                             (if uu____10232
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____10234 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____10250 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.not_lid in
                          if uu____10250
                          then
                            let uu____10251 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1) in
                            match uu____10251 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10306)::[] ->
                                w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10345)::[] ->
                                w FStar_Syntax_Util.t_true
                            | uu____10384 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10400 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.forall_lid in
                             if uu____10400
                             then
                               match args with
                               | (t,uu____10402)::[] ->
                                   let uu____10419 =
                                     let uu____10420 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10420.FStar_Syntax_Syntax.n in
                                   (match uu____10419 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10423::[],body,uu____10425) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10452 -> tm1)
                                    | uu____10455 -> tm1)
                               | (uu____10456,FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu____10457))::
                                   (t,uu____10459)::[] ->
                                   let uu____10498 =
                                     let uu____10499 =
                                       FStar_Syntax_Subst.compress t in
                                     uu____10499.FStar_Syntax_Syntax.n in
                                   (match uu____10498 with
                                    | FStar_Syntax_Syntax.Tm_abs
                                        (uu____10502::[],body,uu____10504) ->
                                        (match simp_t body with
                                         | FStar_Pervasives_Native.Some (true
                                             ) -> w FStar_Syntax_Util.t_true
                                         | uu____10531 -> tm1)
                                    | uu____10534 -> tm1)
                               | uu____10535 -> tm1
                             else
                               (let uu____10545 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.exists_lid in
                                if uu____10545
                                then
                                  match args with
                                  | (t,uu____10547)::[] ->
                                      let uu____10564 =
                                        let uu____10565 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10565.FStar_Syntax_Syntax.n in
                                      (match uu____10564 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10568::[],body,uu____10570)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10597 -> tm1)
                                       | uu____10600 -> tm1)
                                  | (uu____10601,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10602))::(t,uu____10604)::[] ->
                                      let uu____10643 =
                                        let uu____10644 =
                                          FStar_Syntax_Subst.compress t in
                                        uu____10644.FStar_Syntax_Syntax.n in
                                      (match uu____10643 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10647::[],body,uu____10649)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (false ) ->
                                                w FStar_Syntax_Util.t_false
                                            | uu____10676 -> tm1)
                                       | uu____10679 -> tm1)
                                  | uu____10680 -> tm1
                                else
                                  (let uu____10690 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.b2t_lid in
                                   if uu____10690
                                   then
                                     match args with
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (true ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10691;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10692;_},uu____10693)::[]
                                         -> w FStar_Syntax_Util.t_true
                                     | ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_constant
                                            (FStar_Const.Const_bool (false ));
                                          FStar_Syntax_Syntax.pos =
                                            uu____10710;
                                          FStar_Syntax_Syntax.vars =
                                            uu____10711;_},uu____10712)::[]
                                         -> w FStar_Syntax_Util.t_false
                                     | uu____10729 -> tm1
                                   else
                                     (let uu____10739 =
                                        FStar_Syntax_Util.is_auto_squash tm1 in
                                      match uu____10739 with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.U_zero ,t)
                                          when
                                          FStar_Syntax_Util.is_sub_singleton
                                            t
                                          -> t
                                      | uu____10759 ->
                                          reduce_equality cfg env stack tm1)))))))
             | uu____10768 -> tm1)
let maybe_simplify:
  'Auu____10775 'Auu____10776 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10776) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10775 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm in
          (let uu____10819 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv)
               (FStar_Options.Other "380") in
           if uu____10819
           then
             let uu____10820 = FStar_Syntax_Print.term_to_string tm in
             let uu____10821 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if FStar_List.contains Simplify cfg.steps then "" else "NOT ")
               uu____10820 uu____10821
           else ());
          tm'
let is_norm_request:
  'Auu____10827 .
    FStar_Syntax_Syntax.term -> 'Auu____10827 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10840 =
        let uu____10847 =
          let uu____10848 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10848.FStar_Syntax_Syntax.n in
        (uu____10847, args) in
      match uu____10840 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10854::uu____10855::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10859::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10864::uu____10865::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10868 -> false
let tr_norm_step: FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___79_10879  ->
    match uu___79_10879 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10885 =
          let uu____10888 =
            let uu____10889 = FStar_List.map FStar_Ident.lid_of_str names1 in
            UnfoldOnly uu____10889 in
          [uu____10888] in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10885
let tr_norm_steps:
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s
let get_norm_request:
  'Auu____10904 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10904) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10942 =
          let uu____10945 =
            let uu____10950 =
              FStar_Syntax_Embeddings.unembed_list
                FStar_Syntax_Embeddings.unembed_norm_step in
            uu____10950 s in
          FStar_All.pipe_right uu____10945 FStar_Util.must in
        FStar_All.pipe_right uu____10942 tr_norm_steps in
      match args with
      | uu____10975::(tm,uu____10977)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (tm,uu____11000)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify] in
          (s, tm)
      | (steps,uu____11015)::uu____11016::(tm,uu____11018)::[] ->
          let add_exclude s z =
            if Prims.op_Negation (FStar_List.contains z s)
            then (Exclude z) :: s
            else s in
          let s =
            let uu____11058 =
              let uu____11061 = full_norm steps in parse_steps uu____11061 in
            Beta :: uu____11058 in
          let s1 = add_exclude s Zeta in
          let s2 = add_exclude s1 Iota in (s2, tm)
      | uu____11070 -> failwith "Impossible"
let is_reify_head: stack_elt Prims.list -> Prims.bool =
  fun uu___80_11087  ->
    match uu___80_11087 with
    | (App
        (uu____11090,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11091;
                       FStar_Syntax_Syntax.vars = uu____11092;_},uu____11093,uu____11094))::uu____11095
        -> true
    | uu____11102 -> false
let firstn:
  'Auu____11108 .
    Prims.int ->
      'Auu____11108 Prims.list ->
        ('Auu____11108 Prims.list,'Auu____11108 Prims.list)
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
          (uu____11144,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11145;
                         FStar_Syntax_Syntax.vars = uu____11146;_},uu____11147,uu____11148))::uu____11149
          -> FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)
      | uu____11156 -> false
let rec norm:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 = FStar_Syntax_Subst.compress t in
          log cfg
            (fun uu____11303  ->
               let uu____11304 = FStar_Syntax_Print.tag_of_term t1 in
               let uu____11305 = FStar_Syntax_Print.term_to_string t1 in
               let uu____11306 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____11313 =
                 let uu____11314 =
                   let uu____11317 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11317 in
                 stack_to_string uu____11314 in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11304 uu____11305 uu____11306 uu____11313);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_delayed uu____11340 ->
               failwith "Impossible: got a delayed substitution"
           | FStar_Syntax_Syntax.Tm_uvar uu____11365 when
               FStar_All.pipe_right cfg.steps
                 (FStar_List.contains CheckNoUvars)
               ->
               let uu____11382 =
                 let uu____11383 =
                   FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                 let uu____11384 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format2
                   "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                   uu____11383 uu____11384 in
               failwith uu____11382
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_uvar uu____11385 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11402 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11403 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11404;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11405;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11408;
                 FStar_Syntax_Syntax.fv_delta = uu____11409;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11410;
                 FStar_Syntax_Syntax.fv_delta = uu____11411;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11412);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar fv when
               let uu____11420 = FStar_Syntax_Syntax.lid_of_fv fv in
               FStar_TypeChecker_Env.is_action cfg.tcenv uu____11420 ->
               let b = should_reify cfg stack in
               (log cfg
                  (fun uu____11426  ->
                     let uu____11427 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11428 = FStar_Util.string_of_bool b in
                     FStar_Util.print2
                       ">>> For DM4F action %s, should_reify = %s\n"
                       uu____11427 uu____11428);
                if b
                then
                  (let uu____11429 = FStar_List.tl stack in
                   do_unfold_fv cfg env uu____11429 t1 fv)
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
                 let uu___115_11468 = t1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd2, args1));
                   FStar_Syntax_Syntax.pos =
                     (uu___115_11468.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___115_11468.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((let uu____11501 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains NoFullNorm) in
                 Prims.op_Negation uu____11501) && (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___116_11509 = cfg in
                 let uu____11510 =
                   FStar_List.filter
                     (fun uu___81_11513  ->
                        match uu___81_11513 with
                        | UnfoldOnly uu____11514 -> false
                        | NoDeltaSteps  -> false
                        | uu____11517 -> true) cfg.steps in
                 {
                   steps = uu____11510;
                   tcenv = (uu___116_11509.tcenv);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___116_11509.primitive_steps);
                   strong = (uu___116_11509.strong);
                   memoize_lazy = (uu___116_11509.memoize_lazy)
                 } in
               let uu____11518 = get_norm_request (norm cfg' env []) args in
               (match uu____11518 with
                | (s,tm) ->
                    let delta_level =
                      let uu____11534 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___82_11539  ->
                                match uu___82_11539 with
                                | UnfoldUntil uu____11540 -> true
                                | UnfoldOnly uu____11541 -> true
                                | uu____11544 -> false)) in
                      if uu____11534
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta] in
                    let cfg'1 =
                      let uu___117_11549 = cfg in
                      {
                        steps = s;
                        tcenv = (uu___117_11549.tcenv);
                        delta_level;
                        primitive_steps = (uu___117_11549.primitive_steps);
                        strong = (uu___117_11549.strong);
                        memoize_lazy = (uu___117_11549.memoize_lazy)
                      } in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack in
                      let uu____11556 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug cfg.tcenv)
                          (FStar_Options.Other "print_normalized_terms") in
                      if uu____11556
                      then
                        let uu____11559 =
                          let uu____11560 =
                            let uu____11565 = FStar_Util.now () in
                            (t1, uu____11565) in
                          Debug uu____11560 in
                        uu____11559 :: tail1
                      else tail1 in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u in
               let uu____11569 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____11569
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               let uu____11576 =
                 FStar_All.pipe_right cfg.steps
                   (FStar_List.contains EraseUniverses) in
               if uu____11576
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____11579 =
                      let uu____11586 =
                        FStar_List.map (norm_universe cfg env) us in
                      (uu____11586, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu____11579 in
                  let stack1 = us1 :: stack in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar f ->
               let should_delta =
                 FStar_All.pipe_right cfg.delta_level
                   (FStar_Util.for_some
                      (fun uu___83_11599  ->
                         match uu___83_11599 with
                         | FStar_TypeChecker_Env.UnfoldTac  -> false
                         | FStar_TypeChecker_Env.NoDelta  -> false
                         | FStar_TypeChecker_Env.Inlining  -> true
                         | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                             true
                         | FStar_TypeChecker_Env.Unfold l ->
                             FStar_TypeChecker_Common.delta_depth_greater_than
                               f.FStar_Syntax_Syntax.fv_delta l)) in
               let should_delta1 =
                 let uu____11602 =
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
                 if uu____11602
                 then false
                 else
                   (let uu____11604 =
                      FStar_All.pipe_right cfg.steps
                        (FStar_List.tryFind
                           (fun uu___84_11611  ->
                              match uu___84_11611 with
                              | UnfoldOnly uu____11612 -> true
                              | uu____11615 -> false)) in
                    match uu____11604 with
                    | FStar_Pervasives_Native.Some (UnfoldOnly lids) ->
                        should_delta &&
                          (FStar_Util.for_some
                             (FStar_Syntax_Syntax.fv_eq_lid f) lids)
                    | uu____11619 -> should_delta) in
               (log cfg
                  (fun uu____11627  ->
                     let uu____11628 = FStar_Syntax_Print.term_to_string t1 in
                     let uu____11629 =
                       FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                     let uu____11630 =
                       FStar_Util.string_of_bool should_delta1 in
                     FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n"
                       uu____11628 uu____11629 uu____11630);
                if Prims.op_Negation should_delta1
                then rebuild cfg env stack t1
                else do_unfold_fv cfg env stack t1 f)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____11633 = lookup_bvar env x in
               (match uu____11633 with
                | Univ uu____11636 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (Prims.op_Negation
                           (FStar_List.contains (Exclude Zeta) cfg.steps))
                    then
                      let uu____11685 = FStar_ST.op_Bang r in
                      (match uu____11685 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____11803  ->
                                 let uu____11804 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu____11805 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____11804
                                   uu____11805);
                            (let uu____11806 =
                               let uu____11807 =
                                 FStar_Syntax_Subst.compress t' in
                               uu____11807.FStar_Syntax_Syntax.n in
                             match uu____11806 with
                             | FStar_Syntax_Syntax.Tm_abs uu____11810 ->
                                 norm cfg env2 stack t'
                             | uu____11827 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____11897)::uu____11898 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____11907)::uu____11908 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____11918,uu____11919))::stack_rest ->
                    (match c with
                     | Univ uu____11923 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____11932 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____11953  ->
                                    let uu____11954 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11954);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____11994  ->
                                    let uu____11995 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____11995);
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
                       (fun uu____12073  ->
                          let uu____12074 =
                            FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12074);
                     norm cfg env stack1 t1)
                | (Debug uu____12075)::uu____12076 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12083 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12083
                    else
                      (let uu____12085 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12085 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12127  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12155 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12155
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12165 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12165)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12170 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12170.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12170.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12171 -> lopt in
                           (log cfg
                              (fun uu____12177  ->
                                 let uu____12178 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12178);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12187 = cfg in
                               {
                                 steps = (uu___119_12187.steps);
                                 tcenv = (uu___119_12187.tcenv);
                                 delta_level = (uu___119_12187.delta_level);
                                 primitive_steps =
                                   (uu___119_12187.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12187.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12198)::uu____12199 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12206 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12206
                    else
                      (let uu____12208 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12208 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12250  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12278 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12278
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12288 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12288)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12293 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12293.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12293.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12294 -> lopt in
                           (log cfg
                              (fun uu____12300  ->
                                 let uu____12301 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12301);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12310 = cfg in
                               {
                                 steps = (uu___119_12310.steps);
                                 tcenv = (uu___119_12310.tcenv);
                                 delta_level = (uu___119_12310.delta_level);
                                 primitive_steps =
                                   (uu___119_12310.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12310.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12321)::uu____12322 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12333 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12333
                    else
                      (let uu____12335 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12335 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12377  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12405 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12405
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12415 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12415)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12420 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12420.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12420.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12421 -> lopt in
                           (log cfg
                              (fun uu____12427  ->
                                 let uu____12428 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12428);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12437 = cfg in
                               {
                                 steps = (uu___119_12437.steps);
                                 tcenv = (uu___119_12437.tcenv);
                                 delta_level = (uu___119_12437.delta_level);
                                 primitive_steps =
                                   (uu___119_12437.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12437.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____12448)::uu____12449 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12460 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12460
                    else
                      (let uu____12462 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12462 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12504  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12532 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12532
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12542 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12542)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12547 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12547.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12547.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12548 -> lopt in
                           (log cfg
                              (fun uu____12554  ->
                                 let uu____12555 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12555);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12564 = cfg in
                               {
                                 steps = (uu___119_12564.steps);
                                 tcenv = (uu___119_12564.tcenv);
                                 delta_level = (uu___119_12564.delta_level);
                                 primitive_steps =
                                   (uu___119_12564.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12564.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____12575)::uu____12576 ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12591 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12591
                    else
                      (let uu____12593 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12593 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12635  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12663 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12663
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12673 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12673)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12678 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12678.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12678.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12679 -> lopt in
                           (log cfg
                              (fun uu____12685  ->
                                 let uu____12686 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12686);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12695 = cfg in
                               {
                                 steps = (uu___119_12695.steps);
                                 tcenv = (uu___119_12695.tcenv);
                                 delta_level = (uu___119_12695.delta_level);
                                 primitive_steps =
                                   (uu___119_12695.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12695.memoize_lazy)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if FStar_List.contains Weak cfg.steps
                    then
                      let uu____12706 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____12706
                    else
                      (let uu____12708 =
                         FStar_Syntax_Subst.open_term' bs body in
                       match uu____12708 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12750  -> dummy :: env1) env) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   let uu____12778 =
                                     FStar_All.pipe_right cfg.steps
                                       (FStar_List.contains CheckNoUvars) in
                                   if uu____12778
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____12788 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu____12788)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___118_12793 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___118_12793.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___118_12793.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12794 -> lopt in
                           (log cfg
                              (fun uu____12800  ->
                                 let uu____12801 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12801);
                            (let stack1 = (Cfg cfg) :: stack in
                             let cfg1 =
                               let uu___119_12810 = cfg in
                               {
                                 steps = (uu___119_12810.steps);
                                 tcenv = (uu___119_12810.tcenv);
                                 delta_level = (uu___119_12810.delta_level);
                                 primitive_steps =
                                   (uu___119_12810.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___119_12810.memoize_lazy)
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
                      (fun uu____12859  ->
                         fun stack1  ->
                           match uu____12859 with
                           | (a,aq) ->
                               let uu____12871 =
                                 let uu____12872 =
                                   let uu____12879 =
                                     let uu____12880 =
                                       let uu____12911 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None in
                                       (env, a, uu____12911, false) in
                                     Clos uu____12880 in
                                   (uu____12879, aq,
                                     (t1.FStar_Syntax_Syntax.pos)) in
                                 Arg uu____12872 in
                               uu____12871 :: stack1) args) in
               (log cfg
                  (fun uu____12995  ->
                     let uu____12996 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args) in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____12996);
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
                             ((let uu___120_13032 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___120_13032.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___120_13032.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2
                  | uu____13033 ->
                      let uu____13038 = closure_as_term cfg env t1 in
                      rebuild cfg env stack uu____13038)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort in
                  let uu____13041 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f in
                  match uu____13041 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1 in
                      let t2 =
                        let uu____13072 =
                          let uu____13073 =
                            let uu____13080 =
                              FStar_Syntax_Subst.close closing f2 in
                            ((let uu___121_13082 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___121_13082.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___121_13082.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13080) in
                          FStar_Syntax_Syntax.Tm_refine uu____13073 in
                        mk uu____13072 t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if FStar_List.contains Weak cfg.steps
               then
                 let uu____13101 = closure_as_term cfg env t1 in
                 rebuild cfg env stack uu____13101
               else
                 (let uu____13103 = FStar_Syntax_Subst.open_comp bs c in
                  match uu____13103 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13111 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13135  -> dummy :: env1) env) in
                        norm_comp cfg uu____13111 c1 in
                      let t2 =
                        let uu____13157 = norm_binders cfg env bs1 in
                        FStar_Syntax_Util.arrow uu____13157 c2 in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13216)::uu____13217 ->
                    (log cfg
                       (fun uu____13228  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13229)::uu____13230 ->
                    (log cfg
                       (fun uu____13241  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13242,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13243;
                                   FStar_Syntax_Syntax.vars = uu____13244;_},uu____13245,uu____13246))::uu____13247
                    ->
                    (log cfg
                       (fun uu____13256  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13257)::uu____13258 ->
                    (log cfg
                       (fun uu____13269  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13270 ->
                    (log cfg
                       (fun uu____13273  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11 in
                      log cfg
                        (fun uu____13277  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13294 = norm cfg env [] t2 in
                             FStar_Util.Inl uu____13294
                         | FStar_Util.Inr c ->
                             let uu____13302 = norm_comp cfg env c in
                             FStar_Util.Inr uu____13302 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env []) in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13315 =
                               let uu____13316 =
                                 let uu____13343 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13343, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13316 in
                             mk uu____13315 t1.FStar_Syntax_Syntax.pos in
                           norm cfg1 env stack1 t2
                       | uu____13362 ->
                           let uu____13363 =
                             let uu____13364 =
                               let uu____13365 =
                                 let uu____13392 =
                                   FStar_Syntax_Util.unascribe t12 in
                                 (uu____13392, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13365 in
                             mk uu____13364 t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env stack uu____13363))))
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
                         let uu____13502 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu____13502 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___122_13522 = cfg in
                               let uu____13523 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs in
                               {
                                 steps = (uu___122_13522.steps);
                                 tcenv = uu____13523;
                                 delta_level = (uu___122_13522.delta_level);
                                 primitive_steps =
                                   (uu___122_13522.primitive_steps);
                                 strong = (uu___122_13522.strong);
                                 memoize_lazy = (uu___122_13522.memoize_lazy)
                               } in
                             let norm1 t2 =
                               let uu____13528 =
                                 let uu____13529 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env [] uu____13529 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13528 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___123_13532 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___123_13532.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___123_13532.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef
                             })) in
               let uu____13533 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env stack uu____13533
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13544,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13545;
                               FStar_Syntax_Syntax.lbunivs = uu____13546;
                               FStar_Syntax_Syntax.lbtyp = uu____13547;
                               FStar_Syntax_Syntax.lbeff = uu____13548;
                               FStar_Syntax_Syntax.lbdef = uu____13549;_}::uu____13550),uu____13551)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff in
               let uu____13587 =
                 (let uu____13590 =
                    FStar_All.pipe_right cfg.steps
                      (FStar_List.contains NoDeltaSteps) in
                  Prims.op_Negation uu____13590) &&
                   (((FStar_Syntax_Util.is_pure_effect n1) ||
                       (FStar_Syntax_Util.is_ghost_effect n1))
                      &&
                      (let uu____13592 =
                         FStar_All.pipe_right cfg.steps
                           (FStar_List.contains
                              PureSubtermsWithinComputations) in
                       Prims.op_Negation uu____13592)) in
               if uu____13587
               then
                 let binder =
                   let uu____13594 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu____13594 in
                 let env1 =
                   let uu____13604 =
                     let uu____13611 =
                       let uu____13612 =
                         let uu____13643 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13643,
                           false) in
                       Clos uu____13612 in
                     ((FStar_Pervasives_Native.Some binder), uu____13611) in
                   uu____13604 :: env in
                 (log cfg
                    (fun uu____13736  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13738 =
                    let uu____13743 =
                      let uu____13744 =
                        let uu____13745 =
                          FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname
                            FStar_Util.left in
                        FStar_All.pipe_right uu____13745
                          FStar_Syntax_Syntax.mk_binder in
                      [uu____13744] in
                    FStar_Syntax_Subst.open_term uu____13743 body in
                  match uu____13738 with
                  | (bs,body1) ->
                      (log cfg
                         (fun uu____13754  ->
                            FStar_Util.print_string
                              "+++ Normalizing Tm_let -- type\n");
                       (let ty = norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                        let lbname =
                          let x =
                            let uu____13762 = FStar_List.hd bs in
                            FStar_Pervasives_Native.fst uu____13762 in
                          FStar_Util.Inl
                            (let uu___124_13772 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___124_13772.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___124_13772.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = ty
                             }) in
                        log cfg
                          (fun uu____13775  ->
                             FStar_Util.print_string
                               "+++ Normalizing Tm_let -- definiens\n");
                        (let lb1 =
                           let uu___125_13777 = lb in
                           let uu____13778 =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbdef in
                           {
                             FStar_Syntax_Syntax.lbname = lbname;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___125_13777.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = ty;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___125_13777.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____13778
                           } in
                         let env' =
                           FStar_All.pipe_right bs
                             (FStar_List.fold_left
                                (fun env1  ->
                                   fun uu____13813  -> dummy :: env1) env) in
                         let stack1 = (Cfg cfg) :: stack in
                         let cfg1 =
                           let uu___126_13836 = cfg in
                           {
                             steps = (uu___126_13836.steps);
                             tcenv = (uu___126_13836.tcenv);
                             delta_level = (uu___126_13836.delta_level);
                             primitive_steps =
                               (uu___126_13836.primitive_steps);
                             strong = true;
                             memoize_lazy = (uu___126_13836.memoize_lazy)
                           } in
                         log cfg1
                           (fun uu____13839  ->
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
               let uu____13856 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu____13856 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu____13892 =
                               let uu___127_13893 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___127_13893.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___127_13893.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Util.Inl uu____13892 in
                           let uu____13894 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu____13894 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs in
                               let env1 =
                                 let uu____13920 =
                                   FStar_List.map (fun uu____13936  -> dummy)
                                     lbs1 in
                                 let uu____13937 =
                                   let uu____13946 =
                                     FStar_List.map
                                       (fun uu____13966  -> dummy) xs1 in
                                   FStar_List.append uu____13946 env in
                                 FStar_List.append uu____13920 uu____13937 in
                               let def_body1 = norm cfg env1 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13990 =
                                       let uu___128_13991 = rc in
                                       let uu____13992 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___128_13991.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13992;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___128_13991.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu____13990
                                 | uu____13999 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___129_14003 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___129_14003.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___129_14003.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def
                               }) lbs1 in
                    let env' =
                      let uu____14013 =
                        FStar_List.map (fun uu____14029  -> dummy) lbs2 in
                      FStar_List.append uu____14013 env in
                    let body2 = norm cfg env' [] body1 in
                    let uu____14037 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu____14037 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___130_14053 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___130_14053.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___130_14053.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               FStar_List.contains (Exclude Zeta) cfg.steps ->
               let uu____14080 = closure_as_term cfg env t1 in
               rebuild cfg env stack uu____14080
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14099 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14175  ->
                        match uu____14175 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___131_14296 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___131_14296.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___131_14296.FStar_Syntax_Syntax.sort)
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
               (match uu____14099 with
                | (rec_env,memos,uu____14509) ->
                    let uu____14562 =
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
                             let uu____14873 =
                               let uu____14880 =
                                 let uu____14881 =
                                   let uu____14912 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14912, false) in
                                 Clos uu____14881 in
                               (FStar_Pervasives_Native.None, uu____14880) in
                             uu____14873 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15022  ->
                     let uu____15023 =
                       FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15023);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15045 ->
                     if FStar_List.contains Unmeta cfg.steps
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15047::uu____15048 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15053) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_alien uu____15054 ->
                                 rebuild cfg env stack t1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____15085 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1 in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15099 =
                                    norm_pattern_args cfg env args in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15099
                              | uu____15110 -> m in
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
              let uu____15122 = FStar_Syntax_Syntax.range_of_fv f in
              FStar_TypeChecker_Env.set_range cfg.tcenv uu____15122 in
            let uu____15123 =
              FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            match uu____15123 with
            | FStar_Pervasives_Native.None  ->
                (log cfg
                   (fun uu____15136  ->
                      FStar_Util.print "Tm_fvar case 2\n" []);
                 rebuild cfg env stack t0)
            | FStar_Pervasives_Native.Some (us,t) ->
                (log cfg
                   (fun uu____15147  ->
                      let uu____15148 = FStar_Syntax_Print.term_to_string t0 in
                      let uu____15149 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____15148
                        uu____15149);
                 (let t1 =
                    let uu____15151 =
                      (FStar_All.pipe_right cfg.steps
                         (FStar_List.contains
                            (UnfoldUntil FStar_Syntax_Syntax.Delta_constant)))
                        &&
                        (let uu____15153 =
                           FStar_All.pipe_right cfg.steps
                             (FStar_List.contains UnfoldTac) in
                         Prims.op_Negation uu____15153) in
                    if uu____15151
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
                    | (UnivArgs (us',uu____15163))::stack1 ->
                        let env1 =
                          FStar_All.pipe_right us'
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun u  ->
                                    (FStar_Pervasives_Native.None, (Univ u))
                                    :: env1) env) in
                        norm cfg env1 stack1 t1
                    | uu____15218 when
                        FStar_All.pipe_right cfg.steps
                          (FStar_List.contains EraseUniverses)
                        -> norm cfg env stack t1
                    | uu____15221 ->
                        let uu____15224 =
                          let uu____15225 =
                            FStar_Syntax_Print.lid_to_string
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu____15225 in
                        failwith uu____15224
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
                let uu____15246 =
                  FStar_All.pipe_right cfg.steps
                    (FStar_List.contains PureSubtermsWithinComputations) in
                if uu____15246
                then
                  let uu___132_15247 = cfg in
                  {
                    steps =
                      [PureSubtermsWithinComputations;
                      Primops;
                      AllowUnboundUniverses;
                      EraseUniverses;
                      Exclude Zeta;
                      NoDeltaSteps];
                    tcenv = (uu___132_15247.tcenv);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___132_15247.primitive_steps);
                    strong = (uu___132_15247.strong);
                    memoize_lazy = (uu___132_15247.memoize_lazy)
                  }
                else
                  (let uu___133_15249 = cfg in
                   {
                     steps = (FStar_List.append [Exclude Zeta] cfg.steps);
                     tcenv = (uu___133_15249.tcenv);
                     delta_level = (uu___133_15249.delta_level);
                     primitive_steps = (uu___133_15249.primitive_steps);
                     strong = (uu___133_15249.strong);
                     memoize_lazy = (uu___133_15249.memoize_lazy)
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
                  (fun uu____15278  ->
                     let uu____15279 = FStar_Syntax_Print.tag_of_term head2 in
                     let uu____15280 =
                       FStar_Syntax_Print.term_to_string head2 in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____15279
                       uu____15280);
                (let uu____15281 =
                   let uu____15282 = FStar_Syntax_Subst.compress head2 in
                   uu____15282.FStar_Syntax_Syntax.n in
                 match uu____15281 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15300 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15300 with
                      | (uu____15301,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____15307 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____15315 =
                                   let uu____15316 =
                                     FStar_Syntax_Subst.compress e in
                                   uu____15316.FStar_Syntax_Syntax.n in
                                 match uu____15315 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____15322,uu____15323))
                                     ->
                                     let uu____15332 =
                                       let uu____15333 =
                                         FStar_Syntax_Subst.compress e1 in
                                       uu____15333.FStar_Syntax_Syntax.n in
                                     (match uu____15332 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____15339,msrc,uu____15341))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____15350 =
                                            FStar_Syntax_Subst.compress e2 in
                                          FStar_Pervasives_Native.Some
                                            uu____15350
                                      | uu____15351 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____15352 ->
                                     FStar_Pervasives_Native.None in
                               let uu____15353 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef in
                               (match uu____15353 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___134_15358 = lb in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___134_15358.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___134_15358.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___134_15358.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e
                                      } in
                                    let uu____15359 = FStar_List.tl stack in
                                    let uu____15360 =
                                      let uu____15361 =
                                        let uu____15364 =
                                          let uu____15365 =
                                            let uu____15378 =
                                              FStar_Syntax_Util.mk_reify body in
                                            ((false, [lb1]), uu____15378) in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____15365 in
                                        FStar_Syntax_Syntax.mk uu____15364 in
                                      uu____15361
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos in
                                    norm cfg env uu____15359 uu____15360
                                | FStar_Pervasives_Native.None  ->
                                    let uu____15394 =
                                      let uu____15395 = is_return body in
                                      match uu____15395 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____15399;
                                            FStar_Syntax_Syntax.vars =
                                              uu____15400;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____15405 -> false in
                                    if uu____15394
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
                                         let uu____15428 =
                                           let uu____15431 =
                                             let uu____15432 =
                                               let uu____15449 =
                                                 let uu____15452 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x in
                                                 [uu____15452] in
                                               (uu____15449, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc)) in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____15432 in
                                           FStar_Syntax_Syntax.mk uu____15431 in
                                         uu____15428
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos in
                                       let close1 = closure_as_term cfg env in
                                       let bind_inst =
                                         let uu____15468 =
                                           let uu____15469 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr in
                                           uu____15469.FStar_Syntax_Syntax.n in
                                         match uu____15468 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____15475::uu____15476::[])
                                             ->
                                             let uu____15483 =
                                               let uu____15486 =
                                                 let uu____15487 =
                                                   let uu____15494 =
                                                     let uu____15497 =
                                                       let uu____15498 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____15498 in
                                                     let uu____15499 =
                                                       let uu____15502 =
                                                         let uu____15503 =
                                                           close1 t in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____15503 in
                                                       [uu____15502] in
                                                     uu____15497 ::
                                                       uu____15499 in
                                                   (bind1, uu____15494) in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____15487 in
                                               FStar_Syntax_Syntax.mk
                                                 uu____15486 in
                                             uu____15483
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____15511 ->
                                             failwith
                                               "NIY : Reification of indexed effects" in
                                       let reified =
                                         let uu____15517 =
                                           let uu____15520 =
                                             let uu____15521 =
                                               let uu____15536 =
                                                 let uu____15539 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu____15540 =
                                                   let uu____15543 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu____15544 =
                                                     let uu____15547 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun in
                                                     let uu____15548 =
                                                       let uu____15551 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3 in
                                                       let uu____15552 =
                                                         let uu____15555 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun in
                                                         let uu____15556 =
                                                           let uu____15559 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu____15559] in
                                                         uu____15555 ::
                                                           uu____15556 in
                                                       uu____15551 ::
                                                         uu____15552 in
                                                     uu____15547 ::
                                                       uu____15548 in
                                                   uu____15543 :: uu____15544 in
                                                 uu____15539 :: uu____15540 in
                                               (bind_inst, uu____15536) in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____15521 in
                                           FStar_Syntax_Syntax.mk uu____15520 in
                                         uu____15517
                                           FStar_Pervasives_Native.None rng in
                                       log cfg
                                         (fun uu____15570  ->
                                            let uu____15571 =
                                              FStar_Syntax_Print.term_to_string
                                                reified in
                                            FStar_Util.print1
                                              "Reified to %s\n" uu____15571);
                                       (let uu____15572 = FStar_List.tl stack in
                                        norm cfg env uu____15572 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m in
                     let uu____15596 = ed.FStar_Syntax_Syntax.bind_repr in
                     (match uu____15596 with
                      | (uu____15597,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____15632 =
                                  let uu____15633 =
                                    FStar_Syntax_Subst.compress t1 in
                                  uu____15633.FStar_Syntax_Syntax.n in
                                match uu____15632 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____15639) -> t2
                                | uu____15644 -> head3 in
                              let uu____15645 =
                                let uu____15646 =
                                  FStar_Syntax_Subst.compress t2 in
                                uu____15646.FStar_Syntax_Syntax.n in
                              match uu____15645 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____15652 -> FStar_Pervasives_Native.None in
                            let uu____15653 = maybe_extract_fv head3 in
                            match uu____15653 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____15663 =
                                  FStar_Syntax_Syntax.lid_of_fv x in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____15663
                                ->
                                let head4 = norm cfg env [] head3 in
                                let action_unfolded =
                                  let uu____15668 = maybe_extract_fv head4 in
                                  match uu____15668 with
                                  | FStar_Pervasives_Native.Some uu____15673
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____15674 ->
                                      FStar_Pervasives_Native.Some false in
                                (head4, action_unfolded)
                            | uu____15679 ->
                                (head3, FStar_Pervasives_Native.None) in
                          ((let is_arg_impure uu____15694 =
                              match uu____15694 with
                              | (e,q) ->
                                  let uu____15701 =
                                    let uu____15702 =
                                      FStar_Syntax_Subst.compress e in
                                    uu____15702.FStar_Syntax_Syntax.n in
                                  (match uu____15701 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____15717 -> false) in
                            let uu____15718 =
                              let uu____15719 =
                                let uu____15726 =
                                  FStar_Syntax_Syntax.as_arg head_app in
                                uu____15726 :: args in
                              FStar_Util.for_some is_arg_impure uu____15719 in
                            if uu____15718
                            then
                              let uu____15731 =
                                let uu____15732 =
                                  FStar_Syntax_Print.term_to_string head2 in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____15732 in
                              failwith uu____15731
                            else ());
                           (let uu____15734 = maybe_unfold_action head_app in
                            match uu____15734 with
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
                                let uu____15771 = FStar_List.tl stack in
                                norm cfg env uu____15771 body1)))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____15773) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____15797 = closure_as_term cfg env t' in
                       reify_lift cfg e msrc mtgt uu____15797 in
                     (log cfg
                        (fun uu____15801  ->
                           let uu____15802 =
                             FStar_Syntax_Print.term_to_string lifted in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____15802);
                      (let uu____15803 = FStar_List.tl stack in
                       norm cfg env uu____15803 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____15805) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____15930  ->
                               match uu____15930 with
                               | (pat,wopt,tm) ->
                                   let uu____15978 =
                                     FStar_Syntax_Util.mk_reify tm in
                                   (pat, wopt, uu____15978))) in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos in
                     let uu____16010 = FStar_List.tl stack in
                     norm cfg env uu____16010 tm
                 | uu____16011 -> fallback ())
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
              (fun uu____16025  ->
                 let uu____16026 = FStar_Ident.string_of_lid msrc in
                 let uu____16027 = FStar_Ident.string_of_lid mtgt in
                 let uu____16028 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16026
                   uu____16027 uu____16028);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt in
               let uu____16030 = ed.FStar_Syntax_Syntax.return_repr in
               match uu____16030 with
               | (uu____16031,return_repr) ->
                   let return_inst =
                     let uu____16040 =
                       let uu____16041 =
                         FStar_Syntax_Subst.compress return_repr in
                       uu____16041.FStar_Syntax_Syntax.n in
                     match uu____16040 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16047::[]) ->
                         let uu____16054 =
                           let uu____16057 =
                             let uu____16058 =
                               let uu____16065 =
                                 let uu____16068 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t in
                                 [uu____16068] in
                               (return_tm, uu____16065) in
                             FStar_Syntax_Syntax.Tm_uinst uu____16058 in
                           FStar_Syntax_Syntax.mk uu____16057 in
                         uu____16054 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16076 ->
                         failwith "NIY : Reification of indexed effects" in
                   let uu____16079 =
                     let uu____16082 =
                       let uu____16083 =
                         let uu____16098 =
                           let uu____16101 = FStar_Syntax_Syntax.as_arg t in
                           let uu____16102 =
                             let uu____16105 = FStar_Syntax_Syntax.as_arg e in
                             [uu____16105] in
                           uu____16101 :: uu____16102 in
                         (return_inst, uu____16098) in
                       FStar_Syntax_Syntax.Tm_app uu____16083 in
                     FStar_Syntax_Syntax.mk uu____16082 in
                   uu____16079 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____16114 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt in
               match uu____16114 with
               | FStar_Pervasives_Native.None  ->
                   let uu____16117 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt) in
                   failwith uu____16117
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16118;
                     FStar_TypeChecker_Env.mtarget = uu____16119;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16120;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   failwith
                     "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____16135;
                     FStar_TypeChecker_Env.mtarget = uu____16136;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____16137;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____16161 =
                     env.FStar_TypeChecker_Env.universe_of env t in
                   let uu____16162 = FStar_Syntax_Util.mk_reify e in
                   lift uu____16161 t FStar_Syntax_Syntax.tun uu____16162)
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
                (fun uu____16218  ->
                   match uu____16218 with
                   | (a,imp) ->
                       let uu____16229 = norm cfg env [] a in
                       (uu____16229, imp))))
and norm_comp:
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___135_16243 = comp in
            let uu____16244 =
              let uu____16245 =
                let uu____16254 = norm cfg env [] t in
                let uu____16255 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16254, uu____16255) in
              FStar_Syntax_Syntax.Total uu____16245 in
            {
              FStar_Syntax_Syntax.n = uu____16244;
              FStar_Syntax_Syntax.pos =
                (uu___135_16243.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___135_16243.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___136_16270 = comp in
            let uu____16271 =
              let uu____16272 =
                let uu____16281 = norm cfg env [] t in
                let uu____16282 =
                  FStar_Option.map (norm_universe cfg env) uopt in
                (uu____16281, uu____16282) in
              FStar_Syntax_Syntax.GTotal uu____16272 in
            {
              FStar_Syntax_Syntax.n = uu____16271;
              FStar_Syntax_Syntax.pos =
                (uu___136_16270.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___136_16270.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____16334  ->
                      match uu____16334 with
                      | (a,i) ->
                          let uu____16345 = norm cfg env [] a in
                          (uu____16345, i))) in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___85_16356  ->
                      match uu___85_16356 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____16360 = norm cfg env [] t in
                          FStar_Syntax_Syntax.DECREASES uu____16360
                      | f -> f)) in
            let uu___137_16364 = comp in
            let uu____16365 =
              let uu____16366 =
                let uu___138_16367 = ct in
                let uu____16368 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs in
                let uu____16369 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ in
                let uu____16372 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____16368;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___138_16367.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____16369;
                  FStar_Syntax_Syntax.effect_args = uu____16372;
                  FStar_Syntax_Syntax.flags = flags1
                } in
              FStar_Syntax_Syntax.Comp uu____16366 in
            {
              FStar_Syntax_Syntax.n = uu____16365;
              FStar_Syntax_Syntax.pos =
                (uu___137_16364.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___137_16364.FStar_Syntax_Syntax.vars)
            }
and norm_binder:
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____16383  ->
        match uu____16383 with
        | (x,imp) ->
            let uu____16386 =
              let uu___139_16387 = x in
              let uu____16388 = norm cfg env [] x.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___139_16387.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___139_16387.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16388
              } in
            (uu____16386, imp)
and norm_binders:
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16394 =
          FStar_List.fold_left
            (fun uu____16412  ->
               fun b  ->
                 match uu____16412 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs in
        match uu____16394 with | (nbs,uu____16452) -> FStar_List.rev nbs
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
            let uu____16468 =
              let uu___140_16469 = rc in
              let uu____16470 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_16469.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16470;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___140_16469.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu____16468
        | uu____16477 -> lopt
and rebuild:
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____16490  ->
               let uu____16491 = FStar_Syntax_Print.tag_of_term t in
               let uu____16492 = FStar_Syntax_Print.term_to_string t in
               let uu____16493 =
                 FStar_Util.string_of_int (FStar_List.length env) in
               let uu____16500 =
                 let uu____16501 =
                   let uu____16504 = firstn (Prims.parse_int "4") stack in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____16504 in
                 stack_to_string uu____16501 in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____16491 uu____16492 uu____16493 uu____16500);
          (match stack with
           | [] -> t
           | (Debug (tm,time_then))::stack1 ->
               ((let uu____16533 =
                   FStar_All.pipe_left
                     (FStar_TypeChecker_Env.debug cfg.tcenv)
                     (FStar_Options.Other "print_normalized_terms") in
                 if uu____16533
                 then
                   let time_now = FStar_Util.now () in
                   let uu____16535 =
                     let uu____16536 =
                       let uu____16537 =
                         FStar_Util.time_diff time_then time_now in
                       FStar_Pervasives_Native.snd uu____16537 in
                     FStar_Util.string_of_int uu____16536 in
                   let uu____16542 = FStar_Syntax_Print.term_to_string tm in
                   let uu____16543 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____16535 uu____16542 uu____16543
                 else ());
                rebuild cfg env stack1 t)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t
           | (Meta (m,r))::stack1 ->
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m)) r in
               rebuild cfg env stack1 t1
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t);
                log cfg
                  (fun uu____16597  ->
                     let uu____16598 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1 "\tSet memo %s\n" uu____16598);
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
               let uu____16634 =
                 let uu___141_16635 = FStar_Syntax_Util.abs bs1 t lopt1 in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___141_16635.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___141_16635.FStar_Syntax_Syntax.vars)
                 } in
               rebuild cfg env stack1 uu____16634
           | (Arg (Univ uu____16636,uu____16637,uu____16638))::uu____16639 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____16642,uu____16643))::uu____16644 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t1 = FStar_Syntax_Syntax.mk_Tm_uinst t us in
               rebuild cfg env stack1 t1
           | (Arg (Clos (env_arg,tm,m,uu____16660),aq,r))::stack1 ->
               (log cfg
                  (fun uu____16713  ->
                     let uu____16714 = FStar_Syntax_Print.term_to_string tm in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____16714);
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
                  (let uu____16724 = FStar_ST.op_Bang m in
                   match uu____16724 with
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
                   | FStar_Pervasives_Native.Some (uu____16861,a) ->
                       let t1 =
                         FStar_Syntax_Syntax.extend_app t (a, aq)
                           FStar_Pervasives_Native.None r in
                       rebuild cfg env_arg stack1 t1))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t in
               let fallback msg uu____16908 =
                 log cfg
                   (fun uu____16912  ->
                      let uu____16913 = FStar_Syntax_Print.term_to_string t in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____16913);
                 (let t1 =
                    FStar_Syntax_Syntax.extend_app head1 (t, aq)
                      FStar_Pervasives_Native.None r in
                  rebuild cfg env1 stack' t1) in
               let uu____16917 =
                 let uu____16918 = FStar_Syntax_Subst.compress t in
                 uu____16918.FStar_Syntax_Syntax.n in
               (match uu____16917 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t1 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t1,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____16945 = closure_as_term cfg env1 ty in
                      reify_lift cfg t1 msrc mtgt uu____16945 in
                    (log cfg
                       (fun uu____16949  ->
                          let uu____16950 =
                            FStar_Syntax_Print.term_to_string lifted in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____16950);
                     (let uu____16951 = FStar_List.tl stack in
                      norm cfg env1 uu____16951 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____16952);
                       FStar_Syntax_Syntax.pos = uu____16953;
                       FStar_Syntax_Syntax.vars = uu____16954;_},(e,uu____16956)::[])
                    -> norm cfg env1 stack' e
                | uu____16985 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r in
               let uu____16996 = maybe_simplify cfg env1 stack1 t1 in
               rebuild cfg env1 stack1 uu____16996
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____17008  ->
                     let uu____17009 = FStar_Syntax_Print.term_to_string t in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____17009);
                (let scrutinee = t in
                 let norm_and_rebuild_match uu____17014 =
                   log cfg
                     (fun uu____17019  ->
                        let uu____17020 =
                          FStar_Syntax_Print.term_to_string scrutinee in
                        let uu____17021 =
                          let uu____17022 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____17039  ->
                                    match uu____17039 with
                                    | (p,uu____17049,uu____17050) ->
                                        FStar_Syntax_Print.pat_to_string p)) in
                          FStar_All.pipe_right uu____17022
                            (FStar_String.concat "\n\t") in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____17020 uu____17021);
                   (let whnf =
                      (FStar_List.contains Weak cfg.steps) ||
                        (FStar_List.contains HNF cfg.steps) in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___86_17067  ->
                                match uu___86_17067 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____17068 -> false)) in
                      let steps' = [Exclude Zeta] in
                      let uu___142_17072 = cfg in
                      {
                        steps = (FStar_List.append steps' cfg.steps);
                        tcenv = (uu___142_17072.tcenv);
                        delta_level = new_delta;
                        primitive_steps = (uu___142_17072.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___142_17072.memoize_lazy)
                      } in
                    let norm_or_whnf env2 t1 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t1
                      else norm cfg_exclude_iota_zeta env2 [] t1 in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____17104 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____17125 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____17185  ->
                                    fun uu____17186  ->
                                      match (uu____17185, uu____17186) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____17277 = norm_pat env3 p1 in
                                          (match uu____17277 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2)) in
                          (match uu____17125 with
                           | (pats1,env3) ->
                               ((let uu___143_17359 = p in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___143_17359.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___144_17378 = x in
                            let uu____17379 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___144_17378.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___144_17378.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17379
                            } in
                          ((let uu___145_17393 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___145_17393.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___146_17404 = x in
                            let uu____17405 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_17404.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_17404.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17405
                            } in
                          ((let uu___147_17419 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___147_17419.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                          let x1 =
                            let uu___148_17435 = x in
                            let uu____17436 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_17435.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_17435.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____17436
                            } in
                          let t2 = norm_or_whnf env2 t1 in
                          ((let uu___149_17443 = p in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                              FStar_Syntax_Syntax.p =
                                (uu___149_17443.FStar_Syntax_Syntax.p)
                            }), env2) in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____17453 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____17467 =
                                    FStar_Syntax_Subst.open_branch branch1 in
                                  match uu____17467 with
                                  | (p,wopt,e) ->
                                      let uu____17487 = norm_pat env1 p in
                                      (match uu____17487 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____17512 =
                                                   norm_or_whnf env2 w in
                                                 FStar_Pervasives_Native.Some
                                                   uu____17512 in
                                           let e1 = norm_or_whnf env2 e in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1)))) in
                    let uu____17518 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r in
                    rebuild cfg env1 stack1 uu____17518) in
                 let rec is_cons head1 =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____17528) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____17533 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17534;
                         FStar_Syntax_Syntax.fv_delta = uu____17535;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____17536;
                         FStar_Syntax_Syntax.fv_delta = uu____17537;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____17538);_}
                       -> true
                   | uu____17545 -> false in
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
                   let uu____17690 =
                     FStar_Syntax_Util.head_and_args scrutinee1 in
                   match uu____17690 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____17777 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____17816 ->
                                 let uu____17817 =
                                   let uu____17818 = is_cons head1 in
                                   Prims.op_Negation uu____17818 in
                                 FStar_Util.Inr uu____17817)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____17843 =
                              let uu____17844 =
                                FStar_Syntax_Util.un_uinst head1 in
                              uu____17844.FStar_Syntax_Syntax.n in
                            (match uu____17843 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____17862 ->
                                 let uu____17863 =
                                   let uu____17864 = is_cons head1 in
                                   Prims.op_Negation uu____17864 in
                                 FStar_Util.Inr uu____17863))
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t1,uu____17933)::rest_a,(p1,uu____17936)::rest_p) ->
                       let uu____17980 = matches_pat t1 p1 in
                       (match uu____17980 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____18029 -> FStar_Util.Inr false in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____18135 = matches_pat scrutinee1 p1 in
                       (match uu____18135 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____18175  ->
                                  let uu____18176 =
                                    FStar_Syntax_Print.pat_to_string p1 in
                                  let uu____18177 =
                                    let uu____18178 =
                                      FStar_List.map
                                        (fun uu____18188  ->
                                           match uu____18188 with
                                           | (uu____18193,t1) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t1) s in
                                    FStar_All.pipe_right uu____18178
                                      (FStar_String.concat "; ") in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____18176 uu____18177);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____18224  ->
                                       match uu____18224 with
                                       | (bv,t1) ->
                                           let uu____18247 =
                                             let uu____18254 =
                                               let uu____18257 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv in
                                               FStar_Pervasives_Native.Some
                                                 uu____18257 in
                                             let uu____18258 =
                                               let uu____18259 =
                                                 let uu____18290 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t1)) in
                                                 ([], t1, uu____18290, false) in
                                               Clos uu____18259 in
                                             (uu____18254, uu____18258) in
                                           uu____18247 :: env2) env1 s in
                              let uu____18407 = guard_when_clause wopt b rest in
                              norm cfg env2 stack1 uu____18407))) in
                 let uu____18408 =
                   FStar_All.pipe_right cfg.steps
                     (FStar_List.contains (Exclude Iota)) in
                 if uu____18408
                 then norm_and_rebuild_match ()
                 else matches scrutinee branches)))
let config: step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  ->
    fun e  ->
      let d =
        FStar_All.pipe_right s
          (FStar_List.collect
             (fun uu___87_18429  ->
                match uu___87_18429 with
                | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                | Eager_unfolding  ->
                    [FStar_TypeChecker_Env.Eager_unfolding_only]
                | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                | uu____18433 -> [])) in
      let d1 =
        match d with
        | [] -> [FStar_TypeChecker_Env.NoDelta]
        | uu____18439 -> d in
      {
        steps = s;
        tcenv = e;
        delta_level = d1;
        primitive_steps = built_in_primitive_steps;
        strong = false;
        memoize_lazy = true
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
            let uu___150_18464 = config s e in
            {
              steps = (uu___150_18464.steps);
              tcenv = (uu___150_18464.tcenv);
              delta_level = (uu___150_18464.delta_level);
              primitive_steps = (FStar_List.append c.primitive_steps ps);
              strong = (uu___150_18464.strong);
              memoize_lazy = (uu___150_18464.memoize_lazy)
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
      fun t  -> let uu____18489 = config s e in norm_comp uu____18489 [] t
let normalize_universe:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____18502 = config [] env in norm_universe uu____18502 [] u
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
        let uu____18520 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18520 in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____18527 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___151_18546 = c in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___151_18546.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___151_18546.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name in
          let uu____18553 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ) in
          if uu____18553
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
                  let uu___152_18562 = ct in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___152_18562.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___152_18562.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___152_18562.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c in
                  let uu___153_18564 = ct1 in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___153_18564.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___153_18564.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___153_18564.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___153_18564.FStar_Syntax_Syntax.flags)
                  } in
            let uu___154_18565 = c in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___154_18565.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___154_18565.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____18567 -> c
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
        let uu____18579 = norm cfg [] [] t in
        FStar_Syntax_Util.non_informative uu____18579 in
      let uu____18586 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ) in
      if uu____18586
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____18590  ->
                 let uu____18591 = FStar_Syntax_Syntax.lcomp_comp lc in
                 ghost_to_pure env uu____18591)
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
            ((let uu____18608 =
                let uu____18613 =
                  let uu____18614 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18614 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18613) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____18608);
             t) in
      FStar_Syntax_Print.term_to_string t1
let comp_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____18625 = config [AllowUnboundUniverses] env in
          norm_comp uu____18625 [] c
        with
        | e ->
            ((let uu____18638 =
                let uu____18643 =
                  let uu____18644 = FStar_Util.message_of_exn e in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____18644 in
                (FStar_Errors.Warning_NormalizationFailure, uu____18643) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____18638);
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
                   let uu____18681 =
                     let uu____18682 =
                       let uu____18689 = FStar_Syntax_Util.mk_conj phi1 phi in
                       (y, uu____18689) in
                     FStar_Syntax_Syntax.Tm_refine uu____18682 in
                   mk uu____18681 t01.FStar_Syntax_Syntax.pos
               | uu____18694 -> t2)
          | uu____18695 -> t2 in
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
        let uu____18735 = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu____18735 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____18764 ->
                 let uu____18771 = FStar_Syntax_Util.abs_formals e in
                 (match uu____18771 with
                  | (actuals,uu____18781,uu____18782) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____18796 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu____18796 with
                         | (binders,args) ->
                             let uu____18813 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu____18813
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
      | uu____18821 ->
          let uu____18822 = FStar_Syntax_Util.head_and_args t in
          (match uu____18822 with
           | (head1,args) ->
               let uu____18859 =
                 let uu____18860 = FStar_Syntax_Subst.compress head1 in
                 uu____18860.FStar_Syntax_Syntax.n in
               (match uu____18859 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____18863,thead) ->
                    let uu____18889 = FStar_Syntax_Util.arrow_formals thead in
                    (match uu____18889 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____18931 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___159_18939 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___159_18939.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___159_18939.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___159_18939.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___159_18939.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___159_18939.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___159_18939.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___159_18939.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___159_18939.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___159_18939.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___159_18939.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___159_18939.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___159_18939.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___159_18939.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___159_18939.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___159_18939.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___159_18939.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___159_18939.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___159_18939.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___159_18939.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___159_18939.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___159_18939.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___159_18939.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___159_18939.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___159_18939.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___159_18939.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___159_18939.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___159_18939.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___159_18939.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___159_18939.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___159_18939.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___159_18939.FStar_TypeChecker_Env.dep_graph)
                                 }) t in
                            match uu____18931 with
                            | (uu____18940,ty,uu____18942) ->
                                eta_expand_with_type env t ty))
                | uu____18943 ->
                    let uu____18944 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___160_18952 = env in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___160_18952.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___160_18952.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___160_18952.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___160_18952.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___160_18952.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___160_18952.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___160_18952.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___160_18952.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___160_18952.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___160_18952.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___160_18952.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___160_18952.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___160_18952.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___160_18952.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___160_18952.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___160_18952.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___160_18952.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___160_18952.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___160_18952.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___160_18952.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___160_18952.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___160_18952.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___160_18952.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___160_18952.FStar_TypeChecker_Env.qname_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___160_18952.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___160_18952.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___160_18952.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___160_18952.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___160_18952.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___160_18952.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___160_18952.FStar_TypeChecker_Env.dep_graph)
                         }) t in
                    (match uu____18944 with
                     | (uu____18953,ty,uu____18955) ->
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
            | (uu____19029,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____19035,FStar_Util.Inl t) ->
                let uu____19041 =
                  let uu____19044 =
                    let uu____19045 =
                      let uu____19058 = FStar_Syntax_Syntax.mk_Total t in
                      (binders, uu____19058) in
                    FStar_Syntax_Syntax.Tm_arrow uu____19045 in
                  FStar_Syntax_Syntax.mk uu____19044 in
                uu____19041 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos in
          let uu____19062 = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu____19062 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu____19089 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t3))
                | uu____19144 ->
                    let uu____19145 =
                      let uu____19154 =
                        let uu____19155 = FStar_Syntax_Subst.compress t3 in
                        uu____19155.FStar_Syntax_Syntax.n in
                      (uu____19154, tc) in
                    (match uu____19145 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____19180) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____19217) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____19256,FStar_Util.Inl uu____19257) ->
                         ([], (FStar_Util.Inl t3))
                     | uu____19280 -> failwith "Impossible") in
              (match uu____19089 with
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
          let uu____19385 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t) in
          match uu____19385 with
          | (univ_names1,binders1,tc) ->
              let uu____19443 = FStar_Util.left tc in
              (univ_names1, binders1, uu____19443)
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
          let uu____19478 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c) in
          match uu____19478 with
          | (univ_names1,binders1,tc) ->
              let uu____19538 = FStar_Util.right tc in
              (univ_names1, binders1, uu____19538)
let rec elim_uvars:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____19571 = elim_uvars_aux_t env univ_names binders typ in
          (match uu____19571 with
           | (univ_names1,binders1,typ1) ->
               let uu___161_19599 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___161_19599.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___161_19599.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___161_19599.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___161_19599.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___162_19620 = s in
          let uu____19621 =
            let uu____19622 =
              let uu____19631 = FStar_List.map (elim_uvars env) sigs in
              (uu____19631, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu____19622 in
          {
            FStar_Syntax_Syntax.sigel = uu____19621;
            FStar_Syntax_Syntax.sigrng =
              (uu___162_19620.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___162_19620.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___162_19620.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___162_19620.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____19648 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19648 with
           | (univ_names1,uu____19666,typ1) ->
               let uu___163_19680 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___163_19680.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___163_19680.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___163_19680.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___163_19680.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____19686 = elim_uvars_aux_t env univ_names [] typ in
          (match uu____19686 with
           | (univ_names1,uu____19704,typ1) ->
               let uu___164_19718 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___164_19718.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___164_19718.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___164_19718.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___164_19718.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____19752 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu____19752 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____19775 =
                            let uu____19776 =
                              FStar_Syntax_Subst.subst opening t in
                            remove_uvar_solutions env uu____19776 in
                          FStar_Syntax_Subst.close_univ_vars lbunivs
                            uu____19775 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___165_19779 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___165_19779.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___165_19779.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef
                        })) in
          let uu___166_19780 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___166_19780.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___166_19780.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___166_19780.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___166_19780.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___167_19792 = s in
          let uu____19793 =
            let uu____19794 = remove_uvar_solutions env t in
            FStar_Syntax_Syntax.Sig_main uu____19794 in
          {
            FStar_Syntax_Syntax.sigel = uu____19793;
            FStar_Syntax_Syntax.sigrng =
              (uu___167_19792.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___167_19792.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___167_19792.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___167_19792.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____19798 = elim_uvars_aux_t env us [] t in
          (match uu____19798 with
           | (us1,uu____19816,t1) ->
               let uu___168_19830 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___168_19830.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___168_19830.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___168_19830.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___168_19830.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19831 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____19833 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature in
          (match uu____19833 with
           | (univs1,binders,signature) ->
               let uu____19861 =
                 let uu____19870 = FStar_Syntax_Subst.univ_var_opening univs1 in
                 match uu____19870 with
                 | (univs_opening,univs2) ->
                     let uu____19897 =
                       FStar_Syntax_Subst.univ_var_closing univs2 in
                     (univs_opening, uu____19897) in
               (match uu____19861 with
                | (univs_opening,univs_closing) ->
                    let uu____19914 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu____19920 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu____19921 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu____19920, uu____19921) in
                    (match uu____19914 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1 in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu____19943 =
                           match uu____19943 with
                           | (us,t) ->
                               let n_us = FStar_List.length us in
                               let uu____19961 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu____19961 with
                                | (us1,t1) ->
                                    let uu____19972 =
                                      let uu____19977 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu____19984 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu____19977, uu____19984) in
                                    (match uu____19972 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____19997 =
                                           let uu____20002 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           let uu____20011 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us) in
                                           (uu____20002, uu____20011) in
                                         (match uu____19997 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____20027 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____20027 in
                                              let uu____20028 =
                                                elim_uvars_aux_t env [] [] t2 in
                                              (match uu____20028 with
                                               | (uu____20049,uu____20050,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____20065 =
                                                       let uu____20066 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____20066 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____20065 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu____20071 =
                             elim_uvars_aux_t env univs1 binders t in
                           match uu____20071 with
                           | (uu____20084,uu____20085,t1) -> t1 in
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
                             | uu____20145 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu____20162 =
                               let uu____20163 =
                                 FStar_Syntax_Subst.compress body in
                               uu____20163.FStar_Syntax_Syntax.n in
                             match uu____20162 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____20222 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu____20251 =
                               let uu____20252 =
                                 FStar_Syntax_Subst.compress t in
                               uu____20252.FStar_Syntax_Syntax.n in
                             match uu____20251 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____20273) ->
                                 let uu____20294 = destruct_action_body body in
                                 (match uu____20294 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____20339 ->
                                 let uu____20340 = destruct_action_body t in
                                 (match uu____20340 with
                                  | (defn,typ) -> ([], defn, typ)) in
                           let uu____20389 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu____20389 with
                           | (action_univs,t) ->
                               let uu____20398 = destruct_action_typ_templ t in
                               (match uu____20398 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___169_20439 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___169_20439.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___169_20439.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___170_20441 = ed in
                           let uu____20442 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____20443 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____20444 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____20445 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____20446 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger in
                           let uu____20447 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp in
                           let uu____20448 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p in
                           let uu____20449 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p in
                           let uu____20450 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp in
                           let uu____20451 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial in
                           let uu____20452 =
                             elim_term ed.FStar_Syntax_Syntax.repr in
                           let uu____20453 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr in
                           let uu____20454 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____20455 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___170_20441.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___170_20441.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____20442;
                             FStar_Syntax_Syntax.bind_wp = uu____20443;
                             FStar_Syntax_Syntax.if_then_else = uu____20444;
                             FStar_Syntax_Syntax.ite_wp = uu____20445;
                             FStar_Syntax_Syntax.stronger = uu____20446;
                             FStar_Syntax_Syntax.close_wp = uu____20447;
                             FStar_Syntax_Syntax.assert_p = uu____20448;
                             FStar_Syntax_Syntax.assume_p = uu____20449;
                             FStar_Syntax_Syntax.null_wp = uu____20450;
                             FStar_Syntax_Syntax.trivial = uu____20451;
                             FStar_Syntax_Syntax.repr = uu____20452;
                             FStar_Syntax_Syntax.return_repr = uu____20453;
                             FStar_Syntax_Syntax.bind_repr = uu____20454;
                             FStar_Syntax_Syntax.actions = uu____20455
                           } in
                         let uu___171_20458 = s in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___171_20458.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___171_20458.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___171_20458.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___171_20458.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___88_20475 =
            match uu___88_20475 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____20502 = elim_uvars_aux_t env us [] t in
                (match uu____20502 with
                 | (us1,uu____20526,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___172_20545 = sub_eff in
            let uu____20546 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu____20549 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source =
                (uu___172_20545.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___172_20545.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____20546;
              FStar_Syntax_Syntax.lift = uu____20549
            } in
          let uu___173_20552 = s in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___173_20552.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___173_20552.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___173_20552.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___173_20552.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____20562 = elim_uvars_aux_c env univ_names binders comp in
          (match uu____20562 with
           | (univ_names1,binders1,comp1) ->
               let uu___174_20596 = s in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___174_20596.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___174_20596.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___174_20596.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___174_20596.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____20607 -> s
let erase_universes:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t