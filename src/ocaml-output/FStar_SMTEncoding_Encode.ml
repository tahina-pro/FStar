open Prims
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,Prims.int,FStar_SMTEncoding_Term.decl
                                                 Prims.list)
          FStar_Pervasives_Native.tuple3
    ;
  is: FStar_Ident.lident -> Prims.bool }
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,Prims.int,FStar_SMTEncoding_Term.decl
                                                 Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
  
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
  
let (prims : prims_t) =
  let uu____119 =
    FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____119 with
  | (asym,a) ->
      let uu____126 =
        FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort
         in
      (match uu____126 with
       | (xsym,x) ->
           let uu____133 =
             FStar_SMTEncoding_Env.fresh_fvar "y"
               FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____133 with
            | (ysym,y) ->
                let quant vars body rng x1 =
                  let xname_decl =
                    let uu____194 =
                      let uu____205 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____205, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____194  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____227 =
                      let uu____234 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____234)  in
                    FStar_SMTEncoding_Util.mkApp uu____227  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app =
                    FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars  in
                  let uu____247 =
                    let uu____250 =
                      let uu____253 =
                        let uu____256 =
                          let uu____257 =
                            let uu____264 =
                              let uu____265 =
                                let uu____276 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____276)  in
                              FStar_SMTEncoding_Term.mkForall rng uu____265
                               in
                            (uu____264, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____257  in
                        let uu____285 =
                          let uu____288 =
                            let uu____289 =
                              let uu____296 =
                                let uu____297 =
                                  let uu____308 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____308)  in
                                FStar_SMTEncoding_Term.mkForall rng uu____297
                                 in
                              (uu____296,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____289  in
                          [uu____288]  in
                        uu____256 :: uu____285  in
                      xtok_decl :: uu____253  in
                    xname_decl :: uu____250  in
                  (xtok1, (FStar_List.length vars), uu____247)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____401 =
                    let uu____420 =
                      let uu____437 =
                        let uu____438 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____438
                         in
                      quant axy uu____437  in
                    (FStar_Parser_Const.op_Eq, uu____420)  in
                  let uu____453 =
                    let uu____474 =
                      let uu____493 =
                        let uu____510 =
                          let uu____511 =
                            let uu____512 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____512  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____511
                           in
                        quant axy uu____510  in
                      (FStar_Parser_Const.op_notEq, uu____493)  in
                    let uu____527 =
                      let uu____548 =
                        let uu____567 =
                          let uu____584 =
                            let uu____585 =
                              let uu____586 =
                                let uu____591 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____592 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____591, uu____592)  in
                              FStar_SMTEncoding_Util.mkLT uu____586  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____585
                             in
                          quant xy uu____584  in
                        (FStar_Parser_Const.op_LT, uu____567)  in
                      let uu____607 =
                        let uu____628 =
                          let uu____647 =
                            let uu____664 =
                              let uu____665 =
                                let uu____666 =
                                  let uu____671 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____672 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____671, uu____672)  in
                                FStar_SMTEncoding_Util.mkLTE uu____666  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____665
                               in
                            quant xy uu____664  in
                          (FStar_Parser_Const.op_LTE, uu____647)  in
                        let uu____687 =
                          let uu____708 =
                            let uu____727 =
                              let uu____744 =
                                let uu____745 =
                                  let uu____746 =
                                    let uu____751 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____752 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____751, uu____752)  in
                                  FStar_SMTEncoding_Util.mkGT uu____746  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____745
                                 in
                              quant xy uu____744  in
                            (FStar_Parser_Const.op_GT, uu____727)  in
                          let uu____767 =
                            let uu____788 =
                              let uu____807 =
                                let uu____824 =
                                  let uu____825 =
                                    let uu____826 =
                                      let uu____831 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____832 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____831, uu____832)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____826
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____825
                                   in
                                quant xy uu____824  in
                              (FStar_Parser_Const.op_GTE, uu____807)  in
                            let uu____847 =
                              let uu____868 =
                                let uu____887 =
                                  let uu____904 =
                                    let uu____905 =
                                      let uu____906 =
                                        let uu____911 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____912 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____911, uu____912)  in
                                      FStar_SMTEncoding_Util.mkSub uu____906
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt uu____905
                                     in
                                  quant xy uu____904  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____887)
                                 in
                              let uu____927 =
                                let uu____948 =
                                  let uu____967 =
                                    let uu____984 =
                                      let uu____985 =
                                        let uu____986 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____986
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____985
                                       in
                                    quant qx uu____984  in
                                  (FStar_Parser_Const.op_Minus, uu____967)
                                   in
                                let uu____1001 =
                                  let uu____1022 =
                                    let uu____1041 =
                                      let uu____1058 =
                                        let uu____1059 =
                                          let uu____1060 =
                                            let uu____1065 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____1066 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____1065, uu____1066)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____1060
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____1059
                                         in
                                      quant xy uu____1058  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____1041)
                                     in
                                  let uu____1081 =
                                    let uu____1102 =
                                      let uu____1121 =
                                        let uu____1138 =
                                          let uu____1139 =
                                            let uu____1140 =
                                              let uu____1145 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____1146 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____1145, uu____1146)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____1140
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____1139
                                           in
                                        quant xy uu____1138  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____1121)
                                       in
                                    let uu____1161 =
                                      let uu____1182 =
                                        let uu____1201 =
                                          let uu____1218 =
                                            let uu____1219 =
                                              let uu____1220 =
                                                let uu____1225 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____1226 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____1225, uu____1226)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____1220
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____1219
                                             in
                                          quant xy uu____1218  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____1201)
                                         in
                                      let uu____1241 =
                                        let uu____1262 =
                                          let uu____1281 =
                                            let uu____1298 =
                                              let uu____1299 =
                                                let uu____1300 =
                                                  let uu____1305 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____1306 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____1305, uu____1306)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____1300
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____1299
                                               in
                                            quant xy uu____1298  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____1281)
                                           in
                                        let uu____1321 =
                                          let uu____1342 =
                                            let uu____1361 =
                                              let uu____1378 =
                                                let uu____1379 =
                                                  let uu____1380 =
                                                    let uu____1385 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____1386 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____1385, uu____1386)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____1380
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____1379
                                                 in
                                              quant xy uu____1378  in
                                            (FStar_Parser_Const.op_And,
                                              uu____1361)
                                             in
                                          let uu____1401 =
                                            let uu____1422 =
                                              let uu____1441 =
                                                let uu____1458 =
                                                  let uu____1459 =
                                                    let uu____1460 =
                                                      let uu____1465 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____1466 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____1465,
                                                        uu____1466)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____1460
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____1459
                                                   in
                                                quant xy uu____1458  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____1441)
                                               in
                                            let uu____1481 =
                                              let uu____1502 =
                                                let uu____1521 =
                                                  let uu____1538 =
                                                    let uu____1539 =
                                                      let uu____1540 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____1540
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____1539
                                                     in
                                                  quant qx uu____1538  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____1521)
                                                 in
                                              [uu____1502]  in
                                            uu____1422 :: uu____1481  in
                                          uu____1342 :: uu____1401  in
                                        uu____1262 :: uu____1321  in
                                      uu____1182 :: uu____1241  in
                                    uu____1102 :: uu____1161  in
                                  uu____1022 :: uu____1081  in
                                uu____948 :: uu____1001  in
                              uu____868 :: uu____927  in
                            uu____788 :: uu____847  in
                          uu____708 :: uu____767  in
                        uu____628 :: uu____687  in
                      uu____548 :: uu____607  in
                    uu____474 :: uu____527  in
                  uu____401 :: uu____453  in
                let mk1 l v1 =
                  let uu____1862 =
                    let uu____1873 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____1955  ->
                              match uu____1955 with
                              | (l',uu____1973) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____1873
                      (FStar_Option.map
                         (fun uu____2062  ->
                            match uu____2062 with
                            | (uu____2087,b) ->
                                let uu____2117 = FStar_Ident.range_of_lid l
                                   in
                                b uu____2117 v1))
                     in
                  FStar_All.pipe_right uu____1862 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____2191  ->
                          match uu____2191 with
                          | (l',uu____2209) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let (pretype_axiom :
  FStar_Range.range ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_SMTEncoding_Term.term ->
        (Prims.string,FStar_SMTEncoding_Term.sort)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_SMTEncoding_Term.decl)
  =
  fun rng  ->
    fun env  ->
      fun tapp  ->
        fun vars  ->
          let uu____2270 =
            FStar_SMTEncoding_Env.fresh_fvar "x"
              FStar_SMTEncoding_Term.Term_sort
             in
          match uu____2270 with
          | (xxsym,xx) ->
              let uu____2277 =
                FStar_SMTEncoding_Env.fresh_fvar "f"
                  FStar_SMTEncoding_Term.Fuel_sort
                 in
              (match uu____2277 with
               | (ffsym,ff) ->
                   let xx_has_type =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                   let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp
                      in
                   let module_name =
                     env.FStar_SMTEncoding_Env.current_module_name  in
                   let uu____2287 =
                     let uu____2294 =
                       let uu____2295 =
                         let uu____2306 =
                           let uu____2307 =
                             let uu____2312 =
                               let uu____2313 =
                                 let uu____2318 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, uu____2318)  in
                               FStar_SMTEncoding_Util.mkEq uu____2313  in
                             (xx_has_type, uu____2312)  in
                           FStar_SMTEncoding_Util.mkImp uu____2307  in
                         ([[xx_has_type]],
                           ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                           (ffsym, FStar_SMTEncoding_Term.Fuel_sort) ::
                           vars), uu____2306)
                          in
                       FStar_SMTEncoding_Term.mkForall rng uu____2295  in
                     let uu____2337 =
                       let uu____2338 =
                         let uu____2339 =
                           let uu____2340 =
                             FStar_Util.digest_of_string tapp_hash  in
                           Prims.strcat "_pretyping_" uu____2340  in
                         Prims.strcat module_name uu____2339  in
                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                         uu____2338
                        in
                     (uu____2294, (FStar_Pervasives_Native.Some "pretyping"),
                       uu____2337)
                      in
                   FStar_SMTEncoding_Util.mkAssume uu____2287)
  
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____2388 =
      let uu____2389 =
        let uu____2396 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____2396, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2389  in
    let uu____2397 =
      let uu____2400 =
        let uu____2401 =
          let uu____2408 =
            let uu____2409 =
              let uu____2420 =
                let uu____2421 =
                  let uu____2426 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____2426)  in
                FStar_SMTEncoding_Util.mkImp uu____2421  in
              ([[typing_pred]], [xx], uu____2420)  in
            let uu____2443 =
              let uu____2458 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2458  in
            uu____2443 uu____2409  in
          (uu____2408, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2401  in
      [uu____2400]  in
    uu____2388 :: uu____2397  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2482 =
      let uu____2483 =
        let uu____2490 =
          let uu____2491 = FStar_TypeChecker_Env.get_range env  in
          let uu____2492 =
            let uu____2503 =
              let uu____2508 =
                let uu____2511 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____2511]  in
              [uu____2508]  in
            let uu____2516 =
              let uu____2517 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2517 tt  in
            (uu____2503, [bb], uu____2516)  in
          FStar_SMTEncoding_Term.mkForall uu____2491 uu____2492  in
        (uu____2490, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2483  in
    let uu____2530 =
      let uu____2533 =
        let uu____2534 =
          let uu____2541 =
            let uu____2542 =
              let uu____2553 =
                let uu____2554 =
                  let uu____2559 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____2559)  in
                FStar_SMTEncoding_Util.mkImp uu____2554  in
              ([[typing_pred]], [xx], uu____2553)  in
            let uu____2576 =
              let uu____2591 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2591  in
            uu____2576 uu____2542  in
          (uu____2541, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2534  in
      [uu____2533]  in
    uu____2482 :: uu____2530  in
  let mk_int env nm tt =
    let lex_t1 =
      let uu____2609 =
        let uu____2614 = FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid
           in
        (uu____2614, FStar_SMTEncoding_Term.Term_sort)  in
      FStar_SMTEncoding_Util.mkFreeV uu____2609  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes_y_x =
      let uu____2630 =
        FStar_SMTEncoding_Util.mkApp
          ("Prims.precedes", [lex_t1; lex_t1; y; x])
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2630  in
    let uu____2633 =
      let uu____2634 =
        let uu____2641 =
          let uu____2642 = FStar_TypeChecker_Env.get_range env  in
          let uu____2643 =
            let uu____2654 =
              let uu____2659 =
                let uu____2662 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____2662]  in
              [uu____2659]  in
            let uu____2667 =
              let uu____2668 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2668 tt  in
            (uu____2654, [bb], uu____2667)  in
          FStar_SMTEncoding_Term.mkForall uu____2642 uu____2643  in
        (uu____2641, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2634  in
    let uu____2681 =
      let uu____2684 =
        let uu____2685 =
          let uu____2692 =
            let uu____2693 =
              let uu____2704 =
                let uu____2705 =
                  let uu____2710 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____2710)  in
                FStar_SMTEncoding_Util.mkImp uu____2705  in
              ([[typing_pred]], [xx], uu____2704)  in
            let uu____2727 =
              let uu____2742 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2742  in
            uu____2727 uu____2693  in
          (uu____2692, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2685  in
      let uu____2743 =
        let uu____2746 =
          let uu____2747 =
            let uu____2754 =
              let uu____2755 =
                let uu____2766 =
                  let uu____2767 =
                    let uu____2772 =
                      let uu____2773 =
                        let uu____2776 =
                          let uu____2779 =
                            let uu____2782 =
                              let uu____2783 =
                                let uu____2788 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____2789 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____2788, uu____2789)  in
                              FStar_SMTEncoding_Util.mkGT uu____2783  in
                            let uu____2790 =
                              let uu____2793 =
                                let uu____2794 =
                                  let uu____2799 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____2800 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____2799, uu____2800)  in
                                FStar_SMTEncoding_Util.mkGTE uu____2794  in
                              let uu____2801 =
                                let uu____2804 =
                                  let uu____2805 =
                                    let uu____2810 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____2811 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____2810, uu____2811)  in
                                  FStar_SMTEncoding_Util.mkLT uu____2805  in
                                [uu____2804]  in
                              uu____2793 :: uu____2801  in
                            uu____2782 :: uu____2790  in
                          typing_pred_y :: uu____2779  in
                        typing_pred :: uu____2776  in
                      FStar_SMTEncoding_Util.mk_and_l uu____2773  in
                    (uu____2772, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____2767  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____2766)
                 in
              let uu____2832 =
                let uu____2847 = FStar_TypeChecker_Env.get_range env  in
                FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2847  in
              uu____2832 uu____2755  in
            (uu____2754,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____2747  in
        [uu____2746]  in
      uu____2684 :: uu____2743  in
    uu____2633 :: uu____2681  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____2871 =
      let uu____2872 =
        let uu____2879 =
          let uu____2880 = FStar_TypeChecker_Env.get_range env  in
          let uu____2881 =
            let uu____2892 =
              let uu____2897 =
                let uu____2900 = FStar_SMTEncoding_Term.boxString b  in
                [uu____2900]  in
              [uu____2897]  in
            let uu____2905 =
              let uu____2906 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____2906 tt  in
            (uu____2892, [bb], uu____2905)  in
          FStar_SMTEncoding_Term.mkForall uu____2880 uu____2881  in
        (uu____2879, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____2872  in
    let uu____2919 =
      let uu____2922 =
        let uu____2923 =
          let uu____2930 =
            let uu____2931 =
              let uu____2942 =
                let uu____2943 =
                  let uu____2948 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____2948)  in
                FStar_SMTEncoding_Util.mkImp uu____2943  in
              ([[typing_pred]], [xx], uu____2942)  in
            let uu____2965 =
              let uu____2980 = FStar_TypeChecker_Env.get_range env  in
              FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2980  in
            uu____2965 uu____2931  in
          (uu____2930, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____2923  in
      [uu____2922]  in
    uu____2871 :: uu____2919  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____3019 =
      let uu____3020 =
        let uu____3027 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____3027, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3020  in
    [uu____3019]  in
  let mk_and_interp env conj uu____3043 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3068 =
      let uu____3069 =
        let uu____3076 =
          let uu____3077 = FStar_TypeChecker_Env.get_range env  in
          let uu____3078 =
            let uu____3089 =
              let uu____3090 =
                let uu____3095 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____3095, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3090  in
            ([[l_and_a_b]], [aa; bb], uu____3089)  in
          FStar_SMTEncoding_Term.mkForall uu____3077 uu____3078  in
        (uu____3076, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3069  in
    [uu____3068]  in
  let mk_or_interp env disj uu____3131 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3156 =
      let uu____3157 =
        let uu____3164 =
          let uu____3165 = FStar_TypeChecker_Env.get_range env  in
          let uu____3166 =
            let uu____3177 =
              let uu____3178 =
                let uu____3183 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____3183, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3178  in
            ([[l_or_a_b]], [aa; bb], uu____3177)  in
          FStar_SMTEncoding_Term.mkForall uu____3165 uu____3166  in
        (uu____3164, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3157  in
    [uu____3156]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____3244 =
      let uu____3245 =
        let uu____3252 =
          let uu____3253 = FStar_TypeChecker_Env.get_range env  in
          let uu____3254 =
            let uu____3265 =
              let uu____3266 =
                let uu____3271 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3271, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3266  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____3265)  in
          FStar_SMTEncoding_Term.mkForall uu____3253 uu____3254  in
        (uu____3252, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3245  in
    [uu____3244]  in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y])  in
    let uu____3342 =
      let uu____3343 =
        let uu____3350 =
          let uu____3351 = FStar_TypeChecker_Env.get_range env  in
          let uu____3352 =
            let uu____3363 =
              let uu____3364 =
                let uu____3369 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____3369, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3364  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____3363)  in
          FStar_SMTEncoding_Term.mkForall uu____3351 uu____3352  in
        (uu____3350, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3343  in
    [uu____3342]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3438 =
      let uu____3439 =
        let uu____3446 =
          let uu____3447 = FStar_TypeChecker_Env.get_range env  in
          let uu____3448 =
            let uu____3459 =
              let uu____3460 =
                let uu____3465 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____3465, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3460  in
            ([[l_imp_a_b]], [aa; bb], uu____3459)  in
          FStar_SMTEncoding_Term.mkForall uu____3447 uu____3448  in
        (uu____3446, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3439  in
    [uu____3438]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____3526 =
      let uu____3527 =
        let uu____3534 =
          let uu____3535 = FStar_TypeChecker_Env.get_range env  in
          let uu____3536 =
            let uu____3547 =
              let uu____3548 =
                let uu____3553 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____3553, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____3548  in
            ([[l_iff_a_b]], [aa; bb], uu____3547)  in
          FStar_SMTEncoding_Term.mkForall uu____3535 uu____3536  in
        (uu____3534, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3527  in
    [uu____3526]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____3603 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____3603  in
    let uu____3606 =
      let uu____3607 =
        let uu____3614 =
          let uu____3615 = FStar_TypeChecker_Env.get_range env  in
          let uu____3616 =
            let uu____3627 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____3627)  in
          FStar_SMTEncoding_Term.mkForall uu____3615 uu____3616  in
        (uu____3614, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3607  in
    [uu____3606]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____3663 =
      let uu____3664 =
        let uu____3671 =
          let uu____3672 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____3672 range_ty  in
        let uu____3673 =
          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
            "typing_range_const"
           in
        (uu____3671, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____3673)
         in
      FStar_SMTEncoding_Util.mkAssume uu____3664  in
    [uu____3663]  in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t])  in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t  in
      let hastypeS =
        let uu____3711 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____3711 x1 t  in
      let uu____3712 = FStar_TypeChecker_Env.get_range env  in
      let uu____3713 =
        let uu____3724 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____3724)  in
      FStar_SMTEncoding_Term.mkForall uu____3712 uu____3713  in
    let uu____3741 =
      let uu____3742 =
        let uu____3749 =
          let uu____3750 = FStar_TypeChecker_Env.get_range env  in
          let uu____3751 =
            let uu____3762 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____3762)  in
          FStar_SMTEncoding_Term.mkForall uu____3750 uu____3751  in
        (uu____3749,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3742  in
    [uu____3741]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____3810 =
      let uu____3811 =
        let uu____3818 =
          let uu____3819 = FStar_TypeChecker_Env.get_range env  in
          let uu____3820 =
            let uu____3835 =
              let uu____3836 =
                let uu____3841 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____3842 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____3841, uu____3842)  in
              FStar_SMTEncoding_Util.mkAnd uu____3836  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____3835)
             in
          FStar_SMTEncoding_Term.mkForall' uu____3819 uu____3820  in
        (uu____3818,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____3811  in
    [uu____3810]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.true_lid, mk_true_interp);
    (FStar_Parser_Const.false_lid, mk_false_interp);
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____4318 =
            FStar_Util.find_opt
              (fun uu____4354  ->
                 match uu____4354 with
                 | (l,uu____4368) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____4318 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____4408,f) -> f env s tt
  
let (encode_smt_lemma :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____4465 =
          FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env
           in
        match uu____4465 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
  
let (encode_free_var :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____4523 =
                ((let uu____4526 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function
                         env.FStar_SMTEncoding_Env.tcenv t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____4526) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____4523
              then
                let arg_sorts =
                  let uu____4536 =
                    let uu____4537 = FStar_Syntax_Subst.compress t_norm  in
                    uu____4537.FStar_Syntax_Syntax.n  in
                  match uu____4536 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4543) ->
                      FStar_All.pipe_right binders
                        (FStar_List.map
                           (fun uu____4573  ->
                              FStar_SMTEncoding_Term.Term_sort))
                  | uu____4578 -> []  in
                let arity = FStar_List.length arg_sorts  in
                let uu____4580 =
                  FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                    env lid arity
                   in
                match uu____4580 with
                | (vname,vtok,env1) ->
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function"))
                       in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function"))
                       in
                    ([d; dd], env1)
              else
                (let uu____4609 = prims.is lid  in
                 if uu____4609
                 then
                   let vname =
                     FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                       lid
                      in
                   let uu____4617 = prims.mk lid vname  in
                   match uu____4617 with
                   | (tok,arity,definition) ->
                       let env1 =
                         FStar_SMTEncoding_Env.push_free_var env lid arity
                           vname (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____4644 =
                      let uu____4661 =
                        FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                          t_norm
                         in
                      match uu____4661 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____4687 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.FStar_SMTEncoding_Env.tcenv comp
                               in
                            if uu____4687
                            then
                              let uu____4690 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___104_4693 =
                                     env.FStar_SMTEncoding_Env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___104_4693.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___104_4693.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___104_4693.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___104_4693.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___104_4693.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___104_4693.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___104_4693.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___104_4693.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___104_4693.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___104_4693.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___104_4693.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___104_4693.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___104_4693.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___104_4693.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___104_4693.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___104_4693.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___104_4693.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___104_4693.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___104_4693.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___104_4693.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___104_4693.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___104_4693.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___104_4693.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___104_4693.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___104_4693.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___104_4693.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___104_4693.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___104_4693.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___104_4693.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___104_4693.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___104_4693.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___104_4693.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___104_4693.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___104_4693.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___104_4693.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___104_4693.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___104_4693.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___104_4693.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____4690
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____4711 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.FStar_SMTEncoding_Env.tcenv comp1
                               in
                            (args, uu____4711)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____4644 with
                    | (formals,(pre_opt,res_t)) ->
                        let arity = FStar_List.length formals  in
                        let uu____4781 =
                          FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                            env lid arity
                           in
                        (match uu____4781 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____4806 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___94_4862  ->
                                       match uu___94_4862 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____4866 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4866 with
                                            | (uu____4887,(xxsym,uu____4889))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____4907 =
                                                  let uu____4908 =
                                                    let uu____4915 =
                                                      let uu____4916 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____4917 =
                                                        let uu____4928 =
                                                          let uu____4929 =
                                                            let uu____4934 =
                                                              let uu____4935
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (FStar_SMTEncoding_Env.escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____4935
                                                               in
                                                            (vapp,
                                                              uu____4934)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____4929
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____4928)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____4916 uu____4917
                                                       in
                                                    (uu____4915,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (FStar_SMTEncoding_Env.escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4908
                                                   in
                                                [uu____4907])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____4946 =
                                             FStar_Util.prefix vars  in
                                           (match uu____4946 with
                                            | (uu____4967,(xxsym,uu____4969))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  }  in
                                                let tp_name =
                                                  FStar_SMTEncoding_Env.mk_term_projector_name
                                                    d f1
                                                   in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx])
                                                   in
                                                let uu____4992 =
                                                  let uu____4993 =
                                                    let uu____5000 =
                                                      let uu____5001 =
                                                        FStar_Syntax_Syntax.range_of_fv
                                                          fv
                                                         in
                                                      let uu____5002 =
                                                        let uu____5013 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____5013)
                                                         in
                                                      FStar_SMTEncoding_Term.mkForall
                                                        uu____5001 uu____5002
                                                       in
                                                    (uu____5000,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4993
                                                   in
                                                [uu____4992])
                                       | uu____5022 -> []))
                                in
                             let uu____5023 =
                               FStar_SMTEncoding_EncodeTerm.encode_binders
                                 FStar_Pervasives_Native.None formals env1
                                in
                             (match uu____5023 with
                              | (vars,guards,env',decls1,uu____5050) ->
                                  let uu____5063 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5076 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____5076, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____5080 =
                                          FStar_SMTEncoding_EncodeTerm.encode_formula
                                            p env'
                                           in
                                        (match uu____5080 with
                                         | (g,ds) ->
                                             let uu____5093 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____5093,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____5063 with
                                   | (guard,decls11) ->
                                       let vtok_app =
                                         FStar_SMTEncoding_EncodeTerm.mk_Apply
                                           vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____5110 =
                                           let uu____5117 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____5117)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____5110
                                          in
                                       let uu____5122 =
                                         let vname_decl =
                                           let uu____5130 =
                                             let uu____5141 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____5157  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____5141,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____5130
                                            in
                                         let uu____5164 =
                                           let env2 =
                                             let uu___105_5170 = env1  in
                                             {
                                               FStar_SMTEncoding_Env.bvar_bindings
                                                 =
                                                 (uu___105_5170.FStar_SMTEncoding_Env.bvar_bindings);
                                               FStar_SMTEncoding_Env.fvar_bindings
                                                 =
                                                 (uu___105_5170.FStar_SMTEncoding_Env.fvar_bindings);
                                               FStar_SMTEncoding_Env.depth =
                                                 (uu___105_5170.FStar_SMTEncoding_Env.depth);
                                               FStar_SMTEncoding_Env.tcenv =
                                                 (uu___105_5170.FStar_SMTEncoding_Env.tcenv);
                                               FStar_SMTEncoding_Env.warn =
                                                 (uu___105_5170.FStar_SMTEncoding_Env.warn);
                                               FStar_SMTEncoding_Env.cache =
                                                 (uu___105_5170.FStar_SMTEncoding_Env.cache);
                                               FStar_SMTEncoding_Env.nolabels
                                                 =
                                                 (uu___105_5170.FStar_SMTEncoding_Env.nolabels);
                                               FStar_SMTEncoding_Env.use_zfuel_name
                                                 =
                                                 (uu___105_5170.FStar_SMTEncoding_Env.use_zfuel_name);
                                               FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                 =
                                                 encode_non_total_function_typ;
                                               FStar_SMTEncoding_Env.current_module_name
                                                 =
                                                 (uu___105_5170.FStar_SMTEncoding_Env.current_module_name);
                                               FStar_SMTEncoding_Env.encoding_quantifier
                                                 =
                                                 (uu___105_5170.FStar_SMTEncoding_Env.encoding_quantifier)
                                             }  in
                                           let uu____5171 =
                                             let uu____5172 =
                                               FStar_SMTEncoding_EncodeTerm.head_normal
                                                 env2 tt
                                                in
                                             Prims.op_Negation uu____5172  in
                                           if uu____5171
                                           then
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____5164 with
                                         | (tok_typing,decls2) ->
                                             let uu____5186 =
                                               match formals with
                                               | [] ->
                                                   let tok_typing1 =
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       (tok_typing,
                                                         (FStar_Pervasives_Native.Some
                                                            "function token typing"),
                                                         (Prims.strcat
                                                            "function_token_typing_"
                                                            vname))
                                                      in
                                                   let uu____5204 =
                                                     let uu____5205 =
                                                       let uu____5208 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_17  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_17)
                                                         uu____5208
                                                        in
                                                     FStar_SMTEncoding_Env.push_free_var
                                                       env1 lid arity vname
                                                       uu____5205
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____5204)
                                               | uu____5217 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_app_0 =
                                                     let uu____5228 =
                                                       let uu____5235 =
                                                         FStar_List.hd vars
                                                          in
                                                       [uu____5235]  in
                                                     FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                       vtok_tm uu____5228
                                                      in
                                                   let name_tok_corr_formula
                                                     pat =
                                                     let uu____5254 =
                                                       FStar_Syntax_Syntax.range_of_fv
                                                         fv
                                                        in
                                                     let uu____5255 =
                                                       let uu____5266 =
                                                         FStar_SMTEncoding_Util.mkEq
                                                           (vtok_app, vapp)
                                                          in
                                                       ([[pat]], vars,
                                                         uu____5266)
                                                        in
                                                     FStar_SMTEncoding_Term.mkForall
                                                       uu____5254 uu____5255
                                                      in
                                                   let name_tok_corr =
                                                     let uu____5276 =
                                                       let uu____5283 =
                                                         name_tok_corr_formula
                                                           vtok_app
                                                          in
                                                       (uu____5283,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____5276
                                                      in
                                                   let tok_typing1 =
                                                     let ff =
                                                       ("ty",
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     let f =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         ff
                                                        in
                                                     let vtok_app_l =
                                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                         vtok_tm [ff]
                                                        in
                                                     let vtok_app_r =
                                                       FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                         f
                                                         [(vtok,
                                                            FStar_SMTEncoding_Term.Term_sort)]
                                                        in
                                                     let guarded_tok_typing =
                                                       let uu____5310 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5311 =
                                                         let uu____5322 =
                                                           let uu____5323 =
                                                             let uu____5328 =
                                                               FStar_SMTEncoding_Term.mk_NoHoist
                                                                 f tok_typing
                                                                in
                                                             let uu____5329 =
                                                               name_tok_corr_formula
                                                                 vapp
                                                                in
                                                             (uu____5328,
                                                               uu____5329)
                                                              in
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             uu____5323
                                                            in
                                                         ([[vtok_app_r]],
                                                           [ff], uu____5322)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____5310
                                                         uu____5311
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       (guarded_tok_typing,
                                                         (FStar_Pervasives_Native.Some
                                                            "function token typing"),
                                                         (Prims.strcat
                                                            "function_token_typing_"
                                                            vname))
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____5186 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____5122 with
                                        | (decls2,env2) ->
                                            let uu____5374 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____5384 =
                                                FStar_SMTEncoding_EncodeTerm.encode_term
                                                  res_t1 env'
                                                 in
                                              match uu____5384 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____5399 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t, uu____5399,
                                                    decls)
                                               in
                                            (match uu____5374 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____5416 =
                                                     let uu____5423 =
                                                       let uu____5424 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5425 =
                                                         let uu____5436 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____5436)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____5424
                                                         uu____5425
                                                        in
                                                     (uu____5423,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____5416
                                                    in
                                                 let freshness =
                                                   let uu____5448 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____5448
                                                   then
                                                     let uu____5453 =
                                                       let uu____5454 =
                                                         FStar_Syntax_Syntax.range_of_fv
                                                           fv
                                                          in
                                                       let uu____5455 =
                                                         let uu____5466 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____5481 =
                                                           FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                             ()
                                                            in
                                                         (vname, uu____5466,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____5481)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____5454
                                                         uu____5455
                                                        in
                                                     let uu____5484 =
                                                       let uu____5487 =
                                                         let uu____5488 =
                                                           FStar_Syntax_Syntax.range_of_fv
                                                             fv
                                                            in
                                                         pretype_axiom
                                                           uu____5488 env2
                                                           vapp vars
                                                          in
                                                       [uu____5487]  in
                                                     uu____5453 :: uu____5484
                                                   else []  in
                                                 let g =
                                                   let uu____5493 =
                                                     let uu____5496 =
                                                       let uu____5499 =
                                                         let uu____5502 =
                                                           let uu____5505 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____5505
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____5502
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____5499
                                                        in
                                                     FStar_List.append decls2
                                                       uu____5496
                                                      in
                                                   FStar_List.append decls11
                                                     uu____5493
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (FStar_SMTEncoding_Env.fvar_binding,FStar_SMTEncoding_Term.decl
                                                Prims.list,FStar_SMTEncoding_Env.env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____5546 =
            FStar_SMTEncoding_Env.lookup_fvar_binding env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____5546 with
          | FStar_Pervasives_Native.None  ->
              let uu____5557 = encode_free_var false env x t t_norm []  in
              (match uu____5557 with
               | (decls,env1) ->
                   let fvb =
                     FStar_SMTEncoding_Env.lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (fvb, decls, env1))
          | FStar_Pervasives_Native.Some fvb -> (fvb, [], env)
  
let (encode_top_level_val :
  Prims.bool ->
    FStar_SMTEncoding_Env.env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = FStar_SMTEncoding_EncodeTerm.norm env t  in
            let uu____5624 = encode_free_var uninterpreted env lid t tt quals
               in
            match uu____5624 with
            | (decls,env1) ->
                let uu____5643 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____5643
                then
                  let uu____5650 =
                    let uu____5653 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____5653  in
                  (uu____5650, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____5711  ->
                fun lb  ->
                  match uu____5711 with
                  | (decls,env1) ->
                      let uu____5731 =
                        let uu____5738 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____5738
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____5731 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____5761 = FStar_Syntax_Util.head_and_args t  in
    match uu____5761 with
    | (hd1,args) ->
        let uu____5798 =
          let uu____5799 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5799.FStar_Syntax_Syntax.n  in
        (match uu____5798 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____5803,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____5822 -> false)
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____5828 -> false
  
let (encode_top_level_let :
  FStar_SMTEncoding_Env.env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____5856  ->
      fun quals  ->
        match uu____5856 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____5948 = FStar_Util.first_N nbinders formals  in
              match uu____5948 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____6029  ->
                         fun uu____6030  ->
                           match (uu____6029, uu____6030) with
                           | ((formal,uu____6048),(binder,uu____6050)) ->
                               let uu____6059 =
                                 let uu____6066 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____6066)  in
                               FStar_Syntax_Syntax.NT uu____6059) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____6078 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____6109  ->
                              match uu____6109 with
                              | (x,i) ->
                                  let uu____6120 =
                                    let uu___106_6121 = x  in
                                    let uu____6122 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___106_6121.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___106_6121.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6122
                                    }  in
                                  (uu____6120, i)))
                       in
                    FStar_All.pipe_right uu____6078
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____6140 =
                      let uu____6145 = FStar_Syntax_Subst.compress body  in
                      let uu____6146 =
                        let uu____6147 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____6147
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____6145 uu____6146
                       in
                    uu____6140 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____6226 =
                  FStar_TypeChecker_Env.is_reifiable_comp
                    env.FStar_SMTEncoding_Env.tcenv c
                   in
                if uu____6226
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___107_6231 = env.FStar_SMTEncoding_Env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___107_6231.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___107_6231.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___107_6231.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___107_6231.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___107_6231.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___107_6231.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___107_6231.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___107_6231.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___107_6231.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___107_6231.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___107_6231.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___107_6231.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___107_6231.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___107_6231.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___107_6231.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___107_6231.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___107_6231.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___107_6231.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___107_6231.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___107_6231.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___107_6231.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___107_6231.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___107_6231.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___107_6231.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___107_6231.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___107_6231.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___107_6231.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___107_6231.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___107_6231.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___107_6231.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___107_6231.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___107_6231.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___107_6231.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___107_6231.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___107_6231.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___107_6231.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___107_6231.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___107_6231.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____6272 = FStar_Syntax_Util.abs_formals e  in
                match uu____6272 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____6344::uu____6345 ->
                         let uu____6360 =
                           let uu____6361 =
                             let uu____6364 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____6364
                              in
                           uu____6361.FStar_Syntax_Syntax.n  in
                         (match uu____6360 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____6413 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____6413 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____6461 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____6461
                                   then
                                     let uu____6500 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____6500 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____6598  ->
                                                   fun uu____6599  ->
                                                     match (uu____6598,
                                                             uu____6599)
                                                     with
                                                     | ((x,uu____6617),
                                                        (b,uu____6619)) ->
                                                         let uu____6628 =
                                                           let uu____6635 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____6635)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____6628)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____6643 =
                                            let uu____6668 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____6668)  in
                                          (uu____6643, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____6750 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____6750 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____6891) ->
                              let uu____6896 =
                                let uu____6921 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____6921  in
                              (uu____6896, true)
                          | uu____6998 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.Weak;
                                  FStar_TypeChecker_Normalize.HNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.FStar_SMTEncoding_Env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____7000 ->
                              let uu____7001 =
                                let uu____7002 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____7003 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____7002 uu____7003
                                 in
                              failwith uu____7001)
                     | uu____7032 ->
                         let rec aux' t_norm2 =
                           let uu____7067 =
                             let uu____7068 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____7068.FStar_Syntax_Syntax.n  in
                           match uu____7067 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____7117 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____7117 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____7155 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____7155 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____7259) ->
                               aux' bv.FStar_Syntax_Syntax.sort
                           | uu____7264 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____7328 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____7328
               then encode_top_level_vals env bindings quals
               else
                 (let uu____7340 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____7403  ->
                            fun lb  ->
                              match uu____7403 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____7458 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____7458
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      FStar_SMTEncoding_EncodeTerm.whnf env1
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____7461 =
                                      let uu____7470 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____7470
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____7461 with
                                    | (tok,decl,env2) ->
                                        ((tok :: toks), (t_norm :: typs),
                                          (decl :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____7340 with
                  | (toks,typs,decls,env1) ->
                      let toks_fvbs = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 rng curry fvb vars =
                        let mk_fv uu____7595 =
                          if
                            fvb.FStar_SMTEncoding_Env.smt_arity =
                              (Prims.parse_int "0")
                          then
                            FStar_SMTEncoding_Util.mkFreeV
                              ((fvb.FStar_SMTEncoding_Env.smt_id),
                                FStar_SMTEncoding_Term.Term_sort)
                          else
                            FStar_SMTEncoding_EncodeTerm.raise_arity_mismatch
                              fvb.FStar_SMTEncoding_Env.smt_id
                              fvb.FStar_SMTEncoding_Env.smt_arity
                              (Prims.parse_int "0") rng
                           in
                        match vars with
                        | [] -> mk_fv ()
                        | uu____7601 ->
                            if curry
                            then
                              (match fvb.FStar_SMTEncoding_Env.smt_token with
                               | FStar_Pervasives_Native.Some ftok ->
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply ftok
                                     vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____7609 = mk_fv ()  in
                                   FStar_SMTEncoding_EncodeTerm.mk_Apply
                                     uu____7609 vars)
                            else
                              (let uu____7611 =
                                 FStar_List.map
                                   FStar_SMTEncoding_Util.mkFreeV vars
                                  in
                               FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                 rng
                                 (FStar_SMTEncoding_Term.Var
                                    (fvb.FStar_SMTEncoding_Env.smt_id))
                                 fvb.FStar_SMTEncoding_Env.smt_arity
                                 uu____7611)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                        match (bindings1, typs2, toks1) with
                        | ({ FStar_Syntax_Syntax.lbname = lbn;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____7671;
                             FStar_Syntax_Syntax.lbeff = uu____7672;
                             FStar_Syntax_Syntax.lbdef = e;
                             FStar_Syntax_Syntax.lbattrs = uu____7674;
                             FStar_Syntax_Syntax.lbpos = uu____7675;_}::[],t_norm::[],fvb::[])
                            ->
                            let flid = fvb.FStar_SMTEncoding_Env.fvar_lid  in
                            let uu____7699 =
                              let uu____7708 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.FStar_SMTEncoding_Env.tcenv uvs
                                  [e; t_norm]
                                 in
                              match uu____7708 with
                              | (tcenv',uu____7726,e_t) ->
                                  let uu____7732 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____7749 -> failwith "Impossible"  in
                                  (match uu____7732 with
                                   | (e1,t_norm1) ->
                                       ((let uu___110_7775 = env2  in
                                         {
                                           FStar_SMTEncoding_Env.bvar_bindings
                                             =
                                             (uu___110_7775.FStar_SMTEncoding_Env.bvar_bindings);
                                           FStar_SMTEncoding_Env.fvar_bindings
                                             =
                                             (uu___110_7775.FStar_SMTEncoding_Env.fvar_bindings);
                                           FStar_SMTEncoding_Env.depth =
                                             (uu___110_7775.FStar_SMTEncoding_Env.depth);
                                           FStar_SMTEncoding_Env.tcenv =
                                             tcenv';
                                           FStar_SMTEncoding_Env.warn =
                                             (uu___110_7775.FStar_SMTEncoding_Env.warn);
                                           FStar_SMTEncoding_Env.cache =
                                             (uu___110_7775.FStar_SMTEncoding_Env.cache);
                                           FStar_SMTEncoding_Env.nolabels =
                                             (uu___110_7775.FStar_SMTEncoding_Env.nolabels);
                                           FStar_SMTEncoding_Env.use_zfuel_name
                                             =
                                             (uu___110_7775.FStar_SMTEncoding_Env.use_zfuel_name);
                                           FStar_SMTEncoding_Env.encode_non_total_function_typ
                                             =
                                             (uu___110_7775.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                           FStar_SMTEncoding_Env.current_module_name
                                             =
                                             (uu___110_7775.FStar_SMTEncoding_Env.current_module_name);
                                           FStar_SMTEncoding_Env.encoding_quantifier
                                             =
                                             (uu___110_7775.FStar_SMTEncoding_Env.encoding_quantifier)
                                         }), e1, t_norm1))
                               in
                            (match uu____7699 with
                             | (env',e1,t_norm1) ->
                                 let uu____7789 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____7789 with
                                  | ((binders,body,uu____7810,t_body),curry)
                                      ->
                                      ((let uu____7822 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.FStar_SMTEncoding_Env.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____7822
                                        then
                                          let uu____7823 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____7824 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____7823 uu____7824
                                        else ());
                                       (let uu____7826 =
                                          FStar_SMTEncoding_EncodeTerm.encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____7826 with
                                        | (vars,guards,env'1,binder_decls,uu____7853)
                                            ->
                                            let body1 =
                                              let uu____7867 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  t_norm1
                                                 in
                                              if uu____7867
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.FStar_SMTEncoding_Env.tcenv
                                                  body
                                              else
                                                FStar_Syntax_Util.ascribe
                                                  body
                                                  ((FStar_Util.Inl t_body),
                                                    FStar_Pervasives_Native.None)
                                               in
                                            let app =
                                              let uu____7888 =
                                                FStar_Syntax_Util.range_of_lbname
                                                  lbn
                                                 in
                                              mk_app1 uu____7888 curry fvb
                                                vars
                                               in
                                            let uu____7889 =
                                              let uu____7898 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____7898
                                              then
                                                let uu____7909 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____7910 =
                                                  FStar_SMTEncoding_EncodeTerm.encode_formula
                                                    body1 env'1
                                                   in
                                                (uu____7909, uu____7910)
                                              else
                                                (let uu____7920 =
                                                   FStar_SMTEncoding_EncodeTerm.encode_term
                                                     body1 env'1
                                                    in
                                                 (app, uu____7920))
                                               in
                                            (match uu____7889 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____7943 =
                                                     let uu____7950 =
                                                       let uu____7951 =
                                                         FStar_Syntax_Util.range_of_lbname
                                                           lbn
                                                          in
                                                       let uu____7952 =
                                                         let uu____7963 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____7963)
                                                          in
                                                       FStar_SMTEncoding_Term.mkForall
                                                         uu____7951
                                                         uu____7952
                                                        in
                                                     let uu____7972 =
                                                       let uu____7973 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____7973
                                                        in
                                                     (uu____7950, uu____7972,
                                                       (Prims.strcat
                                                          "equation_"
                                                          fvb.FStar_SMTEncoding_Env.smt_id))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____7943
                                                    in
                                                 let uu____7974 =
                                                   let uu____7977 =
                                                     let uu____7980 =
                                                       let uu____7983 =
                                                         let uu____7986 =
                                                           primitive_type_axioms
                                                             env2.FStar_SMTEncoding_Env.tcenv
                                                             flid
                                                             fvb.FStar_SMTEncoding_Env.smt_id
                                                             app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____7986
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____7983
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____7980
                                                      in
                                                   FStar_List.append decls1
                                                     uu____7977
                                                    in
                                                 (uu____7974, env2))))))
                        | uu____7991 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                        let fuel =
                          let uu____8054 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                              "fuel"
                             in
                          (uu____8054, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____8057 =
                          FStar_All.pipe_right toks1
                            (FStar_List.fold_left
                               (fun uu____8104  ->
                                  fun fvb  ->
                                    match uu____8104 with
                                    | (gtoks,env3) ->
                                        let flid =
                                          fvb.FStar_SMTEncoding_Env.fvar_lid
                                           in
                                        let g =
                                          let uu____8150 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____8150
                                           in
                                        let gtok =
                                          let uu____8152 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar
                                            uu____8152
                                           in
                                        let env4 =
                                          let uu____8154 =
                                            let uu____8157 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_18  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_18) uu____8157
                                             in
                                          FStar_SMTEncoding_Env.push_free_var
                                            env3 flid
                                            fvb.FStar_SMTEncoding_Env.smt_arity
                                            gtok uu____8154
                                           in
                                        (((fvb, g, gtok) :: gtoks), env4))
                               ([], env2))
                           in
                        match uu____8057 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____8263 t_norm
                              uu____8265 =
                              match (uu____8263, uu____8265) with
                              | ((fvb,g,gtok),{
                                                FStar_Syntax_Syntax.lbname =
                                                  lbn;
                                                FStar_Syntax_Syntax.lbunivs =
                                                  uvs;
                                                FStar_Syntax_Syntax.lbtyp =
                                                  uu____8293;
                                                FStar_Syntax_Syntax.lbeff =
                                                  uu____8294;
                                                FStar_Syntax_Syntax.lbdef = e;
                                                FStar_Syntax_Syntax.lbattrs =
                                                  uu____8296;
                                                FStar_Syntax_Syntax.lbpos =
                                                  uu____8297;_})
                                  ->
                                  let uu____8318 =
                                    let uu____8327 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.FStar_SMTEncoding_Env.tcenv uvs
                                        [e; t_norm]
                                       in
                                    match uu____8327 with
                                    | (tcenv',uu____8345,e_t) ->
                                        let uu____8351 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____8368 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____8351 with
                                         | (e1,t_norm1) ->
                                             ((let uu___111_8394 = env3  in
                                               {
                                                 FStar_SMTEncoding_Env.bvar_bindings
                                                   =
                                                   (uu___111_8394.FStar_SMTEncoding_Env.bvar_bindings);
                                                 FStar_SMTEncoding_Env.fvar_bindings
                                                   =
                                                   (uu___111_8394.FStar_SMTEncoding_Env.fvar_bindings);
                                                 FStar_SMTEncoding_Env.depth
                                                   =
                                                   (uu___111_8394.FStar_SMTEncoding_Env.depth);
                                                 FStar_SMTEncoding_Env.tcenv
                                                   = tcenv';
                                                 FStar_SMTEncoding_Env.warn =
                                                   (uu___111_8394.FStar_SMTEncoding_Env.warn);
                                                 FStar_SMTEncoding_Env.cache
                                                   =
                                                   (uu___111_8394.FStar_SMTEncoding_Env.cache);
                                                 FStar_SMTEncoding_Env.nolabels
                                                   =
                                                   (uu___111_8394.FStar_SMTEncoding_Env.nolabels);
                                                 FStar_SMTEncoding_Env.use_zfuel_name
                                                   =
                                                   (uu___111_8394.FStar_SMTEncoding_Env.use_zfuel_name);
                                                 FStar_SMTEncoding_Env.encode_non_total_function_typ
                                                   =
                                                   (uu___111_8394.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                                                 FStar_SMTEncoding_Env.current_module_name
                                                   =
                                                   (uu___111_8394.FStar_SMTEncoding_Env.current_module_name);
                                                 FStar_SMTEncoding_Env.encoding_quantifier
                                                   =
                                                   (uu___111_8394.FStar_SMTEncoding_Env.encoding_quantifier)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____8318 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____8413 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.FStar_SMTEncoding_Env.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____8413
                                         then
                                           let uu____8414 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____8415 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____8416 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____8414 uu____8415 uu____8416
                                         else ());
                                        (let uu____8418 =
                                           destruct_bound_function
                                             fvb.FStar_SMTEncoding_Env.fvar_lid
                                             t_norm1 e1
                                            in
                                         match uu____8418 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____8455 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.FStar_SMTEncoding_Env.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____8455
                                               then
                                                 let uu____8456 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____8457 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____8458 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____8459 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____8456 uu____8457
                                                   uu____8458 uu____8459
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____8463 =
                                                 FStar_SMTEncoding_EncodeTerm.encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____8463 with
                                               | (vars,guards,env'1,binder_decls,uu____8494)
                                                   ->
                                                   let decl_g =
                                                     let uu____8508 =
                                                       let uu____8519 =
                                                         let uu____8522 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____8522
                                                          in
                                                       (g, uu____8519,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____8508
                                                      in
                                                   let env02 =
                                                     FStar_SMTEncoding_Env.push_zfuel_name
                                                       env01
                                                       fvb.FStar_SMTEncoding_Env.fvar_lid
                                                       g
                                                      in
                                                   let decl_g_tok =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (gtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Token for fuel-instrumented partial applications"))
                                                      in
                                                   let vars_tm =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       vars
                                                      in
                                                   let app =
                                                     let uu____8535 =
                                                       let uu____8542 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       ((fvb.FStar_SMTEncoding_Env.smt_id),
                                                         uu____8542)
                                                        in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8535
                                                      in
                                                   let gsapp =
                                                     let uu____8548 =
                                                       let uu____8555 =
                                                         let uu____8558 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____8558 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____8555)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8548
                                                      in
                                                   let gmax =
                                                     let uu____8564 =
                                                       let uu____8571 =
                                                         let uu____8574 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____8574 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____8571)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____8564
                                                      in
                                                   let body1 =
                                                     let uu____8580 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         t_norm1
                                                        in
                                                     if uu____8580
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.FStar_SMTEncoding_Env.tcenv
                                                         body
                                                     else body  in
                                                   let uu____8582 =
                                                     FStar_SMTEncoding_EncodeTerm.encode_term
                                                       body1 env'1
                                                      in
                                                   (match uu____8582 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____8600 =
                                                            let uu____8607 =
                                                              let uu____8608
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8609
                                                                =
                                                                let uu____8624
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                   in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____8624)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall'
                                                                uu____8608
                                                                uu____8609
                                                               in
                                                            let uu____8635 =
                                                              let uu____8636
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  (fvb.FStar_SMTEncoding_Env.fvar_lid).FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____8636
                                                               in
                                                            (uu____8607,
                                                              uu____8635,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8600
                                                           in
                                                        let eqn_f =
                                                          let uu____8638 =
                                                            let uu____8645 =
                                                              let uu____8646
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8647
                                                                =
                                                                let uu____8658
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____8658)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8646
                                                                uu____8647
                                                               in
                                                            (uu____8645,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8638
                                                           in
                                                        let eqn_g' =
                                                          let uu____8668 =
                                                            let uu____8675 =
                                                              let uu____8676
                                                                =
                                                                FStar_Syntax_Util.range_of_lbname
                                                                  lbn
                                                                 in
                                                              let uu____8677
                                                                =
                                                                let uu____8688
                                                                  =
                                                                  let uu____8689
                                                                    =
                                                                    let uu____8694
                                                                    =
                                                                    let uu____8695
                                                                    =
                                                                    let uu____8702
                                                                    =
                                                                    let uu____8705
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____8705
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____8702)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____8695
                                                                     in
                                                                    (gsapp,
                                                                    uu____8694)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____8689
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____8688)
                                                                 in
                                                              FStar_SMTEncoding_Term.mkForall
                                                                uu____8676
                                                                uu____8677
                                                               in
                                                            (uu____8675,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____8668
                                                           in
                                                        let uu____8716 =
                                                          let uu____8725 =
                                                            FStar_SMTEncoding_EncodeTerm.encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____8725
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____8754)
                                                              ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1
                                                                 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1))
                                                                 in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____8775
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu____8775
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____8776
                                                                  =
                                                                  let uu____8783
                                                                    =
                                                                    let uu____8784
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8785
                                                                    =
                                                                    let uu____8796
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8796)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8784
                                                                    uu____8785
                                                                     in
                                                                  (uu____8783,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____8776
                                                                 in
                                                              let uu____8805
                                                                =
                                                                let uu____8814
                                                                  =
                                                                  FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____8814
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____8829
                                                                    =
                                                                    let uu____8832
                                                                    =
                                                                    let uu____8833
                                                                    =
                                                                    let uu____8840
                                                                    =
                                                                    let uu____8841
                                                                    =
                                                                    FStar_Syntax_Util.range_of_lbname
                                                                    lbn  in
                                                                    let uu____8842
                                                                    =
                                                                    let uu____8853
                                                                    =
                                                                    let uu____8854
                                                                    =
                                                                    let uu____8859
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____8859,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____8854
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____8853)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____8841
                                                                    uu____8842
                                                                     in
                                                                    (uu____8840,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____8833
                                                                     in
                                                                    [uu____8832]
                                                                     in
                                                                    (d3,
                                                                    uu____8829)
                                                                 in
                                                              (match uu____8805
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                           in
                                                        (match uu____8716
                                                         with
                                                         | (aux_decls,g_typing)
                                                             ->
                                                             ((FStar_List.append
                                                                 binder_decls
                                                                 (FStar_List.append
                                                                    decls2
                                                                    (
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                               (FStar_List.append
                                                                  [eqn_g;
                                                                  eqn_g';
                                                                  eqn_f]
                                                                  g_typing),
                                                               env02))))))))
                               in
                            let uu____8918 =
                              let uu____8931 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____8988  ->
                                   fun uu____8989  ->
                                     match (uu____8988, uu____8989) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____9104 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____9104 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____8931
                               in
                            (match uu____8918 with
                             | (decls2,eqns,env01) ->
                                 let uu____9177 =
                                   let isDeclFun uu___95_9191 =
                                     match uu___95_9191 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____9192 -> true
                                     | uu____9203 -> false  in
                                   let uu____9204 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____9204
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____9177 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____9244 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___96_9248  ->
                                 match uu___96_9248 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____9249 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____9255 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.FStar_SMTEncoding_Env.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____9255)))
                         in
                      if uu____9244
                      then (decls1, env1)
                      else
                        (try
                           if Prims.op_Negation is_rec
                           then
                             encode_non_rec_lbdef bindings typs1 toks_fvbs
                               env1
                           else
                             encode_rec_lbdefs bindings typs1 toks_fvbs env1
                         with
                         | FStar_SMTEncoding_Env.Inner_let_rec  ->
                             (decls1, env1)))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____9307 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____9307
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec (encode_sigelt :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____9368 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____9368 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____9372 = encode_sigelt' env se  in
      match uu____9372 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____9384 =
                  let uu____9385 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____9385  in
                [uu____9384]
            | uu____9386 ->
                let uu____9387 =
                  let uu____9390 =
                    let uu____9391 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9391  in
                  uu____9390 :: g  in
                let uu____9392 =
                  let uu____9395 =
                    let uu____9396 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____9396  in
                  [uu____9395]  in
                FStar_List.append uu____9387 uu____9392
             in
          (g1, env1)

and (encode_sigelt' :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____9409 =
          let uu____9410 = FStar_Syntax_Subst.compress t  in
          uu____9410.FStar_Syntax_Syntax.n  in
        match uu____9409 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9414)) -> s = "opaque_to_smt"
        | uu____9415 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____9422 =
          let uu____9423 = FStar_Syntax_Subst.compress t  in
          uu____9423.FStar_Syntax_Syntax.n  in
        match uu____9422 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____9427)) -> s = "uninterpreted_by_smt"
        | uu____9428 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____9433 ->
          failwith
            "impossible -- new_effect_for_free should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_splice uu____9438 ->
          failwith "impossible -- splice should have been removed by Tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____9449 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____9450 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____9451 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____9464 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____9466 =
            let uu____9467 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____9467 Prims.op_Negation  in
          if uu____9466
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____9493 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____9523 =
                 FStar_Syntax_Util.arrow_formals_comp
                   a.FStar_Syntax_Syntax.action_typ
                  in
               match uu____9523 with
               | (formals,uu____9541) ->
                   let arity = FStar_List.length formals  in
                   let uu____9559 =
                     FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                       env1 a.FStar_Syntax_Syntax.action_name arity
                      in
                   (match uu____9559 with
                    | (aname,atok,env2) ->
                        let uu____9579 =
                          let uu____9584 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          FStar_SMTEncoding_EncodeTerm.encode_term uu____9584
                            env2
                           in
                        (match uu____9579 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____9596 =
                                 let uu____9597 =
                                   let uu____9608 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____9624  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____9608,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____9597
                                  in
                               [uu____9596;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____9633 =
                               let aux uu____9689 uu____9690 =
                                 match (uu____9689, uu____9690) with
                                 | ((bv,uu____9742),(env3,acc_sorts,acc)) ->
                                     let uu____9780 =
                                       FStar_SMTEncoding_Env.gen_term_var
                                         env3 bv
                                        in
                                     (match uu____9780 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____9633 with
                              | (uu____9852,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____9875 =
                                      let uu____9882 =
                                        let uu____9883 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____9884 =
                                          let uu____9895 =
                                            let uu____9896 =
                                              let uu____9901 =
                                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                                  tm xs_sorts
                                                 in
                                              (app, uu____9901)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____9896
                                             in
                                          ([[app]], xs_sorts, uu____9895)  in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____9883 uu____9884
                                         in
                                      (uu____9882,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9875
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app =
                                      FStar_SMTEncoding_EncodeTerm.mk_Apply
                                        tok_term xs_sorts
                                       in
                                    let uu____9913 =
                                      let uu____9920 =
                                        let uu____9921 =
                                          FStar_Ident.range_of_lid
                                            a.FStar_Syntax_Syntax.action_name
                                           in
                                        let uu____9922 =
                                          let uu____9933 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts, uu____9933)
                                           in
                                        FStar_SMTEncoding_Term.mkForall
                                          uu____9921 uu____9922
                                         in
                                      (uu____9920,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____9913
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____9944 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____9944 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9970,uu____9971) when
          FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____9972 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
              (Prims.parse_int "4")
             in
          (match uu____9972 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____9987,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____9993 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___97_9997  ->
                      match uu___97_9997 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____9998 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____10003 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10004 -> false))
               in
            Prims.op_Negation uu____9993  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____10011 =
               let uu____10018 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____10018 env fv t quals  in
             match uu____10011 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____10033 =
                   let uu____10034 =
                     primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv
                       lid tname tsym
                      in
                   FStar_List.append decls uu____10034  in
                 (uu____10033, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____10040 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____10040 with
           | (uvs,f1) ->
               let env1 =
                 let uu___114_10052 = env  in
                 let uu____10053 =
                   FStar_TypeChecker_Env.push_univ_vars
                     env.FStar_SMTEncoding_Env.tcenv uvs
                    in
                 {
                   FStar_SMTEncoding_Env.bvar_bindings =
                     (uu___114_10052.FStar_SMTEncoding_Env.bvar_bindings);
                   FStar_SMTEncoding_Env.fvar_bindings =
                     (uu___114_10052.FStar_SMTEncoding_Env.fvar_bindings);
                   FStar_SMTEncoding_Env.depth =
                     (uu___114_10052.FStar_SMTEncoding_Env.depth);
                   FStar_SMTEncoding_Env.tcenv = uu____10053;
                   FStar_SMTEncoding_Env.warn =
                     (uu___114_10052.FStar_SMTEncoding_Env.warn);
                   FStar_SMTEncoding_Env.cache =
                     (uu___114_10052.FStar_SMTEncoding_Env.cache);
                   FStar_SMTEncoding_Env.nolabels =
                     (uu___114_10052.FStar_SMTEncoding_Env.nolabels);
                   FStar_SMTEncoding_Env.use_zfuel_name =
                     (uu___114_10052.FStar_SMTEncoding_Env.use_zfuel_name);
                   FStar_SMTEncoding_Env.encode_non_total_function_typ =
                     (uu___114_10052.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                   FStar_SMTEncoding_Env.current_module_name =
                     (uu___114_10052.FStar_SMTEncoding_Env.current_module_name);
                   FStar_SMTEncoding_Env.encoding_quantifier =
                     (uu___114_10052.FStar_SMTEncoding_Env.encoding_quantifier)
                 }  in
               let f2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding]
                   env1.FStar_SMTEncoding_Env.tcenv f1
                  in
               let uu____10055 =
                 FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1  in
               (match uu____10055 with
                | (f3,decls) ->
                    let g =
                      let uu____10069 =
                        let uu____10070 =
                          let uu____10077 =
                            let uu____10078 =
                              let uu____10079 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____10079
                               in
                            FStar_Pervasives_Native.Some uu____10078  in
                          let uu____10080 =
                            FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f3, uu____10077, uu____10080)  in
                        FStar_SMTEncoding_Util.mkAssume uu____10070  in
                      [uu____10069]  in
                    ((FStar_List.append decls g), env1)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____10082) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____10094 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____10116 =
                       let uu____10119 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____10119.FStar_Syntax_Syntax.fv_name  in
                     uu____10116.FStar_Syntax_Syntax.v  in
                   let uu____10120 =
                     let uu____10121 =
                       FStar_TypeChecker_Env.try_lookup_val_decl
                         env1.FStar_SMTEncoding_Env.tcenv lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____10121  in
                   if uu____10120
                   then
                     let val_decl =
                       let uu___115_10151 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___115_10151.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___115_10151.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___115_10151.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____10152 = encode_sigelt' env1 val_decl  in
                     match uu____10152 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____10094 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____10186,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____10188;
                          FStar_Syntax_Syntax.lbtyp = uu____10189;
                          FStar_Syntax_Syntax.lbeff = uu____10190;
                          FStar_Syntax_Syntax.lbdef = uu____10191;
                          FStar_Syntax_Syntax.lbattrs = uu____10192;
                          FStar_Syntax_Syntax.lbpos = uu____10193;_}::[]),uu____10194)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____10211 =
            FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
              (Prims.parse_int "1")
             in
          (match uu____10211 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____10240 =
                   let uu____10243 =
                     let uu____10244 =
                       let uu____10251 =
                         let uu____10252 =
                           FStar_Syntax_Syntax.range_of_fv b2t1  in
                         let uu____10253 =
                           let uu____10264 =
                             let uu____10265 =
                               let uu____10270 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____10270)  in
                             FStar_SMTEncoding_Util.mkEq uu____10265  in
                           ([[b2t_x]], [xx], uu____10264)  in
                         FStar_SMTEncoding_Term.mkForall uu____10252
                           uu____10253
                          in
                       (uu____10251,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____10244  in
                   [uu____10243]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____10240
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____10291,uu____10292) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___98_10301  ->
                  match uu___98_10301 with
                  | FStar_Syntax_Syntax.Discriminator uu____10302 -> true
                  | uu____10303 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____10304,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____10315 =
                     let uu____10316 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____10316.FStar_Ident.idText  in
                   uu____10315 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___99_10320  ->
                     match uu___99_10320 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____10321 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____10323) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___100_10334  ->
                  match uu___100_10334 with
                  | FStar_Syntax_Syntax.Projector uu____10335 -> true
                  | uu____10340 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____10343 = FStar_SMTEncoding_Env.try_lookup_free_var env l
             in
          (match uu____10343 with
           | FStar_Pervasives_Native.Some uu____10350 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___116_10352 = se  in
                 let uu____10353 = FStar_Ident.range_of_lid l  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____10353;
                   FStar_Syntax_Syntax.sigquals =
                     (uu___116_10352.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___116_10352.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___116_10352.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____10356) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10368) ->
          let uu____10377 = encode_sigelts env ses  in
          (match uu____10377 with
           | (g,env1) ->
               let uu____10394 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___101_10417  ->
                         match uu___101_10417 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____10418;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____10419;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____10420;_}
                             -> false
                         | uu____10423 -> true))
                  in
               (match uu____10394 with
                | (g',inversions) ->
                    let uu____10438 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___102_10459  ->
                              match uu___102_10459 with
                              | FStar_SMTEncoding_Term.DeclFun uu____10460 ->
                                  true
                              | uu____10471 -> false))
                       in
                    (match uu____10438 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____10487,tps,k,uu____10490,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___103_10507  ->
                    match uu___103_10507 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____10508 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____10519 = c  in
              match uu____10519 with
              | (name,args,uu____10524,uu____10525,uu____10526) ->
                  let uu____10531 =
                    let uu____10532 =
                      let uu____10543 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____10566  ->
                                match uu____10566 with
                                | (uu____10573,sort,uu____10575) -> sort))
                         in
                      (name, uu____10543, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____10532  in
                  [uu____10531]
            else
              (let uu____10579 = FStar_Ident.range_of_lid t  in
               FStar_SMTEncoding_Term.constructor_to_decl uu____10579 c)
             in
          let inversion_axioms tapp vars =
            let uu____10605 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____10611 =
                        FStar_TypeChecker_Env.try_lookup_lid
                          env.FStar_SMTEncoding_Env.tcenv l
                         in
                      FStar_All.pipe_right uu____10611 FStar_Option.isNone))
               in
            if uu____10605
            then []
            else
              (let uu____10643 =
                 FStar_SMTEncoding_Env.fresh_fvar "x"
                   FStar_SMTEncoding_Term.Term_sort
                  in
               match uu____10643 with
               | (xxsym,xx) ->
                   let uu____10652 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____10691  ->
                             fun l  ->
                               match uu____10691 with
                               | (out,decls) ->
                                   let uu____10711 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.FStar_SMTEncoding_Env.tcenv l
                                      in
                                   (match uu____10711 with
                                    | (uu____10722,data_t) ->
                                        let uu____10724 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____10724 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____10762 =
                                                 let uu____10763 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____10763.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____10762 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____10766,indices) ->
                                                   indices
                                               | uu____10788 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____10812  ->
                                                         match uu____10812
                                                         with
                                                         | (x,uu____10818) ->
                                                             let uu____10819
                                                               =
                                                               let uu____10820
                                                                 =
                                                                 let uu____10827
                                                                   =
                                                                   FStar_SMTEncoding_Env.mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____10827,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____10820
                                                                in
                                                             FStar_SMTEncoding_Env.push_term_var
                                                               env1 x
                                                               uu____10819)
                                                    env)
                                                in
                                             let uu____10830 =
                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                 indices env1
                                                in
                                             (match uu____10830 with
                                              | (indices1,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____10856 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____10872
                                                                 =
                                                                 let uu____10877
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____10877,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____10872)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____10856
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____10880 =
                                                      let uu____10881 =
                                                        let uu____10886 =
                                                          let uu____10887 =
                                                            let uu____10892 =
                                                              FStar_SMTEncoding_Env.mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____10892,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____10887
                                                           in
                                                        (out, uu____10886)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____10881
                                                       in
                                                    (uu____10880,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____10652 with
                    | (data_ax,decls) ->
                        let uu____10905 =
                          FStar_SMTEncoding_Env.fresh_fvar "f"
                            FStar_SMTEncoding_Term.Fuel_sort
                           in
                        (match uu____10905 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____10916 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____10916 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____10920 =
                                 let uu____10927 =
                                   let uu____10928 =
                                     FStar_Ident.range_of_lid t  in
                                   let uu____10929 =
                                     let uu____10940 =
                                       FStar_SMTEncoding_Env.add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____10949 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____10940,
                                       uu____10949)
                                      in
                                   FStar_SMTEncoding_Term.mkForall
                                     uu____10928 uu____10929
                                    in
                                 let uu____10958 =
                                   FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____10927,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____10958)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____10920
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____10959 =
            let uu____10964 =
              let uu____10965 = FStar_Syntax_Subst.compress k  in
              uu____10965.FStar_Syntax_Syntax.n  in
            match uu____10964 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____10994 -> (tps, k)  in
          (match uu____10959 with
           | (formals,res) ->
               let uu____11001 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____11001 with
                | (formals1,res1) ->
                    let uu____11012 =
                      FStar_SMTEncoding_EncodeTerm.encode_binders
                        FStar_Pervasives_Native.None formals1 env
                       in
                    (match uu____11012 with
                     | (vars,guards,env',binder_decls,uu____11037) ->
                         let arity = FStar_List.length vars  in
                         let uu____11051 =
                           FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                             env t arity
                            in
                         (match uu____11051 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____11074 =
                                  let uu____11081 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____11081)  in
                                FStar_SMTEncoding_Util.mkApp uu____11074  in
                              let uu____11086 =
                                let tname_decl =
                                  let uu____11096 =
                                    let uu____11097 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____11121  ->
                                              match uu____11121 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____11134 =
                                      FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                        ()
                                       in
                                    (tname, uu____11097,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____11134, false)
                                     in
                                  constructor_or_logic_type_decl uu____11096
                                   in
                                let uu____11137 =
                                  match vars with
                                  | [] ->
                                      let uu____11150 =
                                        let uu____11151 =
                                          let uu____11154 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_19  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_19) uu____11154
                                           in
                                        FStar_SMTEncoding_Env.push_free_var
                                          env1 t arity tname uu____11151
                                         in
                                      ([], uu____11150)
                                  | uu____11165 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____11172 =
                                          FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                            ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____11172
                                         in
                                      let ttok_app =
                                        FStar_SMTEncoding_EncodeTerm.mk_Apply
                                          ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____11186 =
                                          let uu____11193 =
                                            let uu____11194 =
                                              FStar_Ident.range_of_lid t  in
                                            let uu____11195 =
                                              let uu____11210 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____11210)
                                               in
                                            FStar_SMTEncoding_Term.mkForall'
                                              uu____11194 uu____11195
                                             in
                                          (uu____11193,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____11186
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____11137 with
                                | (tok_decls,env2) ->
                                    let uu____11231 =
                                      FStar_Ident.lid_equals t
                                        FStar_Parser_Const.lex_t_lid
                                       in
                                    if uu____11231
                                    then (tok_decls, env2)
                                    else
                                      ((FStar_List.append tname_decl
                                          tok_decls), env2)
                                 in
                              (match uu____11086 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____11256 =
                                       FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____11256 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____11274 =
                                               let uu____11275 =
                                                 let uu____11282 =
                                                   let uu____11283 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____11283
                                                    in
                                                 (uu____11282,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11275
                                                in
                                             [uu____11274]
                                           else []  in
                                         let uu____11285 =
                                           let uu____11288 =
                                             let uu____11291 =
                                               let uu____11292 =
                                                 let uu____11299 =
                                                   let uu____11300 =
                                                     FStar_Ident.range_of_lid
                                                       t
                                                      in
                                                   let uu____11301 =
                                                     let uu____11312 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____11312)
                                                      in
                                                   FStar_SMTEncoding_Term.mkForall
                                                     uu____11300 uu____11301
                                                    in
                                                 (uu____11299,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____11292
                                                in
                                             [uu____11291]  in
                                           FStar_List.append karr uu____11288
                                            in
                                         FStar_List.append decls1 uu____11285
                                      in
                                   let aux =
                                     let uu____11324 =
                                       let uu____11327 =
                                         inversion_axioms tapp vars  in
                                       let uu____11330 =
                                         let uu____11333 =
                                           let uu____11334 =
                                             FStar_Ident.range_of_lid t  in
                                           pretype_axiom uu____11334 env2
                                             tapp vars
                                            in
                                         [uu____11333]  in
                                       FStar_List.append uu____11327
                                         uu____11330
                                        in
                                     FStar_List.append kindingAx uu____11324
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11339,uu____11340,uu____11341,uu____11342,uu____11343)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11349,t,uu____11351,n_tps,uu____11353) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____11361 = FStar_Syntax_Util.arrow_formals t  in
          (match uu____11361 with
           | (formals,t_res) ->
               let arity = FStar_List.length formals  in
               let uu____11401 =
                 FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
                   d arity
                  in
               (match uu____11401 with
                | (ddconstrsym,ddtok,env1) ->
                    let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])
                       in
                    let uu____11422 =
                      FStar_SMTEncoding_Env.fresh_fvar "f"
                        FStar_SMTEncoding_Term.Fuel_sort
                       in
                    (match uu____11422 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11436 =
                           FStar_SMTEncoding_EncodeTerm.encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____11436 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____11506 =
                                            FStar_SMTEncoding_Env.mk_term_projector_name
                                              d x
                                             in
                                          (uu____11506,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____11510 =
                                  let uu____11511 =
                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                      ()
                                     in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____11511, true)
                                   in
                                let uu____11514 =
                                  let uu____11521 =
                                    FStar_Ident.range_of_lid d  in
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                    uu____11521
                                   in
                                FStar_All.pipe_right uu____11510 uu____11514
                                 in
                              let app =
                                FStar_SMTEncoding_EncodeTerm.mk_Apply
                                  ddtok_tm vars
                                 in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars
                                 in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars)
                                 in
                              let uu____11532 =
                                FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                  FStar_Pervasives_Native.None t env1
                                  ddtok_tm
                                 in
                              (match uu____11532 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____11544::uu____11545 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort)
                                            in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff
                                            in
                                         let vtok_app_l =
                                           FStar_SMTEncoding_EncodeTerm.mk_Apply
                                             ddtok_tm [ff]
                                            in
                                         let vtok_app_r =
                                           FStar_SMTEncoding_EncodeTerm.mk_Apply
                                             f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)]
                                            in
                                         let uu____11590 =
                                           FStar_Ident.range_of_lid d  in
                                         let uu____11591 =
                                           let uu____11602 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____11602)
                                            in
                                         FStar_SMTEncoding_Term.mkForall
                                           uu____11590 uu____11591
                                     | uu____11621 -> tok_typing  in
                                   let uu____11630 =
                                     FStar_SMTEncoding_EncodeTerm.encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____11630 with
                                    | (vars',guards',env'',decls_formals,uu____11655)
                                        ->
                                        let uu____11668 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars'
                                             in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1)
                                             in
                                          FStar_SMTEncoding_EncodeTerm.encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1
                                           in
                                        (match uu____11668 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11695 ->
                                                   let uu____11702 =
                                                     let uu____11703 =
                                                       FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id
                                                         ()
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____11703
                                                      in
                                                   [uu____11702]
                                                in
                                             let encode_elim uu____11717 =
                                               let uu____11718 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11718 with
                                               | (head1,args) ->
                                                   let uu____11763 =
                                                     let uu____11764 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____11764.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11763 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____11776;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____11777;_},uu____11778)
                                                        ->
                                                        let uu____11783 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____11783
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____11798
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____11798
                                                              with
                                                              | (encoded_args,arg_decls)
                                                                  ->
                                                                  let guards_for_parameter
                                                                    orig_arg
                                                                    arg xv =
                                                                    let fv1 =
                                                                    match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                    | 
                                                                    uu____11849
                                                                    ->
                                                                    let uu____11850
                                                                    =
                                                                    let uu____11855
                                                                    =
                                                                    let uu____11856
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____11856
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____11855)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____11850
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____11872
                                                                    =
                                                                    let uu____11873
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____11873
                                                                     in
                                                                    if
                                                                    uu____11872
                                                                    then
                                                                    let uu____11886
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____11886]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____11888
                                                                    =
                                                                    let uu____11901
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____11951
                                                                     ->
                                                                    fun
                                                                    uu____11952
                                                                     ->
                                                                    match 
                                                                    (uu____11951,
                                                                    uu____11952)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12047
                                                                    =
                                                                    let uu____12054
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12054
                                                                     in
                                                                    (match uu____12047
                                                                    with
                                                                    | 
                                                                    (uu____12067,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12075
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12075
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12077
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12077
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____11901
                                                                     in
                                                                  (match uu____11888
                                                                   with
                                                                   | 
                                                                   (uu____12094,arg_vars,elim_eqns_or_guards,uu____12097)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                    let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
                                                                    arg_vars1
                                                                     in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____12121
                                                                    =
                                                                    let uu____12128
                                                                    =
                                                                    let uu____12129
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12130
                                                                    =
                                                                    let uu____12141
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12142
                                                                    =
                                                                    let uu____12143
                                                                    =
                                                                    let uu____12148
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12148)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12143
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12141,
                                                                    uu____12142)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12129
                                                                    uu____12130
                                                                     in
                                                                    (uu____12128,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12121
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____12159
                                                                    =
                                                                    let uu____12164
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____12164,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____12159
                                                                     in
                                                                    let uu____12165
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12165
                                                                    then
                                                                    let x =
                                                                    let uu____12171
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12171,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12173
                                                                    =
                                                                    let uu____12180
                                                                    =
                                                                    let uu____12181
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12182
                                                                    =
                                                                    let uu____12193
                                                                    =
                                                                    let uu____12198
                                                                    =
                                                                    let uu____12201
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12201]
                                                                     in
                                                                    [uu____12198]
                                                                     in
                                                                    let uu____12206
                                                                    =
                                                                    let uu____12207
                                                                    =
                                                                    let uu____12212
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12213
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12212,
                                                                    uu____12213)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12207
                                                                     in
                                                                    (uu____12193,
                                                                    [x],
                                                                    uu____12206)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12181
                                                                    uu____12182
                                                                     in
                                                                    let uu____12226
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12180,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12226)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12173
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12231
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____12263
                                                                    =
                                                                    let uu____12264
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____12264
                                                                    dapp1  in
                                                                    [uu____12263])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12231
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12271
                                                                    =
                                                                    let uu____12278
                                                                    =
                                                                    let uu____12279
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12280
                                                                    =
                                                                    let uu____12291
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12292
                                                                    =
                                                                    let uu____12293
                                                                    =
                                                                    let uu____12298
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12298)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12293
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12291,
                                                                    uu____12292)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12279
                                                                    uu____12280
                                                                     in
                                                                    (uu____12278,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12271)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let uu____12312 =
                                                          FStar_SMTEncoding_Env.lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        (match uu____12312
                                                         with
                                                         | (encoded_head,encoded_head_arity)
                                                             ->
                                                             let uu____12327
                                                               =
                                                               FStar_SMTEncoding_EncodeTerm.encode_args
                                                                 args env'
                                                                in
                                                             (match uu____12327
                                                              with
                                                              | (encoded_args,arg_decls)
                                                                  ->
                                                                  let guards_for_parameter
                                                                    orig_arg
                                                                    arg xv =
                                                                    let fv1 =
                                                                    match 
                                                                    arg.FStar_SMTEncoding_Term.tm
                                                                    with
                                                                    | 
                                                                    FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                    | 
                                                                    uu____12378
                                                                    ->
                                                                    let uu____12379
                                                                    =
                                                                    let uu____12384
                                                                    =
                                                                    let uu____12385
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____12385
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____12384)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____12379
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                     in
                                                                    let guards1
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    guards
                                                                    (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____12401
                                                                    =
                                                                    let uu____12402
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____12402
                                                                     in
                                                                    if
                                                                    uu____12401
                                                                    then
                                                                    let uu____12415
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____12415]
                                                                    else []))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    guards1
                                                                     in
                                                                  let uu____12417
                                                                    =
                                                                    let uu____12430
                                                                    =
                                                                    FStar_List.zip
                                                                    args
                                                                    encoded_args
                                                                     in
                                                                    FStar_List.fold_left
                                                                    (fun
                                                                    uu____12480
                                                                     ->
                                                                    fun
                                                                    uu____12481
                                                                     ->
                                                                    match 
                                                                    (uu____12480,
                                                                    uu____12481)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____12576
                                                                    =
                                                                    let uu____12583
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_SMTEncoding_Env.gen_term_var
                                                                    env2
                                                                    uu____12583
                                                                     in
                                                                    (match uu____12576
                                                                    with
                                                                    | 
                                                                    (uu____12596,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____12604
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____12604
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____12606
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____12606
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                    (env',
                                                                    [], [],
                                                                    (Prims.parse_int "0"))
                                                                    uu____12430
                                                                     in
                                                                  (match uu____12417
                                                                   with
                                                                   | 
                                                                   (uu____12623,arg_vars,elim_eqns_or_guards,uu____12626)
                                                                    ->
                                                                    let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                    let ty =
                                                                    FStar_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                                                                    (FStar_SMTEncoding_Term.Var
                                                                    encoded_head)
                                                                    encoded_head_arity
                                                                    arg_vars1
                                                                     in
                                                                    let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    let dapp1
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                    let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                    let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu____12650
                                                                    =
                                                                    let uu____12657
                                                                    =
                                                                    let uu____12658
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12659
                                                                    =
                                                                    let uu____12670
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12671
                                                                    =
                                                                    let uu____12672
                                                                    =
                                                                    let uu____12677
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____12677)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12672
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12670,
                                                                    uu____12671)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12658
                                                                    uu____12659
                                                                     in
                                                                    (uu____12657,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12650
                                                                     in
                                                                    let subterm_ordering
                                                                    =
                                                                    let lex_t1
                                                                    =
                                                                    let uu____12688
                                                                    =
                                                                    let uu____12693
                                                                    =
                                                                    FStar_Ident.text_of_lid
                                                                    FStar_Parser_Const.lex_t_lid
                                                                     in
                                                                    (uu____12693,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    uu____12688
                                                                     in
                                                                    let uu____12694
                                                                    =
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                     in
                                                                    if
                                                                    uu____12694
                                                                    then
                                                                    let x =
                                                                    let uu____12700
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh
                                                                    "x"  in
                                                                    (uu____12700,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____12702
                                                                    =
                                                                    let uu____12709
                                                                    =
                                                                    let uu____12710
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12711
                                                                    =
                                                                    let uu____12722
                                                                    =
                                                                    let uu____12727
                                                                    =
                                                                    let uu____12730
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____12730]
                                                                     in
                                                                    [uu____12727]
                                                                     in
                                                                    let uu____12735
                                                                    =
                                                                    let uu____12736
                                                                    =
                                                                    let uu____12741
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____12742
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____12741,
                                                                    uu____12742)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12736
                                                                     in
                                                                    (uu____12722,
                                                                    [x],
                                                                    uu____12735)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12710
                                                                    uu____12711
                                                                     in
                                                                    let uu____12755
                                                                    =
                                                                    FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____12709,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____12755)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12702
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____12760
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____12792
                                                                    =
                                                                    let uu____12793
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    lex_t1
                                                                    lex_t1
                                                                    uu____12793
                                                                    dapp1  in
                                                                    [uu____12792])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____12760
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____12800
                                                                    =
                                                                    let uu____12807
                                                                    =
                                                                    let uu____12808
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12809
                                                                    =
                                                                    let uu____12820
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____12821
                                                                    =
                                                                    let uu____12822
                                                                    =
                                                                    let uu____12827
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____12827)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12822
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____12820,
                                                                    uu____12821)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12808
                                                                    uu____12809
                                                                     in
                                                                    (uu____12807,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12800)
                                                                     in
                                                                    (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering]))))
                                                    | uu____12840 ->
                                                        ((let uu____12842 =
                                                            let uu____12847 =
                                                              let uu____12848
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____12849
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____12848
                                                                uu____12849
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____12847)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____12842);
                                                         ([], [])))
                                                in
                                             let uu____12854 = encode_elim ()
                                                in
                                             (match uu____12854 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____12880 =
                                                      let uu____12883 =
                                                        let uu____12886 =
                                                          let uu____12889 =
                                                            let uu____12892 =
                                                              let uu____12893
                                                                =
                                                                let uu____12904
                                                                  =
                                                                  let uu____12905
                                                                    =
                                                                    let uu____12906
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____12906
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____12905
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____12904)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____12893
                                                               in
                                                            [uu____12892]  in
                                                          let uu____12909 =
                                                            let uu____12912 =
                                                              let uu____12915
                                                                =
                                                                let uu____12918
                                                                  =
                                                                  let uu____12921
                                                                    =
                                                                    let uu____12924
                                                                    =
                                                                    let uu____12927
                                                                    =
                                                                    let uu____12928
                                                                    =
                                                                    let uu____12935
                                                                    =
                                                                    let uu____12936
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12937
                                                                    =
                                                                    let uu____12948
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____12948)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12936
                                                                    uu____12937
                                                                     in
                                                                    (uu____12935,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12928
                                                                     in
                                                                    let uu____12957
                                                                    =
                                                                    let uu____12960
                                                                    =
                                                                    let uu____12961
                                                                    =
                                                                    let uu____12968
                                                                    =
                                                                    let uu____12969
                                                                    =
                                                                    FStar_Ident.range_of_lid
                                                                    d  in
                                                                    let uu____12970
                                                                    =
                                                                    let uu____12981
                                                                    =
                                                                    FStar_SMTEncoding_Env.add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____12982
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____12981,
                                                                    uu____12982)
                                                                     in
                                                                    FStar_SMTEncoding_Term.mkForall
                                                                    uu____12969
                                                                    uu____12970
                                                                     in
                                                                    (uu____12968,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12961
                                                                     in
                                                                    [uu____12960]
                                                                     in
                                                                    uu____12927
                                                                    ::
                                                                    uu____12957
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____12924
                                                                     in
                                                                  FStar_List.append
                                                                    uu____12921
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____12918
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____12915
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____12912
                                                             in
                                                          FStar_List.append
                                                            uu____12889
                                                            uu____12909
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____12886
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____12883
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____12880
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and (encode_sigelts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____13016  ->
              fun se  ->
                match uu____13016 with
                | (g,env1) ->
                    let uu____13036 = encode_sigelt env1 se  in
                    (match uu____13036 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____13101 =
        match uu____13101 with
        | (i,decls,env1) ->
            (match b with
             | FStar_Syntax_Syntax.Binding_univ uu____13133 ->
                 ((i + (Prims.parse_int "1")), decls, env1)
             | FStar_Syntax_Syntax.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses]
                     env1.FStar_SMTEncoding_Env.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____13139 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          env1.FStar_SMTEncoding_Env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____13139
                   then
                     let uu____13140 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____13141 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____13142 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____13140 uu____13141 uu____13142
                   else ());
                  (let uu____13144 =
                     FStar_SMTEncoding_EncodeTerm.encode_term t1 env1  in
                   match uu____13144 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____13160 =
                         let uu____13167 =
                           let uu____13168 =
                             let uu____13169 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____13169
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____13168  in
                         FStar_SMTEncoding_Env.new_term_constant_from_string
                           env1 x uu____13167
                          in
                       (match uu____13160 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____13183 = FStar_Options.log_queries ()
                                 in
                              if uu____13183
                              then
                                let uu____13184 =
                                  let uu____13185 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____13186 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____13187 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____13185 uu____13186 uu____13187
                                   in
                                FStar_Pervasives_Native.Some uu____13184
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax])
                               in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_Syntax_Syntax.Binding_lid (x,(uu____13199,t)) ->
                 let t_norm = FStar_SMTEncoding_EncodeTerm.whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____13219 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____13219 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____13242 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____13242 with | (uu____13265,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____13278 'Auu____13279 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____13278,'Auu____13279)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____13348  ->
              match uu____13348 with
              | (l,uu____13360,uu____13361) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____13405  ->
              match uu____13405 with
              | (l,uu____13419,uu____13420) ->
                  let uu____13429 =
                    FStar_All.pipe_left
                      (fun _0_20  -> FStar_SMTEncoding_Term.Echo _0_20)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____13430 =
                    let uu____13433 =
                      let uu____13434 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____13434  in
                    [uu____13433]  in
                  uu____13429 :: uu____13430))
       in
    (prefix1, suffix)
  
let (last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    let uu____13461 =
      let uu____13464 =
        let uu____13465 = FStar_Util.psmap_empty ()  in
        let uu____13480 = FStar_Util.psmap_empty ()  in
        let uu____13483 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____13486 =
          let uu____13487 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____13487 FStar_Ident.string_of_lid  in
        {
          FStar_SMTEncoding_Env.bvar_bindings = uu____13465;
          FStar_SMTEncoding_Env.fvar_bindings = uu____13480;
          FStar_SMTEncoding_Env.depth = (Prims.parse_int "0");
          FStar_SMTEncoding_Env.tcenv = tcenv;
          FStar_SMTEncoding_Env.warn = true;
          FStar_SMTEncoding_Env.cache = uu____13483;
          FStar_SMTEncoding_Env.nolabels = false;
          FStar_SMTEncoding_Env.use_zfuel_name = false;
          FStar_SMTEncoding_Env.encode_non_total_function_typ = true;
          FStar_SMTEncoding_Env.current_module_name = uu____13486;
          FStar_SMTEncoding_Env.encoding_quantifier = false
        }  in
      [uu____13464]  in
    FStar_ST.op_Colon_Equals last_env uu____13461
  
let (get_env :
  FStar_Ident.lident ->
    FStar_TypeChecker_Env.env -> FStar_SMTEncoding_Env.env_t)
  =
  fun cmn  ->
    fun tcenv  ->
      let uu____13525 = FStar_ST.op_Bang last_env  in
      match uu____13525 with
      | [] -> failwith "No env; call init first!"
      | e::uu____13556 ->
          let uu___117_13559 = e  in
          let uu____13560 = FStar_Ident.string_of_lid cmn  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___117_13559.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___117_13559.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___117_13559.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv = tcenv;
            FStar_SMTEncoding_Env.warn =
              (uu___117_13559.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache =
              (uu___117_13559.FStar_SMTEncoding_Env.cache);
            FStar_SMTEncoding_Env.nolabels =
              (uu___117_13559.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___117_13559.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___117_13559.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name = uu____13560;
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___117_13559.FStar_SMTEncoding_Env.encoding_quantifier)
          }
  
let (set_env : FStar_SMTEncoding_Env.env_t -> unit) =
  fun env  ->
    let uu____13566 = FStar_ST.op_Bang last_env  in
    match uu____13566 with
    | [] -> failwith "Empty env stack"
    | uu____13596::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : unit -> unit) =
  fun uu____13631  ->
    let uu____13632 = FStar_ST.op_Bang last_env  in
    match uu____13632 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let top =
          let uu___118_13667 = hd1  in
          let uu____13668 =
            FStar_Util.smap_copy hd1.FStar_SMTEncoding_Env.cache  in
          {
            FStar_SMTEncoding_Env.bvar_bindings =
              (uu___118_13667.FStar_SMTEncoding_Env.bvar_bindings);
            FStar_SMTEncoding_Env.fvar_bindings =
              (uu___118_13667.FStar_SMTEncoding_Env.fvar_bindings);
            FStar_SMTEncoding_Env.depth =
              (uu___118_13667.FStar_SMTEncoding_Env.depth);
            FStar_SMTEncoding_Env.tcenv =
              (uu___118_13667.FStar_SMTEncoding_Env.tcenv);
            FStar_SMTEncoding_Env.warn =
              (uu___118_13667.FStar_SMTEncoding_Env.warn);
            FStar_SMTEncoding_Env.cache = uu____13668;
            FStar_SMTEncoding_Env.nolabels =
              (uu___118_13667.FStar_SMTEncoding_Env.nolabels);
            FStar_SMTEncoding_Env.use_zfuel_name =
              (uu___118_13667.FStar_SMTEncoding_Env.use_zfuel_name);
            FStar_SMTEncoding_Env.encode_non_total_function_typ =
              (uu___118_13667.FStar_SMTEncoding_Env.encode_non_total_function_typ);
            FStar_SMTEncoding_Env.current_module_name =
              (uu___118_13667.FStar_SMTEncoding_Env.current_module_name);
            FStar_SMTEncoding_Env.encoding_quantifier =
              (uu___118_13667.FStar_SMTEncoding_Env.encoding_quantifier)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : unit -> unit) =
  fun uu____13702  ->
    let uu____13703 = FStar_ST.op_Bang last_env  in
    match uu____13703 with
    | [] -> failwith "Popping an empty stack"
    | uu____13733::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (snapshot_env : unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2)
  = fun uu____13772  -> FStar_Common.snapshot push_env last_env () 
let (rollback_env : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_env last_env depth 
let (init : FStar_TypeChecker_Env.env -> unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (snapshot :
  Prims.string ->
    (FStar_TypeChecker_Env.solver_depth_t,unit)
      FStar_Pervasives_Native.tuple2)
  =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____13815  ->
         let uu____13816 = snapshot_env ()  in
         match uu____13816 with
         | (env_depth,()) ->
             let uu____13832 =
               FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ()
                in
             (match uu____13832 with
              | (varops_depth,()) ->
                  let uu____13848 = FStar_SMTEncoding_Z3.snapshot msg  in
                  (match uu____13848 with
                   | (z3_depth,()) ->
                       ((env_depth, varops_depth, z3_depth), ()))))
  
let (rollback :
  Prims.string ->
    FStar_TypeChecker_Env.solver_depth_t FStar_Pervasives_Native.option ->
      unit)
  =
  fun msg  ->
    fun depth  ->
      FStar_Util.atomically
        (fun uu____13891  ->
           let uu____13892 =
             match depth with
             | FStar_Pervasives_Native.Some (s1,s2,s3) ->
                 ((FStar_Pervasives_Native.Some s1),
                   (FStar_Pervasives_Native.Some s2),
                   (FStar_Pervasives_Native.Some s3))
             | FStar_Pervasives_Native.None  ->
                 (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None,
                   FStar_Pervasives_Native.None)
              in
           match uu____13892 with
           | (env_depth,varops_depth,z3_depth) ->
               (rollback_env env_depth;
                FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback
                  varops_depth;
                FStar_SMTEncoding_Z3.rollback msg z3_depth))
  
let (push : Prims.string -> unit) =
  fun msg  -> let uu____13954 = snapshot msg  in () 
let (pop : Prims.string -> unit) =
  fun msg  -> rollback msg FStar_Pervasives_Native.None 
let (open_fact_db_tags :
  FStar_SMTEncoding_Env.env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  = fun env  -> [] 
let (place_decl_in_fact_dbs :
  FStar_SMTEncoding_Env.env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____13995::uu____13996,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___119_14004 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___119_14004.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___119_14004.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___119_14004.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____14005 -> d
  
let (fact_dbs_for_lid :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list)
  =
  fun env  ->
    fun lid  ->
      let uu____14024 =
        let uu____14027 =
          let uu____14028 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____14028  in
        let uu____14029 = open_fact_db_tags env  in uu____14027 ::
          uu____14029
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____14024
  
let (encode_top_level_facts :
  FStar_SMTEncoding_Env.env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Env.env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____14055 = encode_sigelt env se  in
      match uu____14055 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____14099 = FStar_Options.log_queries ()  in
        if uu____14099
        then
          let uu____14102 =
            let uu____14103 =
              let uu____14104 =
                let uu____14105 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____14105 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____14104  in
            FStar_SMTEncoding_Term.Caption uu____14103  in
          uu____14102 :: decls
        else decls  in
      (let uu____14116 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14116
       then
         let uu____14117 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____14117
       else ());
      (let env =
         let uu____14120 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____14120 tcenv  in
       let uu____14121 = encode_top_level_facts env se  in
       match uu____14121 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____14135 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____14135)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> unit) =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____14151 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14151
       then
         let uu____14152 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____14152
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____14193  ->
                 fun se  ->
                   match uu____14193 with
                   | (g,env2) ->
                       let uu____14213 = encode_top_level_facts env2 se  in
                       (match uu____14213 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____14236 =
         encode_signature
           (let uu___120_14245 = env  in
            {
              FStar_SMTEncoding_Env.bvar_bindings =
                (uu___120_14245.FStar_SMTEncoding_Env.bvar_bindings);
              FStar_SMTEncoding_Env.fvar_bindings =
                (uu___120_14245.FStar_SMTEncoding_Env.fvar_bindings);
              FStar_SMTEncoding_Env.depth =
                (uu___120_14245.FStar_SMTEncoding_Env.depth);
              FStar_SMTEncoding_Env.tcenv =
                (uu___120_14245.FStar_SMTEncoding_Env.tcenv);
              FStar_SMTEncoding_Env.warn = false;
              FStar_SMTEncoding_Env.cache =
                (uu___120_14245.FStar_SMTEncoding_Env.cache);
              FStar_SMTEncoding_Env.nolabels =
                (uu___120_14245.FStar_SMTEncoding_Env.nolabels);
              FStar_SMTEncoding_Env.use_zfuel_name =
                (uu___120_14245.FStar_SMTEncoding_Env.use_zfuel_name);
              FStar_SMTEncoding_Env.encode_non_total_function_typ =
                (uu___120_14245.FStar_SMTEncoding_Env.encode_non_total_function_typ);
              FStar_SMTEncoding_Env.current_module_name =
                (uu___120_14245.FStar_SMTEncoding_Env.current_module_name);
              FStar_SMTEncoding_Env.encoding_quantifier =
                (uu___120_14245.FStar_SMTEncoding_Env.encoding_quantifier)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____14236 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____14264 = FStar_Options.log_queries ()  in
             if uu____14264
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___121_14272 = env1  in
               {
                 FStar_SMTEncoding_Env.bvar_bindings =
                   (uu___121_14272.FStar_SMTEncoding_Env.bvar_bindings);
                 FStar_SMTEncoding_Env.fvar_bindings =
                   (uu___121_14272.FStar_SMTEncoding_Env.fvar_bindings);
                 FStar_SMTEncoding_Env.depth =
                   (uu___121_14272.FStar_SMTEncoding_Env.depth);
                 FStar_SMTEncoding_Env.tcenv =
                   (uu___121_14272.FStar_SMTEncoding_Env.tcenv);
                 FStar_SMTEncoding_Env.warn = true;
                 FStar_SMTEncoding_Env.cache =
                   (uu___121_14272.FStar_SMTEncoding_Env.cache);
                 FStar_SMTEncoding_Env.nolabels =
                   (uu___121_14272.FStar_SMTEncoding_Env.nolabels);
                 FStar_SMTEncoding_Env.use_zfuel_name =
                   (uu___121_14272.FStar_SMTEncoding_Env.use_zfuel_name);
                 FStar_SMTEncoding_Env.encode_non_total_function_typ =
                   (uu___121_14272.FStar_SMTEncoding_Env.encode_non_total_function_typ);
                 FStar_SMTEncoding_Env.current_module_name =
                   (uu___121_14272.FStar_SMTEncoding_Env.current_module_name);
                 FStar_SMTEncoding_Env.encoding_quantifier =
                   (uu___121_14272.FStar_SMTEncoding_Env.encoding_quantifier)
               });
            (let uu____14274 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____14274
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let (encode_query :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____14332 =
           let uu____14333 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____14333.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____14332);
        (let env =
           let uu____14335 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____14335 tcenv  in
         let uu____14336 =
           let rec aux bindings =
             match bindings with
             | (FStar_Syntax_Syntax.Binding_var x)::rest ->
                 let uu____14375 = aux rest  in
                 (match uu____14375 with
                  | (out,rest1) ->
                      let t =
                        let uu____14403 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____14403 with
                        | FStar_Pervasives_Native.Some uu____14406 ->
                            let uu____14407 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____14407
                              x.FStar_Syntax_Syntax.sort
                        | uu____14408 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.FStar_SMTEncoding_Env.tcenv t
                         in
                      let uu____14412 =
                        let uu____14415 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___122_14418 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___122_14418.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___122_14418.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____14415 :: out  in
                      (uu____14412, rest1))
             | uu____14423 -> ([], bindings)  in
           let uu____14430 = aux tcenv.FStar_TypeChecker_Env.gamma  in
           match uu____14430 with
           | (closing,bindings) ->
               let uu____14457 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____14457, bindings)
            in
         match uu____14336 with
         | (q1,bindings) ->
             let uu____14488 = encode_env_bindings env bindings  in
             (match uu____14488 with
              | (env_decls,env1) ->
                  ((let uu____14510 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery"))
                       in
                    if uu____14510
                    then
                      let uu____14511 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____14511
                    else ());
                   (let uu____14513 =
                      FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1  in
                    match uu____14513 with
                    | (phi,qdecls) ->
                        let uu____14534 =
                          let uu____14539 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____14539 phi
                           in
                        (match uu____14534 with
                         | (labels,phi1) ->
                             let uu____14556 = encode_labels labels  in
                             (match uu____14556 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____14593 =
                                      let uu____14600 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____14601 =
                                        FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique
                                          "@query"
                                         in
                                      (uu____14600,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____14601)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14593
                                     in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"])
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  