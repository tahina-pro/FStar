open Prims
let disentangle_abbrevs_from_bundle:
  FStar_Syntax_Syntax.sigelt Prims.list ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lident Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple2
  =
  fun sigelts  ->
    fun quals  ->
      fun members  ->
        fun rng  ->
          let sigattrs =
            FStar_List.collect (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
              sigelts in
          let type_abbrev_sigelts =
            FStar_All.pipe_right sigelts
              (FStar_List.collect
                 (fun x  ->
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((false
                          ,{
                             FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                               uu____59;
                             FStar_Syntax_Syntax.lbunivs = uu____60;
                             FStar_Syntax_Syntax.lbtyp = uu____61;
                             FStar_Syntax_Syntax.lbeff = uu____62;
                             FStar_Syntax_Syntax.lbdef = uu____63;_}::[]),uu____64)
                        -> [x]
                    | FStar_Syntax_Syntax.Sig_let (uu____83,uu____84) ->
                        failwith
                          "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
                    | uu____91 -> [])) in
          match type_abbrev_sigelts with
          | [] ->
              ({
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle (sigelts, members));
                 FStar_Syntax_Syntax.sigrng = rng;
                 FStar_Syntax_Syntax.sigquals = quals;
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = sigattrs
               }, [])
          | uu____104 ->
              let type_abbrevs =
                FStar_All.pipe_right type_abbrev_sigelts
                  (FStar_List.map
                     (fun x  ->
                        match x.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_let
                            ((uu____123,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____125;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____126;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____127;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____128;_}::[]),uu____129)
                            ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____148 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible")) in
              let unfolded_type_abbrevs =
                let rev_unfolded_type_abbrevs = FStar_Util.mk_ref [] in
                let in_progress = FStar_Util.mk_ref [] in
                let not_unfolded_yet = FStar_Util.mk_ref type_abbrev_sigelts in
                let remove_not_unfolded lid =
                  let uu____177 =
                    let uu____180 = FStar_ST.op_Bang not_unfolded_yet in
                    FStar_All.pipe_right uu____180
                      (FStar_List.filter
                         (fun x  ->
                            match x.FStar_Syntax_Syntax.sigel with
                            | FStar_Syntax_Syntax.Sig_let
                                ((uu____260,{
                                              FStar_Syntax_Syntax.lbname =
                                                FStar_Util.Inr fv;
                                              FStar_Syntax_Syntax.lbunivs =
                                                uu____262;
                                              FStar_Syntax_Syntax.lbtyp =
                                                uu____263;
                                              FStar_Syntax_Syntax.lbeff =
                                                uu____264;
                                              FStar_Syntax_Syntax.lbdef =
                                                uu____265;_}::[]),uu____266)
                                ->
                                Prims.op_Negation
                                  (FStar_Ident.lid_equals lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                            | uu____285 -> true)) in
                  FStar_ST.op_Colon_Equals not_unfolded_yet uu____177 in
                let rec unfold_abbrev_fv t fv =
                  let replacee x =
                    match x.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_let
                        ((uu____368,{
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv';
                                      FStar_Syntax_Syntax.lbunivs = uu____370;
                                      FStar_Syntax_Syntax.lbtyp = uu____371;
                                      FStar_Syntax_Syntax.lbeff = uu____372;
                                      FStar_Syntax_Syntax.lbdef = uu____373;_}::[]),uu____374)
                        when
                        FStar_Ident.lid_equals
                          (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        -> FStar_Pervasives_Native.Some x
                    | uu____393 -> FStar_Pervasives_Native.None in
                  let replacee_term x =
                    match replacee x with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let
                            ((uu____406,{
                                          FStar_Syntax_Syntax.lbname =
                                            uu____407;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____408;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____409;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____410;
                                          FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____412);
                          FStar_Syntax_Syntax.sigrng = uu____413;
                          FStar_Syntax_Syntax.sigquals = uu____414;
                          FStar_Syntax_Syntax.sigmeta = uu____415;
                          FStar_Syntax_Syntax.sigattrs = uu____416;_}
                        -> FStar_Pervasives_Native.Some tm
                    | uu____445 -> FStar_Pervasives_Native.None in
                  let uu____450 =
                    let uu____455 =
                      FStar_ST.op_Bang rev_unfolded_type_abbrevs in
                    FStar_Util.find_map uu____455 replacee_term in
                  match uu____450 with
                  | FStar_Pervasives_Native.Some x -> x
                  | FStar_Pervasives_Native.None  ->
                      let uu____531 =
                        FStar_Util.find_map type_abbrev_sigelts replacee in
                      (match uu____531 with
                       | FStar_Pervasives_Native.Some se ->
                           let uu____535 =
                             let uu____536 = FStar_ST.op_Bang in_progress in
                             FStar_List.existsb
                               (fun x  ->
                                  FStar_Ident.lid_equals x
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                               uu____536 in
                           if uu____535
                           then
                             let msg =
                               FStar_Util.format1
                                 "Cycle on %s in mutually recursive type abbreviations"
                                 ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str in
                             FStar_Exn.raise
                               (FStar_Errors.Error
                                  (msg,
                                    (FStar_Ident.range_of_lid
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)))
                           else unfold_abbrev se
                       | uu____607 -> t)
                and unfold_abbrev x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____612)
                      ->
                      let quals1 =
                        FStar_All.pipe_right x.FStar_Syntax_Syntax.sigquals
                          (FStar_List.filter
                             (fun uu___266_633  ->
                                match uu___266_633 with
                                | FStar_Syntax_Syntax.Noeq  -> false
                                | uu____634 -> true)) in
                      let lid =
                        match lb.FStar_Syntax_Syntax.lbname with
                        | FStar_Util.Inr fv ->
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                        | uu____637 ->
                            failwith
                              "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible" in
                      ((let uu____643 =
                          let uu____646 = FStar_ST.op_Bang in_progress in lid
                            :: uu____646 in
                        FStar_ST.op_Colon_Equals in_progress uu____643);
                       (match () with
                        | () ->
                            (remove_not_unfolded lid;
                             (match () with
                              | () ->
                                  let ty' =
                                    FStar_Syntax_InstFV.inst unfold_abbrev_fv
                                      lb.FStar_Syntax_Syntax.lbtyp in
                                  let tm' =
                                    FStar_Syntax_InstFV.inst unfold_abbrev_fv
                                      lb.FStar_Syntax_Syntax.lbdef in
                                  let lb' =
                                    let uu___267_781 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___267_781.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___267_781.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp = ty';
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___267_781.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = tm'
                                    } in
                                  let sigelt' =
                                    FStar_Syntax_Syntax.Sig_let
                                      ((false, [lb']), [lid]) in
                                  ((let uu____794 =
                                      let uu____797 =
                                        FStar_ST.op_Bang
                                          rev_unfolded_type_abbrevs in
                                      (let uu___268_865 = x in
                                       {
                                         FStar_Syntax_Syntax.sigel = sigelt';
                                         FStar_Syntax_Syntax.sigrng =
                                           (uu___268_865.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           quals1;
                                         FStar_Syntax_Syntax.sigmeta =
                                           (uu___268_865.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (uu___268_865.FStar_Syntax_Syntax.sigattrs)
                                       }) :: uu____797 in
                                    FStar_ST.op_Colon_Equals
                                      rev_unfolded_type_abbrevs uu____794);
                                   (match () with
                                    | () ->
                                        ((let uu____931 =
                                            let uu____934 =
                                              FStar_ST.op_Bang in_progress in
                                            FStar_List.tl uu____934 in
                                          FStar_ST.op_Colon_Equals
                                            in_progress uu____931);
                                         (match () with | () -> tm'))))))))
                  | uu____1065 ->
                      failwith
                        "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible" in
                let rec aux uu____1071 =
                  let uu____1072 = FStar_ST.op_Bang not_unfolded_yet in
                  match uu____1072 with
                  | x::uu____1142 -> let _unused = unfold_abbrev x in aux ()
                  | uu____1146 ->
                      let uu____1149 =
                        FStar_ST.op_Bang rev_unfolded_type_abbrevs in
                      FStar_List.rev uu____1149 in
                aux () in
              let filter_out_type_abbrevs l =
                FStar_List.filter
                  (fun lid  ->
                     FStar_List.for_all
                       (fun lid'  ->
                          Prims.op_Negation (FStar_Ident.lid_equals lid lid'))
                       type_abbrevs) l in
              let inductives_with_abbrevs_unfolded =
                let find_in_unfolded fv =
                  FStar_Util.find_map unfolded_type_abbrevs
                    (fun x  ->
                       match x.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_let
                           ((uu____1256,{
                                          FStar_Syntax_Syntax.lbname =
                                            FStar_Util.Inr fv';
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____1258;
                                          FStar_Syntax_Syntax.lbtyp =
                                            uu____1259;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____1260;
                                          FStar_Syntax_Syntax.lbdef = tm;_}::[]),uu____1262)
                           when
                           FStar_Ident.lid_equals
                             (fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           -> FStar_Pervasives_Native.Some tm
                       | uu____1283 -> FStar_Pervasives_Native.None) in
                let unfold_fv t fv =
                  let uu____1293 = find_in_unfolded fv in
                  match uu____1293 with
                  | FStar_Pervasives_Native.Some t' -> t'
                  | uu____1303 -> t in
                let unfold_in_sig x =
                  match x.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid,univs1,bnd,ty,mut,dc) ->
                      let bnd' =
                        FStar_Syntax_InstFV.inst_binders unfold_fv bnd in
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___269_1336 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_inductive_typ
                               (lid, univs1, bnd', ty', mut', dc));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___269_1336.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___269_1336.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___269_1336.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___269_1336.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_datacon
                      (lid,univs1,ty,res,npars,mut) ->
                      let ty' = FStar_Syntax_InstFV.inst unfold_fv ty in
                      let mut' = filter_out_type_abbrevs mut in
                      [(let uu___270_1356 = x in
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_datacon
                               (lid, univs1, ty', res, npars, mut'));
                          FStar_Syntax_Syntax.sigrng =
                            (uu___270_1356.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (uu___270_1356.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___270_1356.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___270_1356.FStar_Syntax_Syntax.sigattrs)
                        })]
                  | FStar_Syntax_Syntax.Sig_let (uu____1359,uu____1360) -> []
                  | uu____1365 ->
                      failwith
                        "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible" in
                FStar_List.collect unfold_in_sig sigelts in
              let new_members = filter_out_type_abbrevs members in
              let new_bundle =
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_bundle
                       (inductives_with_abbrevs_unfolded, new_members));
                  FStar_Syntax_Syntax.sigrng = rng;
                  FStar_Syntax_Syntax.sigquals = quals;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = sigattrs
                } in
              (new_bundle, unfolded_type_abbrevs)