(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"

module FStar.Tc.Recheck

open FStar
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Absyn.Util
open FStar.Util
open FStar.Absyn.Util


let oktype = Some ktype
let t_unit   = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.unit_lid   ktype)
let t_bool   = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.bool_lid   ktype)
let t_uint8  = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.uint8_lid  ktype)
let t_int    = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.int_lid    ktype)
let t_int32  = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.int32_lid  ktype)
let t_int64  = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.int64_lid  ktype)
let t_string = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.string_lid ktype)
let t_float  = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.float_lid  ktype)
let t_char   = syn dummyRange oktype <| mk_Typ_const (Util.withsort Const.char_lid   ktype)

let typing_const r (s:sconst) = match s with
  | Const_unit -> t_unit
  | Const_bool _ -> t_bool
  | Const_int _ -> t_int
  | Const_int32 _ -> t_int32
  | Const_int64 _ -> t_int64
  | Const_string _ -> t_string
  | Const_float _ -> t_float
  | Const_char _ -> t_char
  | Const_uint8 _ -> t_uint8
  | _ -> raise (Error("Unsupported constant", r))


let rec recompute_kind t =
    let recompute t = match t.n with
        | Typ_delayed _ -> recompute_kind (Util.compress_typ t)
        | Typ_btvar a -> a.sort
        | Typ_const tc -> tc.sort
        | Typ_fun _
        | Typ_refine _ -> ktype
        | Typ_ascribed (_, k)
        | Typ_uvar(_, k) -> k
        | Typ_meta(Meta_labeled _)
        | Typ_meta(Meta_slack_formula _)
        | Typ_meta(Meta_pattern _) -> ktype
        | Typ_meta(Meta_named(t, _)) -> recompute_kind t
        | Typ_meta(Meta_refresh_label(t, _, _)) -> recompute_kind t
        | Typ_lam(binders, body) -> mk_Kind_arrow(binders, recompute_kind body) t.pos
        | Typ_app(t1, args) ->
          begin match t1.n with
            | Typ_const tc when (lid_equals tc.v Const.forall_lid
                                || lid_equals tc.v Const.exists_lid
                                || lid_equals tc.v Const.allTyp_lid
                                || lid_equals tc.v Const.exTyp_lid) -> ktype
            | _ ->
              let k1 = recompute_kind t1 in
              let bs, k = Util.kind_formals k1 in
              let rec aux subst bs args = match bs, args with
                | [], [] -> Util.subst_kind subst k
                | _, [] -> (mk_Kind_arrow(bs, k) t.pos) |> Util.subst_kind subst
                | b::bs, a::args ->
                    let subst = Util.subst_formal b a :: subst in
                    aux subst bs args
                | _ -> failwith (Util.format4 "Head kind is %s\nToo many arguments in type %s; result kind is %s\nwith %s remaining args\n" (Print.kind_to_string k1) (Print.tag_of_typ t) (Print.kind_to_string k) (List.length args |> string_of_int)) in
              aux [] bs args
           end
        | Typ_unknown -> kun in
    match !t.tk with
        | Some k -> k
        | None -> let k = recompute t in t.tk := Some k; k

let rec recompute_typ (e:exp) : typ =
    let recompute e = match e.n with
        | Exp_delayed _ -> recompute_typ (Util.compress_exp e)
        | Exp_bvar x -> x.sort
        | Exp_fvar (f, _) -> f.sort
        | Exp_constant s -> typing_const e.pos s
        | Exp_abs(bs, body) -> mk_Typ_fun(bs, mk_Total (recompute_typ body)) None e.pos
        | Exp_app(head, args) ->
            let t1 = recompute_typ head in
            begin match Util.function_formals t1 with
                | None -> tun
                | Some (bs, c) ->
                  let rec aux subst bs args = match bs, args with
                    | [], [] -> Util.subst_typ subst (Util.comp_result c)
                    | _, [] -> (mk_Typ_fun(bs, c) None e.pos) |> Util.subst_typ subst
                    | b::bs, a::args ->
                        let subst = Util.subst_formal b a :: subst in
                        aux subst bs args
                    | _ -> failwith "Too many arguments" in
                  aux [] bs args
            end

       | Exp_match _ -> failwith "Expect match nodes to be annotated already"
       | Exp_ascribed(_, t, _) -> t
       | Exp_let(_, e) -> recompute_typ e
       | Exp_uvar(_, t) -> t
       | Exp_meta(Meta_desugared(e, _)) -> recompute_typ e in

    match !e.tk with
        | Some t -> t
        | None -> let t = recompute e in e.tk := Some t; t


type db = 
 | Var of int
 | Name of string
 | Abs of db * db
 | App of db * db
 | Binder of db * db

let rec db_to_string = function 
    | Var x -> "(Var " ^ string_of_int x ^ ")"
    | Name s -> "(Name " ^ s ^ ")"
    | Abs(t1, t2) -> "(Abs " ^ db_to_string t1 ^ " " ^ db_to_string t2 ^ ")"
    | App(t1, t2) -> "(App " ^ db_to_string t1 ^ " " ^ db_to_string t2 ^ ")"
    | Binder(t1, t2) -> "(Binder " ^ db_to_string t1 ^ " " ^ db_to_string t2 ^ ")"

let close x db = 
    let rec aux index db = match db with 
        | Name y when y=x -> Var index
        | Abs (db, db') -> Abs (aux index db, aux (index + 1) db')
        | Binder (db, db') -> Binder (aux index db, aux (index + 1) db')
        | App (db1, db2) -> App(aux index db1, aux index db2)
        | _ -> db in
    aux 0 db

let abs (x:string) (t:db) (body:db) = 
    Abs (t, close x body)

let binder (x:string) (t:db) (body:db) = 
    Binder (t, close x body)

let app head args = List.fold_left (fun h a -> App(h, a)) head args

let rec db_of_typ (t:typ) : db = match (unmeta_typ t).n with
 | Typ_btvar x -> Name (x.v.realname.idText)
 | Typ_const f -> Name (f.v.str)
 | Typ_fun([], c) -> failwith "Impossible"
 | Typ_fun([b], c) -> let x, t = db_of_binder b in binder x t (db_of_comp c)
 | Typ_fun(b::bs, c) -> db_of_typ (mk_Typ_fun([b], mk_Total (mk_Typ_fun(bs, c) None dummyRange)) None dummyRange)
 | Typ_refine(x, t) -> binder x.v.realname.idText (db_of_typ x.sort) (db_of_typ t)
 | Typ_app(t, []) -> failwith "Impossible"
 | Typ_app(t, [Inl s, _]) -> App(db_of_typ t, db_of_typ s)
 | Typ_app(t, [Inr s, _]) -> App(db_of_typ t, db_of_exp s)
 | Typ_app(t, s::args) -> db_of_typ (mk_Typ_app(mk_Typ_app(t, [s]) None dummyRange, args) None dummyRange)  
 | Typ_lam([], t) -> failwith "Impossible"
 | Typ_lam([b], t) -> let x, t0 = db_of_binder b in abs x t0 (db_of_typ t)
 | Typ_lam(b::bs, t) -> db_of_typ (mk_Typ_lam([b], mk_Typ_lam(bs, t) None dummyRange) None dummyRange)
 | Typ_uvar (u, _) -> Name "uvar"
 | Typ_ascribed _
 | Typ_meta    _
 | Typ_delayed _ 
 | Typ_unknown _ -> failwith "Impossbile"

and db_of_arg = function 
 | Inl t, _ -> db_of_typ t
 | Inr e, _ -> db_of_exp e

and db_of_comp (c:comp) : db = match c.n with 
 | Total t -> db_of_typ t
 | Comp c -> app (Name c.effect_name.str) (List.map db_of_arg ((Inl c.result_typ, None)::c.effect_args))

and db_of_binder (b, _) = match b with 
 | Inl a -> a.v.realname.idText, db_of_kind a.sort
 | Inr a -> a.v.realname.idText, db_of_typ a.sort

and db_of_kind k = match (compress_kind k).n with 
 | Kind_type -> Name "Type"
 | Kind_effect -> Name "Effect"
 | Kind_abbrev(_, k) -> db_of_kind k
 | Kind_arrow([], _) -> failwith "Imposssible"
 | Kind_arrow([b], k) -> let x, t = db_of_binder b in binder x t (db_of_kind k)
 | Kind_uvar _ -> Name "uvar"
 | _ -> Name "kind_const"
     
and db_of_exp e = match (compress_exp e).n with
 | Exp_bvar x -> Name x.v.realname.idText
 | Exp_fvar (f, _) -> Name f.v.str
 | Exp_constant s -> Name "constant"
 | _ -> Name "Some_exp"

let log = 
    let ts = System.DateTime.Now.ToString("yyyy-MM-dd-HH-mm-ss") in
    let f = FStar.Util.open_file_for_writing ("norm" ^ts^ ".log") in
    let logged_prims = ref false in 
    fun (env:Tc.Env.env) (t:typ) -> 
        if not !logged_prims && env.curmodule.str <> "Prims"
        then begin 
             let tab = List.hd env.sigtab in
             let mappings = Util.smap_fold tab (fun k v out -> match v with 
                    | Sig_typ_abbrev (lid, tps, _, t, quals, _)->
                      let t = Util.close_with_lam tps t in
                      let mapping = Printf.sprintf "%s -> %s" lid.str (db_of_typ t |> db_to_string) in
                      mapping::out
                    | _ -> out) [] in
             logged_prims := true;
             FStar.Util.append_to_file f (Printf.sprintf "Prims=[%s]" (String.concat "; " mappings))
        end;
        if env.curmodule.str <> "Prims"
        then FStar.Util.append_to_file f (db_of_typ t |> db_to_string)
    