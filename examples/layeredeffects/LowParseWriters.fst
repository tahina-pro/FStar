(*
   Copyright 2019 Microsoft Research

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

module LowParseWriters


open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

inline_for_extraction
let read_repr_impl_direct
  (a:Type u#x)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (l: memory_invariant)
  (spec: read_repr_spec a pre post post_err)
: Tot Type0
= unit ->
  HST.Stack (result a)
  (requires (fun h ->
    B.modifies l.lwrite l.h0 h /\
    HS.get_tip l.h0 `HS.includes` HS.get_tip h /\
    pre
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    begin match spec () with
      | Correct r -> res == Correct r
      | Error _ -> Error? res
    end
  ))

inline_for_extraction
let read_repr_impl_cps
  (a:Type u#x)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (l: memory_invariant)
  (spec: read_repr_spec a pre post post_err)
: Tot Type
= (h0: HS.mem {B.modifies l.lwrite l.h0 h0 /\ HS.get_tip l.h0 `HS.includes` HS.get_tip h0 }) ->
  (hpost: (a -> HS.mem -> GTot Type0)) ->
  (hpost_err: (HS.mem -> GTot Type0)) ->
  (((r: a) -> HST.Stack unit
    (requires (fun h ->
      B.modifies B.loc_none h0 h /\
      HS.get_tip h0 `HS.includes` HS.get_tip h /\
      pre /\
      spec () == Correct r
    ))
    (ensures (fun _ _ h -> hpost r h))
  )) ->
  ((s: string) -> HST.Stack unit
    (requires (fun h ->
      B.modifies B.loc_none h0 h /\
      HS.get_tip h0 `HS.includes` HS.get_tip h /\
      pre /\
      Error? (spec ())
    ))
    (ensures (fun _ _ h -> hpost_err h))
  ) ->
  HST.Stack unit
  (requires (fun h ->
    B.modifies B.loc_none h0 h /\
    HS.get_tip h0 `HS.includes` HS.get_tip h /\
    pre
  ))
  (ensures (fun _ _ h' ->
    match spec () with
    | Correct r -> hpost r h'
    | _ -> hpost_err h'
  ))

inline_for_extraction
let read_repr_impl_direct_to_cps
  (a:Type u#x)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (l: memory_invariant)
  (spec: read_repr_spec a pre post post_err)
  (impl: read_repr_impl_direct a pre post post_err l spec)
: Tot (read_repr_impl_cps a pre post post_err l spec)
= fun h0 hpost hpost_err k kerr ->
  match impl () with
  | Correct r -> k r
  | Error s -> kerr s

inline_for_extraction
let read_repr_impl_cps_to_direct
  (a:Type0)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (l: memory_invariant)
  (spec: read_repr_spec a pre post post_err)
  (impl: read_repr_impl_cps a pre post post_err l spec)
: Tot (read_repr_impl_direct a pre post post_err l spec)
= fun _ ->
  HST.push_frame ();
  let bres = B.alloca (Error "read_repr_impl_cps_to_direct" <: result a) 1ul in
  let h0 = HST.get () in
  impl
    h0
    (fun r h -> B.modifies (B.loc_buffer bres) h0 h /\ Seq.index (B.as_seq h bres) 0 == Correct r)
    (fun h -> B.modifies (B.loc_buffer bres) h0 h /\ Error? (Seq.index (B.as_seq h bres) 0))
    (fun r -> B.upd bres 0ul (Correct r))
    (fun s -> B.upd bres 0ul (Error s))
  ;
  let res = B.index bres 0ul in
  HST.pop_frame ();
  res

let read_repr_impl
  a pre post post_err l spec
=
  read_repr_impl_cps a pre post post_err l spec

let mk_read_repr_impl
  a pre post post_err l spec impl
=
  read_repr_impl_direct_to_cps _ _ _ _ _ _ impl

let extract_read_repr_impl
  a pre post post_err l spec impl
=
  read_repr_impl_cps_to_direct _ _ _ _ _ _ impl ()

let read_return_impl
  a x inv
= (fun _ _ _ k _ -> k x)

let read_bind_impl
  a b pre_f post_f post_err_f pre_g post_g post_err_g f_bind_impl g l f' g'
=
  fun h0 kpost kposterr k kerr ->
    f' h0 
      (fun x h ->
        pre_g x /\
        begin match g x () with | Correct y -> kpost y h | Error s -> kposterr h end
      )
      kposterr
      (fun x -> g' x h0 kpost kposterr k kerr) 
      kerr

let read_subcomp_impl
  a pre post post_err pre' post' post_err' l l' f_subcomp_spec f_subcomp sq
=
  fun h0 kpost k kposterr kerr ->
    f_subcomp h0 kpost k kposterr kerr

let lift_pure_read_impl
  a wp f_pure_spec_for_impl l
=
  fun h0 kpost kposterr k kerr -> k (f_pure_spec_for_impl ())

let failwith_impl
  a inv s
= fun h0 kpost k kposterr kerr -> kerr s

let buffer_index_impl
  #t inv b i
=
  fun h0 kpost kposterr k kerr -> k (B.index b i)

let buffer_sub_impl
  #t inv b i len
=
  fun h0 kpost kposterr k kerr -> k (B.sub b i len)

noeq
type rptr = {
  rptr_base: B.buffer U8.t;
  rptr_len: (rptr_len: U32.t { rptr_len == B.len rptr_base });
}

let valid_rptr
  p inv x
=
  inv.lwrite `B.loc_disjoint` B.loc_buffer x.rptr_base /\
  valid_buffer p inv.h0 x.rptr_base

let deref_spec
  #p #inv x
=
  buffer_contents p inv.h0 x.rptr_base

let mk_ptr
  p inv b len
= {
  rptr_base = b;
  rptr_len = len;
}

let buffer_of_ptr
  #p #inv x
=
  (x.rptr_base, x.rptr_len)

let valid_rptr_frame
  #p #inv x inv'
= valid_frame p inv.h0 x.rptr_base 0ul (B.len x.rptr_base) inv.lwrite inv'.h0

let deref_impl
  #p #inv r x
  h0 kpost kposterr k kerr
=
  let h = HST.get () in
  valid_frame p inv.h0 x.rptr_base 0ul (B.len x.rptr_base) inv.lwrite h;
  k (r x.rptr_base x.rptr_len)

let access_spec
  #p1 #p2 #lens #inv g x
=
  let y' = gaccess g inv.h0 x.rptr_base in
  { rptr_base = y'; rptr_len = B.len y' }

let access_impl
  #p1 #p2 #lens #inv #g a x
  h0 kpost kposterr k kerr
=
  let h = HST.get () in
  valid_frame p1 inv.h0 x.rptr_base 0ul (B.len x.rptr_base) inv.lwrite h;
  let (base', len') = baccess a x.rptr_base x.rptr_len in
  let h' = HST.get () in
  gaccessor_frame g inv.h0 x.rptr_base inv.lwrite h;
  gaccessor_frame g inv.h0 x.rptr_base inv.lwrite h';
  k ({ rptr_base = base'; rptr_len = len' })

let validate_spec
  p inv b
= fun _ ->
  match gvalidate p inv.h0 b with
  | None -> Error "validation failed"
  | Some pos ->
    let b' = B.gsub b 0ul pos in
    let x = { rptr_base = b' ; rptr_len = pos } in
    Correct (x, pos)

let valid_frame'
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (l: B.loc)
  (h' : HS.mem)
  (pos' : U32.t)
: Lemma
  ((
    B.live h b /\
    (valid_pos p h b pos pos' \/ valid_pos p h' b pos pos') /\
    B.modifies l h h' /\
    B.loc_disjoint l (B.loc_buffer_from_to b pos pos')
  ) ==> (
    valid_pos p h b pos pos' /\
    valid_pos p h' b pos pos' /\
    contents p h' b pos pos' == contents p h b pos pos'
  ))
= Classical.move_requires (valid_frame p h b pos pos' l) h'

let validate_impl
  #p v inv b len
  h0 kpost kposterr k kerr
=
  let h1 = HST.get () in
  Classical.forall_intro (valid_frame' p inv.h0 b 0ul inv.lwrite h1);
  gvalidate_frame p inv.h0 b inv.lwrite h1;
  let res = bvalidate v b len in
  let h2 = HST.get () in
  Classical.forall_intro (valid_frame' p inv.h0 b 0ul inv.lwrite h2);
  gvalidate_frame p inv.h0 b inv.lwrite h2;
  match res with
  | None -> kerr "validation failed"
  | Some pos ->
    let b' = B.sub b 0ul pos in
    let x = { rptr_base = b' ; rptr_len = pos } in
    k (x, pos)

inline_for_extraction
let repr_impl_direct
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post post_err)
: Tot Type0 =
  (b: B.buffer u8 { l.lwrite `B.loc_includes` B.loc_buffer b }) ->
  (len: U32.t { len == B.len b }) ->
  (pos1: buffer_offset b) ->
  HST.Stack (iresult a)
  (requires (fun h ->
    B.modifies l.lwrite l.h0 h /\
    HS.get_tip l.h0 `HS.includes` HS.get_tip h /\
    valid_pos r_in h b 0ul pos1 /\
    pre (contents r_in h b 0ul pos1)
  ))
  (ensures (fun h res h' ->
    repr_impl_post a r_in r_out pre post post_err l spec b pos1 h res h'
  ))

inline_for_extraction
let repr_impl_cps
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post post_err)
: Tot Type =
  (b: B.buffer u8 { l.lwrite `B.loc_includes` B.loc_buffer b }) ->
  (len: U32.t { len == B.len b }) ->
  (pos1: buffer_offset b) ->
  (h0: HS.mem {
    B.modifies l.lwrite l.h0 h0 /\
    HS.get_tip l.h0 `HS.includes` HS.get_tip h0 /\
    valid_pos r_in h0 b 0ul pos1 /\
    pre (contents r_in h0 b 0ul pos1)
  }) ->
  (hpost: (a -> Parser?.t r_out -> HS.mem -> GTot Type0)) ->
  (((r: a) -> (pos2: buffer_offset b) -> HST.Stack unit
    (requires (fun h ->
      HS.get_tip h0 `HS.includes` HS.get_tip h /\
      B.modifies (B.loc_buffer b) h0 h /\
      U32.v pos1 <= U32.v pos2 /\
      valid_pos r_out h b 0ul pos2 /\
      spec (contents r_in h0 b 0ul pos1) == Correct (r, contents r_out h b 0ul pos2)
    ))
    (ensures (fun h _ h' ->
      hpost r (contents r_out h b 0ul pos2) h'
    ))
  )) ->
  (hpost_overflow: (HS.mem -> GTot Type0)) ->
  (unit -> HST.Stack unit
    (requires (fun h ->
      HS.get_tip h0 `HS.includes` HS.get_tip h /\
      B.modifies (B.loc_buffer b) h0 h /\
      begin match spec (contents r_in h0 b 0ul pos1) with
      | Correct (r, v') -> size r_out v' > B.length b
      | _ -> True
      end
    ))
    (ensures (fun _ _ h -> hpost_overflow h))
  ) ->
  (hpost_err: (HS.mem -> GTot Type0)) ->
  ((s: string) -> HST.Stack unit
    (requires (fun h ->
      HS.get_tip h0 `HS.includes` HS.get_tip h /\
      B.modifies (B.loc_buffer b) h0 h /\
      Error? (spec (contents r_in h0 b 0ul pos1))
    ))
    (ensures (fun _ _ h -> hpost_err h))
  ) ->
  HST.Stack unit
  (requires (fun h ->
    B.modifies B.loc_none h0 h /\
    HS.get_tip h0 `HS.includes` HS.get_tip h
  ))
  (ensures (fun _ _ h' ->
    match spec (contents r_in h0 b 0ul pos1) with
    | Correct (r, v') ->
      if size r_out v' > B.length b
      then hpost_overflow h'
      else hpost r v' h'
    | _ -> hpost_overflow h' \/ hpost_err h'
  ))

inline_for_extraction
let repr_impl_direct_to_cps
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post post_err)
  (impl: repr_impl_direct a r_in r_out pre post post_err l spec)
: Tot (repr_impl_cps a r_in r_out pre post post_err l spec)
=
  fun b len pos1 
  h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  let h = HST.get () in
  valid_frame r_in h0 b 0ul pos1 B.loc_none h;
  match impl b len pos1 with
  | ICorrect v pos2 -> k v pos2
  | IOverflow -> koverflow ()
  | IError s -> kerr s

inline_for_extraction
let repr_impl_cps_to_direct
  (a:Type0)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post post_err)
  (impl: repr_impl_cps a r_in r_out pre post post_err l spec)
: Tot (repr_impl_direct a r_in r_out pre post post_err l spec)
=
  fun b len pos1 ->
  let h0 = HST.get () in
  HST.push_frame ();
  let bres = B.alloca (IError "repr_impl_cps_to_direct" <: iresult a) 1ul in
  let h1 = HST.get () in
  valid_frame r_in h0 b 0ul pos1 B.loc_none h1;
  impl
    b len pos1
    h1
    (fun r v' h ->
      B.modifies (B.loc_buffer b `B.loc_union` B.loc_buffer bres) h1 h /\
      begin match Seq.index (B.as_seq h bres) 0 with
      | ICorrect r' pos2 ->
        r == r' /\
        valid_pos r_out h b 0ul pos2 /\
        contents r_out h b 0ul pos2 == v'
      | _ -> False
      end
    )
    (fun r pos2 ->
      let h2 = HST.get () in
      B.upd bres 0ul (ICorrect r pos2);
      let h = HST.get () in
      valid_frame r_out h2 b 0ul pos2 (B.loc_buffer bres) h
    )
    (fun h -> B.modifies (B.loc_buffer b `B.loc_union` B.loc_buffer bres) h1 h /\ IOverflow? (Seq.index (B.as_seq h bres) 0))
    (fun s -> B.upd bres 0ul IOverflow)
    (fun h -> B.modifies (B.loc_buffer b `B.loc_union` B.loc_buffer bres) h1 h /\ IError? (Seq.index (B.as_seq h bres) 0))
    (fun s -> B.upd bres 0ul (IError s))
  ;
  let h3 = HST.get () in
  let res = B.index bres 0ul in
  HST.pop_frame ();
  let h4 = HST.get () in
  let f (pos2: U32.t) : Lemma
    (requires (valid_pos r_out h3 b 0ul pos2))
    (ensures (
      valid_pos r_out h3 b 0ul pos2 /\
      valid_pos r_out h4 b 0ul pos2 /\
      contents r_out h4 b 0ul pos2 == contents r_out h3 b 0ul pos2
    ))
  =
    valid_frame r_out h3 b 0ul pos2 (B.loc_all_regions_from false (HS.get_tip h1)) h4
  in
  Classical.forall_intro (Classical.move_requires f);
  res

let repr_impl = repr_impl_cps

let mk_repr_impl
  a r_in r_out pre post post_err l spec impl
=
  repr_impl_direct_to_cps _ _ _ _ _ _ _ _ impl

let extract_repr_impl
  a r_in r_out pre post post_err l spec impl
=
  repr_impl_cps_to_direct _ _ _ _ _ _ _ _ impl

inline_for_extraction
let return_impl
  a x r l
= fun b len pos1 
  h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  let h = HST.get () in
  valid_frame r h0 b 0ul pos1 B.loc_none h;
  k x pos1

inline_for_extraction
let bind_impl
  a b r_in_f r_out_f pre_f post_f post_err_f r_out_g pre_g post_g post_err_g f_bind_impl g l f' g'
= fun buf len pos 
  h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  f' buf len pos h0
    (fun x vg h' ->
      pre_g x vg /\
      begin match g x vg with
      | Correct (y, v') ->
        if size r_out_g v' > B.length buf
        then hpost_overflow h'
        else hpost y v' h'
      | Error s -> hpost_overflow h' \/ hpost_err h'
      end
    )
    (fun x posf -> let h1 = HST.get () in g' x buf len posf h1 hpost k hpost_overflow koverflow hpost_err kerr)
    hpost_overflow koverflow
    hpost_err kerr

inline_for_extraction
let subcomp_impl
  a r_in r_out pre post post_err pre' post' post_err' l l' f_subcomp_spec f_subcomp sq
: Tot (repr_impl a r_in r_out pre' post' post_err' l' (subcomp_spec a r_in r_out pre post post_err pre' post' post_err' f_subcomp_spec))
= fun b len pos
  h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  f_subcomp b len pos h0 hpost k hpost_overflow koverflow hpost_err kerr

(*
inline_for_extraction
let lift_pure_impl
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser) (f_pure_spec_for_impl:unit -> PURE a wp)
  (l: memory_invariant)
: Tot (repr_impl a r (fun _ -> r) (lift_pure_pre a wp r) (lift_pure_post a wp r) l (lift_pure_spec a wp r f_pure_spec_for_impl))
= fun buf len pos -> Some (f_pure_spec_for_impl (), pos)
*)

let lift_read_impl
  a pre post post_err inv r f_read_spec
= fun b len pos
  h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  let h = HST.get () in
  valid_frame r h0 b 0ul pos B.loc_none h;
  ReadRepr?.impl f_read_spec
    h
    (fun a h' -> hpost a (contents r h0 b 0ul pos) h')
    hpost_err
    (fun res ->
      let h' = HST.get () in
      valid_frame r h b 0ul pos B.loc_none h';
      k res pos
    )
    (fun s -> kerr s)

let wfailwith_impl
  a inv rin rout s
=
  fun b len pos
  h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  kerr s

let get_state_impl
  inv p
=
  fun b len pos
    h0 hpost k hpost_overflow koverflow hpost_err kerr ->
    let h = HST.get () in
    valid_frame p h0 b 0ul pos B.loc_none h;
    k (Ghost.hide (contents p h b 0ul pos)) pos

#push-options "--ifuel 8"

#restart-solver

inline_for_extraction
let frame_impl
  (a: Type)
  (frame: parser)
  (pre: pre_t parse_empty)
  (p: parser)
  (post: post_t a parse_empty p pre)
  (post_err: post_err_t parse_empty pre)
  (l: memory_invariant)
  (inner: unit -> EWrite a parse_empty p pre post post_err l)
: Tot (repr_impl a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) (frame_post_err frame pre post_err) l (frame_spec a frame pre p post post_err l inner))
= fun buf len pos
    h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  let h = HST.get () in
  valid_frame frame h0 buf 0ul pos B.loc_none h;
  let buf' = B.offset buf pos in
  destr_repr_impl a parse_empty p pre post post_err l inner buf' (len `U32.sub` pos) 0ul
    h 
    (fun x v' h' -> hpost x (contents frame h0 buf 0ul pos, v') h')
    (fun x wlen ->
      let h' = HST.get () in
      let pos' = pos `U32.add` wlen in
      B.loc_disjoint_loc_buffer_from_to buf 0ul pos pos (B.len buf');
      valid_frame frame h buf 0ul pos (B.loc_buffer buf') h';
      valid_parse_pair frame (p) h' buf 0ul pos pos' ;
      k x pos' )
    hpost_overflow koverflow
    hpost_err kerr

#pop-options

#push-options "--z3rlimit 128"

let elem_writer_impl
  #p w l x
=
  fun b len pos
    h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  let b' = B.offset b pos in
  match w b' (len `U32.sub` pos) x with
  | None -> koverflow ()
  | Some xlen -> k () (pos `U32.add` xlen)

inline_for_extraction
let recast_writer_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (f: unit -> EWrite a r_in r_out pre post post_err l)
: Tot (repr_impl a r_in r_out pre (recast_writer_post a r_in r_out pre post post_err l f) (recast_writer_post_err a r_in r_out pre post post_err l f) l (recast_writer_spec a r_in r_out pre post post_err l f))
= fun b len pos -> destr_repr_impl a r_in r_out pre post post_err l f b len pos

#restart-solver

#push-options "--ifuel 8"

inline_for_extraction
let frame2_impl
  a frame ppre pre p post post_err l inner
= fun buf len pos
    h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  let h = HST.get () in
  valid_frame (frame `parse_pair` ppre) h0 buf 0ul pos B.loc_none h;
  let pos2 = valid_parse_pair_inv frame ppre buf len 0ul pos in
  let buf' = B.offset buf pos2 in
  assert (valid_pos ppre h buf pos2 pos);
  assert (valid_pos ppre h buf' 0ul (pos `U32.sub` pos2));
  let h1 = HST.get () in
  valid_frame frame h buf 0ul pos2 B.loc_none h1;
  valid_frame ppre h buf' 0ul (pos `U32.sub` pos2) B.loc_none h1;
  destr_repr_impl a ppre p pre post post_err l inner buf' (len `U32.sub` pos2) (pos `U32.sub` pos2)
    h1
    (fun x v' h' -> hpost x (contents frame h buf 0ul pos2, v') h')
    (fun x wlen ->
      let h' = HST.get () in
      let pos' = pos2 `U32.add` wlen in
      B.loc_disjoint_loc_buffer_from_to buf 0ul pos2 pos2 (B.len buf');
      valid_frame frame h buf 0ul pos2 (B.loc_buffer buf') h';
      valid_parse_pair frame (p) h' buf 0ul pos2 pos' ;
      k x pos'
    )
    hpost_overflow koverflow
    hpost_err kerr

#pop-options

#pop-options

let valid_rewrite_impl
  p1 p2 precond f v inv
=
  fun buf len pos
    h0 hpost k hpost_overflow koverflow hpost_err kerr ->
    let h = HST.get () in
    valid_frame p1 h0 buf 0ul pos B.loc_none h;
    v.valid_rewrite_valid h buf 0ul pos;
    k () pos

let cast
  p1 p2 precond f v inv x1
=
  v.valid_rewrite_valid inv.h0 x1.rptr_base 0ul x1.rptr_len;
  x1

let check_precond_spec
  (p1: parser)
  (precond: pre_t p1)
: Tot (repr_spec unit p1 (p1) precond (fun vin _ vout -> vin == vout /\ precond vin) (fun vin -> ~ (precond vin)))
= fun vin ->
  if FStar.StrongExcludedMiddle.strong_excluded_middle (precond vin)
  then Correct ((), vin)
  else Error "check_precond failed"

inline_for_extraction
let check_precond_impl
  (p1: parser)
  (precond: pre_t p1)
  (c: check_precond_t p1 precond)
  (inv: memory_invariant)
: Tot (repr_impl unit p1 (p1) precond (fun vin _ vout -> vin == vout /\ precond vin) (fun vin -> ~ (precond vin)) inv (check_precond_spec p1 precond))
= fun b len pos
    h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  let h = HST.get () in
  valid_frame p1 h0 b 0ul pos B.loc_none h;
  if c b len 0ul pos
  then
    let h' = HST.get () in
    let _ = valid_frame p1 h b 0ul pos B.loc_none h' in
    k () pos
  else kerr "check_precond failed"

let check_precond_repr
  p1 precond c inv
= Repr _ (check_precond_impl p1 precond c inv)

let cat_impl
  #inv #p x
=
  fun b len _
    h0 hpost k hpost_overflow koverflow hpost_err kerr ->
  if len `U32.lt` x.rptr_len
  then
    koverflow ()
  else begin
    B.blit x.rptr_base 0ul b 0ul x.rptr_len;
    let h' = HST.get () in
    valid_ext p inv.h0 x.rptr_base 0ul x.rptr_len h' b 0ul x.rptr_len;
    k () x.rptr_len
  end
