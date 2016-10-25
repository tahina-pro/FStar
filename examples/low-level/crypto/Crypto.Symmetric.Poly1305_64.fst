(* Implementation of Poly1305 based on the rfc7539 *)
module Crypto.Symmetric.Poly1305_64

open FStar.Mul
open FStar.Ghost
open FStar.Seq
(** Machine integers *)
open FStar.UInt8
open FStar.UInt64
open FStar.Int.Cast
(** Effects and memory layout *)
open FStar.HyperStack
(** Buffers *)
open FStar.Buffer
(** Mathematical definitions *)
open FStar.Math.Lemmas
(** Helper functions for buffers *)
open Buffer.Utils
open Crypto.Symmetric.Bytes

open FStar.Buffer.Quantifiers

open Hacl.Symmetric.Poly1305_64.Parameters
open Hacl.Symmetric.Poly1305_64.Bigint
open Hacl.Symmetric.Poly1305_64.FC.Spec
open Hacl.Symmetric.Poly1305_64.FC
open Flag

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module H8   = Hacl.UInt8
module H64  = Hacl.UInt64
module H128 = Hacl.UInt128
module HS  = FStar.HyperStack


#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 20"

// we may separate field operations, so that we don't
// need to open the bignum modules elsewhere

(* * *********************************************)
(* *            Representation type              *)
(* * *********************************************)

(** Mutable big integer representation (5 64-bit limbs) *)
let elemB = elemB

(** Concrete (mutable) representation of words *)
let wordB : Type0 = if mac_log then b:uint8_p{length b <= 16} else wordB
let wordB_16 : Type0 = if mac_log then b:uint8_p{length b == 16} else wordB_16

let word : Type0 = if mac_log then seq U8.t else seq H8.t
(* let bytes : Type0 = if mac_log then Buffer.buffer U8.t else uint8_p *)

(* * *********************************************)
(* *  Mappings from stateful types to pure types *)
(* * *********************************************)

let live h (b:wordB) = if mac_log then live #U8.t h b else live #H8.t h b

(** From the current memory state, returns the word corresponding to a wordB *)
val sel_word: h:mem -> b:wordB{live h b} -> GTot word
let sel_word h b = sel_word h b

(** Only used when mac_log is true *)
private val _read_word:
  len:u32 ->
  b:wordB{mac_log /\ length #U8.t b == U32.v len} ->
  s:seq byte ->
  i:u32{U32.v i <= U32.v len} ->
  ST word
    (requires (fun h -> live h b /\ Seq.slice (sel_word h b) 0 (U32.v i) == s))
    (ensures  (fun h0 s h1 -> h0 == h1 /\ live h1 b /\ s == sel_word h1 b))
let rec _read_word len b s i =
  let h = ST.get () in
  if U32.v i = U32.v len then
    begin
    Seq.lemma_eq_intro s (sel_word h b);
    s
    end
  else
    begin
    let x = b.(i) in
    let s' = FStar.Seq (s @| Seq.create 1 x) in
    Seq.lemma_eq_intro s' (Seq.slice (sel_word h b) 0 (U32.v i + 1));
    _read_word len b s' (U32 (i +^ 1ul))
    end

val read_word: len:u32 -> b:wordB{mac_log /\ length #U8.t b == U32.v len} -> ST word
  (requires (fun h0 -> live h0 b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 b /\ r == (sel_word h1 b)))
let read_word len b =
  let h = ST.get() in
  let s0 = Seq.createEmpty #byte in
  Seq.lemma_eq_intro s0 (Seq.slice (sel_word h b) 0 0);
  _read_word len b s0 0ul

(** From the current memory state, returns the field element corresponding to a elemB *)
val sel_elem: h:mem -> b:elemB{live h b} -> GTot elem
let sel_elem h b = sel_elem h b

(** From the current memory state, returns the integer corresponding to a elemB, (before
   computing the modulo) *)
val sel_int: h:mem -> b:elemB{live h b} -> GTot nat
let sel_int h b = sel_int h b


(* * ******************************************** *)
(* *        Polynomial computation step           *)
(* * ******************************************** *)

(* Initialization function:
   - clamps the first half of the key
   - stores the well-formatted first half of the key in 'r' *)

let log_t = if mac_log then Seq.seq elem else log_t


val poly1305_encode_r:
  r:bigint ->
  key:uint8_p{length key = 16} ->
  Stack unit
    (requires (fun h -> live h r /\ live h key /\ disjoint key r))
    (ensures  (fun h0 _ h1 -> modifies_1 r h0 h1 /\ live h1 r
      // TODO: function correctness
      ))
let poly1305_encode_r r key =
  poly1305_encode_r r key


val poly1305_encode_b:
  b:bigint ->
  m:wordB_16 ->
  Stack unit
    (requires (fun h -> live h b /\ live h m /\ disjoint #H64.t #byte b m))
    (ensures  (fun h0 _ h1 -> modifies_1 b h0 h1 /\ live h1 b))
let poly1305_encode_b b m =
  poly1305_encode_b b m


val poly1305_init:
  st:poly1305_state ->
  key:uint8_p{length key >= 32 /\ disjoint st.r key} ->
  Stack log_t
    (requires (fun h -> live_st h st /\ live h key))
    (ensures  (fun h0 log h1 -> live_st h0 st /\ live h0 key
      (* /\ norm h1 r /\ live h1 s *)
      (* /\ (if mac_log then modifies_2 #H64.t #U8.t r s h0 h1 else modifies_2 #H64.t #H8.t r s h0 h1) *)
      /\ sel_int h1 st.r == Spec.clamp (sel_word h0 (sub key 0ul 16ul))))
let poly1305_init st key =
  poly1305_init st key


(* val poly1305_start: acc:elemB -> Stack unit *)
(*   (requires (fun h -> live h acc)) *)
(*   (ensures  (fun h0 _ h1 -> modifies_1 acc h0 h1 *)
(*     /\ norm h1 acc *)
(*     /\ sel_elem h1 acc == 0)) *)
(* let poly1305_start a = zeroB a *)


(**
   Update function:
   - takes a ghost log
   - takes a message block, appends '1' to it and formats it to bigint format
   - runs acc = ((acc*block)+r) % p
   *)

//CF note the log now consists of elem
//CF we'll need a simpler, field-only update---not the one below.

val seq_head_snoc: #a:Type -> xs:Seq.seq a -> x:a ->
  Lemma (Seq.length (SeqProperties.snoc xs x) > 0 /\
         seq_head (SeqProperties.snoc xs x) == xs)
let seq_head_snoc #a xs x =
  Seq.lemma_len_append xs (Seq.create 1 x);
  Seq.lemma_eq_intro (seq_head (SeqProperties.snoc xs x)) xs

(* let log_t: Type0 = if mac_log then text else unit *)

val ilog: l:log_t{mac_log} -> Tot text
let ilog l = l

val poly1305_update:
  current_log:log_t ->
  msg:wordB_16 ->
  st:poly1305_state{
    if mac_log then (disjoint #U8.t msg st.h /\ disjoint #U8.t msg st.r)
    else (disjoint #H8.t msg st.h /\ disjoint #H8.t msg st.r)} ->
  (* acc:elemB{if mac_log then disjoint #U8.t msg acc else disjoint #H8.t msg acc} ->  *)
  (* r:elemB{if mac_log then disjoint #U8.t msg r else disjoint #H8.t msg r /\ disjoint acc r} ->  *)
  Stack log_t
  (requires (fun h -> live h msg /\ norm h st.h /\ norm h st.r
    /\ (mac_log ==> sel_elem h (st.h) == poly (ilog current_log) (sel_elem h (st.r))) ))
  (ensures (fun h0 updated_log h1 -> live h1 msg /\ norm h1 (st.h) /\ norm h1 (st.r)
    /\ norm h0 (st.r)
    /\ modifies_1 st.h h0 h1
    /\ (mac_log ==>
         ilog updated_log == SeqProperties.snoc (ilog current_log) (encode (sel_word h1 msg))
       /\ sel_elem h1 st.h == poly (ilog updated_log) (sel_elem h0 st.r)) ))

let elem : Type0 = if mac_log then elem else erased elem

open FStar.SeqProperties

(* let seq_bytes = if mac_log then Seq.seq U8.t else Seq.seq H8.t *)

let rec little_endian (b:Seq.seq byte) : Tot (n:nat) (decreases (Seq.length b)) =
  if Seq.length b = 0 then 0
  else
    UInt8.v (head b) + pow2 8 * little_endian (tail b)

let encode (w:word) : Tot elem =
  if mac_log
    then (let l = Seq.length #U8.t w in
          pow2_le_compat 128 (8*l);
          pow2 (8 * l) +@ little_endian w)
    else elift1 (fun w -> encode w) w

#set-options "--z3timeout 60 --initial_fuel 1 --max_fuel 1"

let poly1305_update log msgB st =
  let m0 = ST.get () in
  push_frame();
  let r0 = st.r.(0ul) in
  let r1 = st.r.(1ul) in
  let r2 = st.r.(2ul) in
  let five = Hacl.Cast.uint64_to_sint64 5uL in
  let s1 = H64 (r1 *^ (five <<^ 2ul)) in
  let s2 = H64 (r2 *^ (five <<^ 2ul)) in
  let l = poly1305_update log st msgB r0 r1 r2 s1 s2 in
  let updated_log:log_t =
    if mac_log then
      begin
      let msg = read_word 16ul msgB in
      (* assert (encode msg == sel_elem h1 block); *)
      seq_head_snoc (ilog log) (encode msg);
      Seq.lemma_index_app2 (ilog log) (Seq.create 1 (encode msg)) (Seq.length (SeqProperties.snoc (ilog log) (encode msg)) - 1);
      SeqProperties.snoc (ilog log) (encode msg)
      end
    else l in
  pop_frame();
  let m3 = ST.get () in
  (* eval_eq_lemma h2 h3 (st.h) (st.h) Hacl.Symmetric.Poly1305_64.Parameters.norm_length; *)
  assert (norm m3 st.h);
  assert (modifies_1 st.h m0 m3);
  updated_log


#set-options "--z3timeout 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val append_as_seq_sub: h:HyperStack.mem -> n:UInt32.t -> m:UInt32.t -> msg:uint8_p{live h msg /\ U32.v m <= U32.v n /\ U32.v n <= length msg} -> Lemma
  (append (as_seq h (Buffer.sub msg 0ul m))
          (as_seq h (Buffer.sub (Buffer.offset msg m) 0ul (U32 (n -^ m)))) ==
   as_seq h (Buffer.sub msg 0ul n))
let append_as_seq_sub h n m msg =
  Seq.lemma_eq_intro
    (append (as_seq h (Buffer.sub msg 0ul m))
            (as_seq h (Buffer.sub (Buffer.offset msg m) 0ul (U32 (n -^ m)))))
     (as_seq h (Buffer.sub msg 0ul n))

(* Loop over Poly1305_update; could go below MAC *)
val poly1305_loop:
  current_log:log_t ->
  msg:uint8_p ->
  (* acc:elemB{disjoint msg acc} -> *)
  (* r:elemB{disjoint msg r /\ disjoint acc r} -> *)
  st:poly1305_state ->
  ctr:u32{length msg >= 16 * U32.v ctr} ->
  ST log_t
  (requires (fun h -> live h msg /\ norm h st.h /\ norm h st.r /\
      (mac_log ==>
        sel_elem h st.h == poly (ilog current_log) (sel_elem h st.r)) ))
  (ensures (fun h0 updated_log h1 -> live h0 msg /\ norm h1 st.h /\ norm h0 st.r /\
      modifies_1 st.h h0 h1 /\
      (mac_log ==>
        (ilog updated_log ==
        encode_pad (ilog current_log) (as_seq h0 (Buffer.sub msg 0ul (UInt32.mul 16ul ctr))) /\
        sel_elem h1 st.h == poly (ilog updated_log) (sel_elem h0 st.r))) ))
    (decreases (U32.v ctr))
#set-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let rec poly1305_loop log msg st ctr =
  if mac_log then (
    let h0 = ST.get() in
    if U32.lte ctr 0ul then
      begin
        encode_pad_empty (ilog log) (as_seq h0 (Buffer.sub msg 0ul 0ul));
        log
      end
    else
      begin
        let msg0:wordB_16 = Buffer.sub msg 0ul 16ul in
        let log1 = poly1305_update log msg0 st in
        let h1 = ST.get () in
        let msg1 = Buffer.offset msg 16ul in
        eval_eq_lemma h0 h1 st.r st.r norm_length;
        assert (live h1 msg1 /\ norm h1 st.h /\ norm h1 st.r);
        assert (mac_log ==> sel_elem h1 st.h == poly (ilog log1) (sel_elem h0 st.r));
        assert (mac_log ==>
          ilog log1 == SeqProperties.snoc (ilog log) (encode (sel_word h1 msg0)));
        let log2 = poly1305_loop log1 msg1 st (U32 (ctr -^ 1ul)) in
        let h2 = ST.get () in
        assert (norm h2 st.h /\ modifies_1 st.h h0 h2);
        lemma_modifies_1_trans st.h h0 h1 h2;
        if mac_log then
          begin
          //assert (ilog log2 ==
          //  encode_pad (ilog log1)
          //    (as_seq h0 (Buffer.sub msg1 0ul (UInt32.mul 16ul (ctr -| 1ul)))) );
          //assert (encode_pad (ilog log1)
          //  (as_seq h0 (Buffer.sub msg1 0ul (UInt32.mul 16ul (ctr -| 1ul)))) ==
          //encode_pad (SeqProperties.snoc (ilog log) (encode (sel_word h1 msg0)))
          //  (as_seq h0 (Buffer.sub (Buffer.offset msg 16ul) 0ul (UInt32.mul 16ul ctr -| 16ul))));
          encode_pad_snoc (ilog log) (as_seq h0 (Buffer.sub (Buffer.offset msg 16ul) 0ul (U32 (16ul *^ ctr -^ 16ul)))) (sel_word h1 msg0);
          append_as_seq_sub h0 (UInt32.mul 16ul ctr) 16ul msg
          //assert (append (sel_word h1 msg0) (as_seq h0 (Buffer.sub (Buffer.offset msg 16ul) 0ul  (UInt32.mul 16ul ctr -| 16ul))) ==
          // (as_seq h0 (Buffer.sub msg 0ul (UInt32.mul 16ul ctr))))
          end;
        log2
      end)
  else poly1305_blocks_loop log st msg

(**
   Performs the last step if there is an incomplete block
   NB: Not relevant for AEAD-ChachaPoly which only uses complete blocks of 16 bytes, hence
   only the 'update' and 'loop' functions are necessary there
*)
val poly1305_last:
  current_log:log_t ->
  msg:wordB ->
  (* acc:elemB{disjoint msg acc} -> *)
  (* r:elemB{disjoint msg r /\ disjoint acc r} ->  *)
  st:poly1305_state ->
  len:u32{U32.v len == (if mac_log then length #U8.t msg else length #H8.t msg)
    /\ 0 < U32.v len /\ U32.v len < 16} ->
  Stack log_t
    (requires (fun h -> live h msg /\ norm h st.h /\ norm h st.r
      /\ (mac_log ==> sel_elem h st.h == poly (ilog current_log) (sel_elem h st.r)) ))
    (ensures (fun h0 updated_log h1 -> live h1 msg /\ norm h1 st.h /\ norm h1 st.r
      /\ norm h0 st.r
      /\ modifies_1 st.h h0 h1
      /\ (mac_log ==>
           ilog updated_log == SeqProperties.snoc (ilog current_log) (encode (sel_word h1 msg))
         /\ sel_elem h1 st.h == poly (ilog updated_log) (sel_elem h0 st.r)) ))

#set-options "--z3timeout 60 --initial_fuel 1 --max_fuel 1"

let poly1305_last log msg st len =
  let m0 = ST.get() in
  let log = poly1305_last log st msg (Int.Cast.uint32_to_uint64 len) in
  let updated_log:log_t =
    if mac_log then
      begin
      let msg = read_word len msg in
      (* assert (encode msg == sel_elem h1 block); *)
      seq_head_snoc (ilog log) (encode msg);
      Seq.lemma_index_app2 (ilog log) (Seq.create 1 (encode msg)) (Seq.length (SeqProperties.snoc (ilog log) (encode msg)) - 1);
      SeqProperties.snoc (ilog log) (encode msg)
      end
    else () in
  pop_frame ();
  let m3 = ST.get() in
  (* eval_eq_lemma h2 h3 acc acc Parameters.norm_length; *)
  assert (norm m3 st.h);
  assert (modifies_1 st.h m0 m3);
  updated_log


(* (\* TODO: certainly a more efficient, better implementation of that *\) *)
(* private val add_word: a:wordB_16 -> b:wordB_16 -> Stack unit *)
(*   (requires (fun h -> live h a /\ live h b)) *)
(*   (ensures  (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h1 a /\ modifies_1 a h0 h1 /\ *)
(*      little_endian (sel_word h1 a) == *)
(*      (little_endian (sel_word h0 a) + little_endian (sel_word h0 b)) % pow2 128 )) *)
(* let add_word a b = *)
(*   let carry = 0ul in *)
(*   let a04:u64 = let (x:u32) = uint32_of_bytes a in uint32_to_uint64 x  in *)
(*   let a48:u64 = let (x:u32) = uint32_of_bytes (offset a 4ul) in uint32_to_uint64 x in *)
(*   let a812:u64 = let (x:u32) = uint32_of_bytes (offset a 8ul) in uint32_to_uint64 x in *)
(*   let a1216:u64 = let (x:u32) = uint32_of_bytes (offset a 12ul) in uint32_to_uint64 x in *)
(*   let b04:u64 = let (x:u32) = uint32_of_bytes b in uint32_to_uint64 x  in *)
(*   let b48:u64 = let (x:u32) = uint32_of_bytes (offset b 4ul) in uint32_to_uint64 x in *)
(*   let b812:u64 = let (x:u32) = uint32_of_bytes (offset b 8ul) in uint32_to_uint64 x in *)
(*   let b1216:u64 = let (x:u32) = uint32_of_bytes (offset b 12ul) in uint32_to_uint64 x in *)
(*   let open FStar.UInt64 in *)
(*   let z0 = a04 +^ b04 in *)
(*   let z1 = a48 +^ b48 +^ (z0 >>^ 32ul) in *)
(*   let z2 = a812 +^ b812 +^ (z1 >>^ 32ul) in *)
(*   let z3 = a1216 +^ b1216 +^ (z2 >>^ 32ul) in *)
(*   bytes_of_uint32 (Buffer.sub a 0ul 4ul) (uint64_to_uint32 z0); *)
(*   bytes_of_uint32 (Buffer.sub a 4ul 4ul) (uint64_to_uint32 z1); *)
(*   bytes_of_uint32 (Buffer.sub a 8ul 4ul) (uint64_to_uint32 z2); *)
(*   bytes_of_uint32 (Buffer.sub a 12ul 4ul) (uint64_to_uint32 z3); *)
(*   admit () *)

(* Finish function, with final accumulator value *)
val poly1305_finish:
  log:log_t ->
  tag:wordB_16 ->
  st:poly1305_state ->
  key:uint8_p ->
  (* acc:elemB -> *)
  (* s:wordB_16 -> *)
  ST unit
    (requires (fun h -> live h tag /\ live h st.h /\ live h key
      /\ norm h st.h
      /\ (if mac_log then disjoint #U8.t tag st.h else disjoint #H8.t tag st.h)
      /\ (if mac_log then disjoint #U8.t tag key else disjoint #H8.t tag key)
      /\ disjoint st.h key))
    (ensures  (fun h0 _ h1 -> live h0 st.h /\ live h0 key
      /\ (if mac_log then modifies_2 #U8.t tag st.h h0 h1 else modifies_2 #H8.t tag st.h h0 h1)
      /\ live h1 st.h /\ live h1 tag
      /\ little_endian (sel_word h1 tag) ==
        (trunc_1305 (sel_elem h0 st.h) + little_endian (sel_word h0 key)) % pow2 128))
let poly1305_finish log tag st key =
  let _ = poly1305_last_sum log st tag key in
  ()

val div_aux: a:UInt32.t -> b:UInt32.t{U32.v b <> 0} -> Lemma
  (requires True)
  (ensures FStar.UInt32(UInt.size (v a / v b) n))
  [SMTPat (FStar.UInt32(UInt.size (v a / v b) n))]
let div_aux a b = ()

(** Computes the Poly1305 MAC on a buffer *)
val poly1305_mac:
  tag:wordB{if mac_log then length #U8.t tag == 16 else length #H8.t tag == 16} ->
  msg:uint8_p{if mac_log then disjoint #U8.t tag msg else disjoint #H8.t tag msg} ->
  len:u32{U32.v len == length msg} ->
  key:uint8_p{length key == 32 /\ disjoint msg key
    /\ (if mac_log then disjoint #U8.t tag key else disjoint #H8.t tag key)} ->
  Stack unit
    (requires (fun h -> live h msg /\ live h key /\ live h tag))
    (ensures (fun h0 _ h1 -> live h0 msg /\ live h0 key /\ live h1 tag
      /\ (if mac_log then modifies_1 #U8.t tag h0 h1 else modifies_1 #H8.t tag h0 h1)
      /\ (let r = Spec.clamp (sel_word h0 (sub key 0ul 16ul)) in
         let s = sel_word h0 (sub key 16ul 16ul) in
         little_endian (sel_word h1 tag) ==
         mac_1305 (encode_pad Seq.createEmpty (Buffer.as_seq h0 msg)) r s)))
let poly1305_mac tag msg len key =
  let h0 = ST.get () in
  push_frame();
  (* Create buffers for the 2 parts of the key and the accumulator *)
  (* let tmp = create 0UL 10ul in *)
  (* let acc = sub tmp 0ul 5ul in *)
  (* let r   = sub tmp 5ul 5ul in *)
  (* let s   = create 0uy 16ul in *)
  let tmp = create (Hacl.Cast.uint64_to_sint64 0uL) 6ul in
  let r = sub tmp 0ul 3ul in
  let h = sub tmp 3ul 3ul in
  let st = {r = r; h = h} in
  (* Initializes the accumulator and the keys values *)
  let initial_log = poly1305_init st key in
  (* let h1 = ST.get () in *)
  (* assert (sel_int h1 r == Spec.clamp (sel_word h0 (sub key 0ul 16ul))); *)
  (* assert (sel_word h1 s == sel_word h0 (sub key 16ul 16ul)); *)
  (* poly1305_start acc; // zeroes acc redundantly *)
  (* Compute the number of 'plain' blocks *)
  let ctr = U32.div len 16ul in
  let rest = U32.rem len 16ul in
  (* Run the poly1305_update function ctr times *)
  let l:log_t = if mac_log then Seq.createEmpty #elem else () in
  let h2 = ST.get () in
  (* norm_eq_lemma h1 h2 r r; *)
  let l = poly1305_loop l msg st ctr in
  assume False; // TODO: REMOVE ME
  (* Run the poly1305_update function one more time on the last incomplete block *)
  let last_block = sub msg (FStar.UInt32 (ctr *^ 16ul)) rest in
  let l = poly1305_last l last_block st rest in
  (* Finish *)
  poly1305_finish l tag st (sub key 16ul 16ul);
  pop_frame()
