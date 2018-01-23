module LowParse.Spec.Bytes
include LowParse.Spec.VLData

module B32 = FStar.Bytes
module Seq = FStar.Seq
module U32 = FStar.UInt32

#set-options "--z3rlimit 128 --max_fuel 64 --max_ifuel 64"

let lt_pow2_32
  (x: nat)
: Lemma
  (requires (x < 4294967296))
  (ensures (x < pow2 32))
= ()

#reset-options

let parse_flbytes_gen
  (sz: nat { sz < 4294967296 } )
  (s: bytes { Seq.length s == sz } )
: GTot (B32.lbytes sz)
= lt_pow2_32 sz;
  B32.hide s

let parse_flbytes
  (sz: nat { sz < 4294967296 } )
: Tot (parser (total_constant_size_parser_kind sz) (B32.lbytes sz))
= make_total_constant_size_parser sz (B32.lbytes sz) (parse_flbytes_gen sz)

let serialize_flbytes'
  (sz: nat { sz < 4294967296 } )
: Tot (bare_serializer (B32.lbytes sz))
= fun (x: B32.lbytes sz) -> (
    lt_pow2_32 sz;
    B32.reveal x
  )

let serialize_flbytes_correct
  (sz: nat { sz < 4294967296 } )
: Lemma
  (serializer_correct (parse_flbytes sz) (serialize_flbytes' sz))
= let prf
    (input: B32.lbytes sz)
  : Lemma
    (
      let ser = serialize_flbytes' sz input in
      Seq.length ser == sz /\
      parse (parse_flbytes sz) ser == Some (input, sz)
    )
  = ()
  in
  Classical.forall_intro prf

let serialize_flbytes
  (sz: nat { sz < 4294967296 } )
: Tot (serializer (parse_flbytes sz))
= serialize_flbytes_correct sz;
  serialize_flbytes' sz

(* VLBytes *)

(* For the payload: since the input buffer is truncated at the time of
reading the length header, "parsing" the payload will always succeed,
by just returning it unchanged (unless the length of the input
is greater than 2^32) *)

let parse_all_bytes_kind =
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_total = false;
    parser_kind_subkind = Some ParserConsumesAll;
  }

let parse_all_bytes'
  (input: bytes)
: GTot (option (B32.bytes * consumed_length input))
= let len = Seq.length input in
  if len >= 4294967296
  then None
  else begin
    lt_pow2_32 len;
    Some (B32.hide input, len)
  end

#set-options "--z3rlimit 16"

let parse_all_bytes_injective () : Lemma
  (injective parse_all_bytes')
= let prf
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond parse_all_bytes' b1 b2))
    (ensures (injective_postcond parse_all_bytes' b1 b2))
  = assert (Seq.length b1 < 4294967296);
    assert (Seq.length b2 < 4294967296);
    lt_pow2_32 (Seq.length b1);
    lt_pow2_32 (Seq.length b2);
    B32.reveal_hide b1;
    B32.reveal_hide b2
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf x))

let parse_all_bytes_correct () : Lemma
  (parser_kind_prop parse_all_bytes_kind parse_all_bytes')
= parse_all_bytes_injective ();
  injective_consumes_all_no_lookahead_weak parse_all_bytes'

let parse_all_bytes : parser parse_all_bytes_kind B32.bytes =
  parse_all_bytes_correct ();
  parse_all_bytes'

let serialize_all_bytes : serializer parse_all_bytes =
  (fun (input: B32.bytes) -> B32.reveal input)

let parse_bounded_vlbytes'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
: Tot (parser (parse_bounded_vldata_kind min max) B32.bytes)
= parse_bounded_vldata min max parse_all_bytes

let parse_bounded_vlbytes_pred
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: B32.bytes)
: GTot Type0
= let reslen = B32.length x in
  min <= reslen /\ reslen <= max

let parse_bounded_vlbytes_t
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot Type0
= (x: B32.bytes { parse_bounded_vlbytes_pred min max x } )

let parse_bounded_vlbytes_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (xbytes: bytes)
  (consumed: consumed_length xbytes)
  (x: B32.bytes)
: Lemma
  (requires (parse (parse_bounded_vlbytes' min max) xbytes == Some (x, consumed)))
  (ensures (parse_bounded_vlbytes_pred min max x))
= parse_bounded_vldata_elim min max parse_all_bytes xbytes x consumed;
  let sz = log256' max in
  let (Some (len, _)) = parse (parse_bounded_integer sz) xbytes in
  let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
  let (Some (x', consumed')) = parse parse_all_bytes input' in
  assert (x' == x);
  assert ((consumed' <: nat) == Seq.length input');
  assert (B32.length x' == Seq.length input');
  assert (log256' max + B32.length x == (consumed <: nat))

let parse_bounded_vlbytes
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot (parser (parse_bounded_vldata_kind min max) (parse_bounded_vlbytes_t min max))
= coerce_parser
  (parse_bounded_vlbytes_t min max)
  (parse_strengthen (parse_bounded_vlbytes' min max) (parse_bounded_vlbytes_pred min max) (parse_bounded_vlbytes_correct min max))
