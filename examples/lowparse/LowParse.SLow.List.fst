module LowParse.SLow.List
include LowParse.Spec.List
include LowParse.SLow.Combinators

module B32 = FStar.Bytes
module U32 = FStar.UInt32

#set-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8"

let rec parse32_list'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (input: bytes32)
: Pure (option (list t * U32.t))
  (requires True)
  (ensures (fun res ->
    parser32_correct (parse_list p) input res
  ))
  (decreases (B32.length input))
= if B32.len input = 0ul
  then Some ([], 0ul)
  else match p32 input with
  | Some (v, consumed) ->
    if consumed = 0ul
    then None
    else begin
      let input' = B32.slice input consumed (B32.len input) in
      match parse32_list' p32 input' with
      | Some (l, consumed') ->
	Some (v :: l, U32.add consumed consumed')
      | _ -> None
    end
  | _ -> None

let parse32_list (#k: parser_kind) (#t: Type0) (#p: parser k t) (p32: parser32 p) : Tot (parser32 (parse_list p)) =
  fun (input: bytes32) -> (parse32_list' p32 input <: (res: option (list t * U32.t) { parser32_correct (parse_list p) input res } ))

let rec partial_serialize32_list'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
  (s32: partial_serializer32 s)
  (input: list t)
: Pure bytes32
  (requires (
    serialize_list_precond k /\ (
    Seq.length (serialize (serialize_list p s) input) < 4294967296
  )))
  (ensures (fun (res: bytes32) ->
    serialize_list_precond k /\
    serializer32_correct (serialize_list p s) input res
  ))
  (decreases input)
= match input with
  | [] ->
    let res = B32.empty_bytes in
    assert (Seq.equal (B32.reveal res) (Seq.createEmpty));
    res
  | a :: q ->
    serialize_list_cons p s a q;
    let sa = s32 a in
    let sq = partial_serialize32_list' p s s32 q in
    let res = B32.append sa sq in
    res

let partial_serialize32_list
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: serializer p)
  (s32: partial_serializer32 s)
  (u: unit {
    serialize_list_precond k
  })
: Tot (partial_serializer32 (serialize_list p s))
= fun (input: list t { Seq.length (serialize (serialize_list p s) input) < 4294967296 } )  -> (partial_serialize32_list' p s s32 input <: (res: bytes32 { serializer32_correct (serialize_list p s) input res }))
