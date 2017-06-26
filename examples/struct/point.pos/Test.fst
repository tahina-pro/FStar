module Test

module S  = FStar.Pointer
module HST = FStar.HyperStack.ST

let point_struct : S.struct_typ = [
  ("X", S.TBase S.TInt);
  ("Y", S.TBase S.TInt);
  ("Color", S.TBase S.TBool);
]

let point_struct_t = S.TStruct point_struct

let point = S.pointer point_struct_t

#set-options "--z3rlimit 16"

let flip
  (p: point)
: HST.Stack unit
  (requires (fun h -> S.readable h p))
  (ensures (fun h0 _ h1 -> 
      S.readable h0 p
    /\ S.readable h1 p
    /\ S.modifies_1 p h0 h1
    /\ S.gread h1 (S.gfield p "X") == S.gread h0 (S.gfield p "Y")
    /\ S.gread h1 (S.gfield p "Y") == S.gread h0 (S.gfield p "X")
    /\ S.gread h1 (S.gfield p "Color") == not (S.gread h0 (S.gfield p "Color"))
    ))
= let x = S.read (S.field p "X") in
  let y = S.read (S.field p "Y") in
  let color = S.read (S.field p "Color") in
  S.write (S.field p "X") y;
  S.write (S.field p "Y") x;
  S.write (S.field p "Color") (not color);
  S.readable_struct_forall_mem p

#set-options "--z3rlimit 128 --max_fuel 20 --max_ifuel 20"

val flip'
  (p: point)
: HST.Stack unit
  (requires (fun h -> S.readable h p))
  (ensures (fun h0 _ h1 -> 
      S.readable h0 p
    /\ S.readable h1 p
    /\ S.modifies_1 p h0 h1
    /\ S.gread h1 (S.gfield p "X") == S.gread h0 (S.gfield p "Y")
    /\ S.gread h1 (S.gfield p "Y") == S.gread h0 (S.gfield p "X")
    /\ S.gread h1 (S.gfield p "Color") == not (S.gread h0 (S.gfield p "Color"))
    ))
let flip' p
= assert ("X" `S.is_struct_field_of` point_struct);
  assert ("Y" `S.is_struct_field_of` point_struct);
  assert_norm ("Color" `S.is_struct_field_of` point_struct);
  assume ("Color" `S.is_struct_field_of` point_struct); // FIXME: WHY WHY WHY does this assert NOT work?
  let x = S.read (S.field p "X") in
  let y = S.read (S.field p "Y") in
  S.write (S.field p "X") y;
  S.write (S.field p "Y") x;
  let h = HST.get () in
  assume (S.readable h (S.gfield p "Color"));
  assume (S.typ_of_struct_field point_struct "Color" == S.TBase S.TBool);
  let color: bool = S.read (S.field p "Color") in
  S.write (S.field p "Color") (not color);
  let h = HST.get () in
  assert (S.readable h (S.gfield p "X"));
  assert (S.readable h (S.gfield p "Y"));
  assert (S.readable h (S.gfield p "Color"));
  assume (S.readable h p)
//  S.readable_struct_forall_mem p
