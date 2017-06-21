module Test
open FStar.Pointer

let ty: typ =
  TStruct [
    ("A", TStruct [
        ("X", TBase TUInt32);
        ("Y", TArray 5ul (TBase TUInt32))
    ]);
    ("B", TArray 3ul (TBase TUInt64))
  ]

let f () =
  let s : Pointer.pointer ty = screate _ (dummy_val ty) in
  let h = ST.get () in
  let p = Pointer.field (Pointer.field s "A") "Y" in
  let _ = Pointer.write (Pointer.cell p 1ul) 19ul in
  let b = BufferNG.buffer_of_array_pointer p in
  let c = BufferNG.sub b 1ul 3ul in
  let _ = BufferNG.write c 2ul 21ul in
  let u = Pointer.read (Pointer.cell p 1ul) in
  let v = Pointer.read (Pointer.cell p 3ul) in
  assert (u == 19ul /\ v == 21ul);
  ()
