module LowParse.Bytes

module Seq = FStar.Seq
module U8 = FStar.UInt8

type byte = U8.byte
type bytes = Seq.seq byte
/// the abstract model of input is a sequence of bytes, with a limit on size so
/// offsets always fit in a U32.t
let bytes32 = bs:bytes{ Seq.length bs < pow2 32}
