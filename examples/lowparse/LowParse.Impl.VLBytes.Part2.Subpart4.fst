module LowParse.Impl.VLBytes.Part2.Subpart4
include LowParse.Impl.VLBytes.Part1

let parse_bounded_integer'_4_correct
  (b: bytes32)
: Lemma
  (parse (parse_bounded_integer' 4) b == parse (parse_bounded_integer 4) b)
= ()
