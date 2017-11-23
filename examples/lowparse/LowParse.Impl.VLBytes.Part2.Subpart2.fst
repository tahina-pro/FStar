module LowParse.Impl.VLBytes.Part2.Subpart2
include LowParse.Impl.VLBytes.Part1

#set-options "--z3rlimit 32"

let parse_bounded_integer'_2_correct
  (b: bytes32)
: Lemma
  (parse (parse_bounded_integer' 2) b == parse (parse_bounded_integer 2) b)
= ()

#reset-options
