module LowParse.Impl.VLBytes.Part2.Subpart3
include LowParse.Impl.VLBytes.Part1

#set-options "--z3rlimit 1024"

let parse_bounded_integer'_3_correct
  (b: bytes32)
: Lemma
  (parse (parse_bounded_integer' 3) b == parse (parse_bounded_integer 3) b)
= ()

#reset-options
