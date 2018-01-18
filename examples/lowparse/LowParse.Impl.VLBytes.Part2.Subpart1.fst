module LowParse.Impl.VLBytes.Part2.Subpart1
include LowParse.Impl.VLBytes.Part1

#set-options "--z3rlimit 1024 --max_fuel 8 --max_ifuel 8"

let parse_bounded_integer'_1_correct
  (b: bytes)
: Lemma
  (parse (parse_bounded_integer' 1) b == parse (parse_bounded_integer 1) b)
= ()

#reset-options
