module LowParseWriters.Test
open LowParseWriters.NoHoare // where effect TWrite is defined, including subcomp2 with valid_rewrite between parsers

module U32 = FStar.UInt32

assume val parse_u32' : parser' U32.t
let parse_u32 = Parser _ parse_u32'

noeq
type example = { left: U32.t; right: U32.t }

assume val parse_example' : parser' example
let parse_example = Parser _ parse_example'

assume val valid_rewrite_example : squash (valid_rewrite_prop
  (parse_u32 `parse_pair` parse_u32)
  parse_example
)

assume val write_u32
  (#inv: _)
  (x: U32.t)
: TWrite unit parse_empty parse_u32 inv

let write_example
  inv
  (left right: U32.t)
: TWrite unit parse_empty parse_example inv
=
  write_u32 left;
  frame (fun _ -> write_u32 right)

assume
val parse_vllist
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot parser

assume
val write_vllist_nil
  (#inv: memory_invariant)
  (p: parser)
  (max: U32.t { U32.v max > 0 })
: TWrite unit parse_empty (parse_vllist p 0ul max) inv

assume
val extend_vllist_snoc
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: TWrite unit (parse_vllist p min max `parse_pair` p) (parse_vllist p min max) inv

let write_two_ints
  inv
  (x y: U32.t)
  (max: U32.t { U32.v max > 0 })
: TWrite unit parse_empty (parse_vllist parse_u32 0ul max) inv
= write_vllist_nil parse_u32 max;
  frame (fun _ -> write_u32 x);
  extend_vllist_snoc _ _ _;
  frame (fun _ -> write_u32 y);
  extend_vllist_snoc _ _ _

let write_two_examples
  inv
  (left1 right1 left2 right2: U32.t)
  (max: U32.t { U32.v max > 0 })
: TWrite unit parse_empty (parse_vllist parse_example 0ul max) inv
= write_vllist_nil parse_example max;
  frame (fun _ -> write_example _ left1 right1);
  extend_vllist_snoc _ _ _;
  frame (fun _ -> write_example _ left2 right2);
  extend_vllist_snoc _ _ _

(* TODO: trying to rewrite write_example with write_u32 for individual fields instead of write_example will trigger associativity issues such as:

// parse_empty
write_vllist_nil parse_example max;
// parse_vllist parse_example min max;
frame (fun _ -> write_u32 left1);
// parse_vllist parse_example min max `parse_pair` parse_u32
frame (fun _ -> write_u32 right1);
// (parse_vllist parse_example min max `parse_pair` parse_u32) `parse_pair` parse_u32
// by LowParseWriters.NoHoare.subcomp2 and some associativity, we should have:
// parse_vllist parse_example min max `parse_pair` parse_example
extend_vllist_snoc _ _;
// parse_vllist parse_example min max
// etc.

Ideally, we should have associativity. (but NOT commutativity, of course, since data must be written in order.)
