module BIGINT = struct
  include Big_int
  type bigint = big_int
  type t = bigint

  let zero = zero_big_int
  let one = big_int_of_int 1
  let two = big_int_of_int 2

  let ediv_big_int = div_big_int
  let erem_big_int = mod_big_int

  (* Zarith div truncates towards zero, rather than (Euclidean) flooring.
     So we NEED to mimic that behavior here. *)
  let div_big_int x y =
    if lt_big_int x zero
    then minus_big_int (ediv_big_int (minus_big_int x) y)
    else ediv_big_int x y
  let mod_big_int x y =
    if lt_big_int x zero
    then minus_big_int (erem_big_int (minus_big_int x) y)
    else erem_big_int x y
(*
    sub_big_int x (mult_big_int (div_big_int x y) y)
*)

  let logand_big_int = and_big_int
  let logor_big_int = or_big_int
  let logxor_big_int = xor_big_int
  let lognot_big_int x =
    if eq_big_int x zero then one else
    logxor_big_int (sub_big_int (power_int_positive_int 2 (num_bits_big_int x)) one) x

  let shift_left_big_int x y = Big_int.shift_left_big_int x (int_of_big_int x)
  let shift_right_big_int x y = Big_int.shift_right_big_int x (int_of_big_int x)
  let shift_arithmetic_left_big_int = Big_int.shift_left_big_int
  let shift_arithmetic_right_big_int = Big_int.shift_right_big_int

  let of_int = big_int_of_int
  let to_int = int_of_big_int

  let of_int_fs x = x
  let to_int_fs x = x

  let hex_of_char = function
    | '0' -> 0
    | '1' -> 1
    | '2' -> 2
    | '3' -> 3
    | '4' -> 4
    | '5' -> 5
    | '6' -> 6
    | '7' -> 7
    | '8' -> 8
    | '9' -> 9
    | 'a' | 'A' -> 10
    | 'b' | 'B' -> 11
    | 'c' | 'C' -> 12
    | 'd' | 'D' -> 13
    | 'e' | 'E' -> 14
    | 'f' | 'F' -> 15
    | _ -> failwith "FStar_BigInt.hex_of_char"

  let sixteen = big_int_of_int 16

  let of_hex s =
    let len = String.length s in
    let rec aux accu i =
      if i = 0
      then accu
      else
        let accu = if i = len then accu else mult_big_int accu sixteen in
        let i = i - 1 in
        let c = String.get s i in
        let accu = add_big_int accu (big_int_of_int (hex_of_char c)) in
        aux accu i
    in
    aux zero_big_int len

  let pp_print fmt x =
    let s = string_of_big_int x in
    Format.pp_print_string fmt s

  let of_float = BatBig_int.of_float
  let to_float = float_of_big_int

  let of_int64 = big_int_of_int64
  let to_int64 = int64_of_big_int

  let big_int_of_string x =
    try
      Big_int.big_int_of_string x
    with _ ->
      (* FStar_Compiler_Util.safe_int_of_string expects big_int_of_string
         to raise Invalid_argument in case of failure *)
      raise (Invalid_argument "big_int_of_string")

end

(*
module BIGINTHashedType : BatHashtbl.HashedType with type t = big_int = struct
  open BIGINT
  type t = big_int
  let pow2_63 = power_int_positive_int 2 63
  let rec uint63_list_of_big_int accu x =
    let (q, r) = quomod_big_int x pow2_63 in
    let accu' = int64_of_big_int r :: accu in
    if eq_big_int q zero_big_int
    then accu'
    else if eq_big_int q (minus_big_int unit_big_int)
    then (-1L) :: accu'
    else uint63_list_of_big_int accu' q
  let hash x = BatHashtbl.hash (uint63_list_of_big_int [] x)
  let equal = eq_big_int
end
module BIGINTOrderedType : BatInterfaces.OrderedType with type t = big_int = struct
  type t = big_int
  let compare = Big_int.compare_big_int
end
*)

type bigint = {
    length: int;
    value: string;
}

type t = bigint

let mirror_char = function
| '0' -> '9'
| '1' -> '8'
| '2' -> '7'
| '3' -> '6'
| '4' -> '5'
| '5' -> '4'
| '6' -> '3'
| '7' -> '2'
| '8' -> '1'
| '9' -> '0'
| x -> x

let bigint_of_big_int'
  (x: BIGINT.big_int)
: bigint
=
  let open BIGINT in
  let nonneg = le_big_int zero_big_int x in
  let s = string_of_big_int x in
  let s0 = s in
  let len = String.length s in
  let s =
    if nonneg
    then s
    else String.map mirror_char s
  in
(*  prerr_string (Printf.sprintf "bigint_of_big_int' : from %s to %s\n" s0 s); *)
  {
    length = (if nonneg then len else 0-len);
    value = s;
  }

let big_int_of_bigint'
  (x: bigint)
: BIGINT.big_int
=
  let open BIGINT in
  let nonneg = x.length >= 0 in
  let s =
    if nonneg
    then x.value
    else String.map mirror_char x.value
  in
(*  prerr_string (Printf.sprintf "big_int_of_bigint' : from %s to %s\n" x.value s); *)
  big_int_of_string s

let bigint_of_big_int x =
  let y = bigint_of_big_int' x in
(*  assert (BIGINT.eq_big_int (big_int_of_bigint' y) x); *)
  y

let big_int_of_bigint x =
  let y = big_int_of_bigint' x in
(*  assert (bigint_of_big_int' y = x); *)
  y

let zero = bigint_of_big_int BIGINT.zero
let one = bigint_of_big_int BIGINT.one
let two = bigint_of_big_int BIGINT.two

let cto (f: 'a -> BIGINT.big_int) (x: 'a) : bigint =
  bigint_of_big_int (f x)

let cfrom1 (f: BIGINT.big_int -> 'a) (x: bigint) : 'a =
  f (big_int_of_bigint x)

let cfrom2 (f: BIGINT.big_int -> BIGINT.big_int -> 'a) : bigint -> bigint -> 'a =
  cfrom1 (fun x -> cfrom1 (f x))

let cunop f = cto (cfrom1 f)

let succ_big_int = cunop BIGINT.succ_big_int
let pred_big_int = cunop BIGINT.pred_big_int
let minus_big_int = cunop BIGINT.minus_big_int
let abs_big_int = cunop BIGINT.abs_big_int

let cbinop f = cfrom2 (fun x -> cto (f x))

let add_big_int = cbinop BIGINT.add_big_int
let mult_big_int = cbinop BIGINT.mult_big_int
let sub_big_int = cbinop BIGINT.sub_big_int
let div_big_int = cbinop BIGINT.div_big_int
let mod_big_int = cbinop BIGINT.mod_big_int

let ediv_big_int = cbinop BIGINT.ediv_big_int
let erem_big_int = cbinop BIGINT.erem_big_int

let eq_big_int = ( = )
let le_big_int = ( <= )
let lt_big_int = ( < )
let ge_big_int = ( >= )
let gt_big_int = ( > )

let logand_big_int = cbinop BIGINT.logand_big_int
let logor_big_int = cbinop BIGINT.logor_big_int
let logxor_big_int = cbinop BIGINT.logxor_big_int
let lognot_big_int = cunop BIGINT.lognot_big_int

let shift_left_big_int = cbinop BIGINT.shift_left_big_int
let shift_right_big_int = cbinop BIGINT.shift_right_big_int

let cbinop1 f = cfrom1 (fun x -> cto (f x))

let shift_arithmetic_left_big_int = cbinop1 BIGINT.shift_arithmetic_left_big_int
let shift_arithmetic_right_big_int = cbinop1 BIGINT.shift_arithmetic_right_big_int

let sqrt_big_int = cunop BIGINT.sqrt_big_int

let of_int = cto BIGINT.of_int
let to_int = cfrom1 BIGINT.to_int

let of_int_fs x = x
let to_int_fs x = x

let big_int_of_string = cto BIGINT.big_int_of_string
let string_of_big_int = cfrom1 BIGINT.string_of_big_int
let of_hex = cto BIGINT.of_hex
let pp_print fmt = cfrom1 (BIGINT.pp_print fmt)

let of_float = cto BIGINT.of_float
let to_float = cfrom1 BIGINT.to_float

let of_int64 = cto BIGINT.of_int64
let to_int64 = cfrom1 BIGINT.to_int64

module HashedType : BatHashtbl.HashedType with type t = bigint = struct
  type t = bigint
  let hash = BatHashtbl.hash
  let equal = ( = )
end

module OrderedType : BatInterfaces.OrderedType with type t = bigint = struct
  type t = bigint
  let compare = cfrom2 Big_int.compare_big_int
end
