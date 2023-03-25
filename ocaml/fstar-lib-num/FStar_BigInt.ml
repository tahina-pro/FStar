module Z = struct
  include Big_int
  type bigint = big_int
  type t = bigint

  let zero = zero_big_int
  let one = big_int_of_int 1
  let two = big_int_of_int 2

  let ediv_big_int = div_big_int
  let erem_big_int = mod_big_int

  let logand_big_int = and_big_int
  let logor_big_int = or_big_int
  let logxor_big_int = xor_big_int
  let lognot_big_int x =
    if x = zero then one else
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

  let of_float x =
    if not (Float.is_integer x)
    then
      big_int_of_int (Float.to_int x)
    else
      let (signif, expon) = Float.frexp x in
      let rec aux lo hi =
        if hi - lo <= 1
        then
          let mantissa = big_int_of_int (Float.to_int (Float.ldexp signif hi)) in (* assuming 64-bit machines *)
          shift_left_big_int mantissa (expon - hi)
        else
          let n = (lo + hi) / 2 in
          let x = Float.ldexp signif n in
          if Float.is_integer x
          then aux lo n
          else aux n hi
      in
      aux 0 expon

  let to_float = float_of_big_int

  let of_int64 = big_int_of_int64
  let to_int64 = int64_of_big_int

end

include Z

module HashedType : BatHashtbl.HashedType with type t = t = struct
  type t = Z.t
  let pow2_63 = power_int_positive_int 2 63
  let rec uint63_list_of_big_int accu x =
    let (q, r) = quomod_big_int x pow2_63 in
    let accu' = int64_of_big_int r :: accu in
    if q = zero_big_int
    then accu'
    else if q = minus_big_int unit_big_int
    then (-1L) :: accu'
    else uint63_list_of_big_int accu' q
  let hash x = BatHashtbl.hash (uint63_list_of_big_int [] x)
  let equal = eq_big_int
end
module OrderedType : BatInterfaces.OrderedType with type t = t = struct
  type t = Z.t
  let compare = compare_big_int
end
