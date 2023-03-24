module Z = FStar_BigInt
module M : FStar_Ints.IntegerType = struct
  include Stdint.Int16
  let n = Z.of_int 16
  let ones = pred zero
  let of_native_int = of_int
  let to_native_int = to_int
  let shift_arithmetic_left = shift_left
  let shift_arithmetic_right = shift_right
  let eq a b = a = b
  let gt a b = a > b
  let gte a b = a >= b
  let lt a b = a < b
  let lte a b = a <= b
end
