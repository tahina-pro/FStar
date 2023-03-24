module Z = FStar_BigInt
module M : FStar_Ints.IntegerType = struct
  include Stdint.Uint32
  let n = Z.of_int 32
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

module S : FStar_Ints.ShiftAmountType with type t = M.t = struct
  type t = M.t
  let to_int = M.to_native_int
end
