module Z = FStar_BigInt

module type IntegerType = sig
  type t
  val n: Z.t

  val zero: t
  val one: t
  val ones: t

  val add: t -> t -> t
  val sub: t -> t -> t
  val mul: t -> t -> t

  (* Conversions to and from strings *)
  val to_string: t -> string
  val of_string: string -> t

  (* Conversion to native OCaml ints; these are potentially unsafe and not part
   * of the interface: they are meant to be called only from OCaml code
   * that is doing the right thing *)
  val of_native_int: int -> t
  val to_native_int: t -> int

  val div: t -> t -> t
  val rem: t -> t -> t
  val logand: t -> t -> t
  val logxor: t -> t -> t
  val logor: t -> t -> t
  val lognot: t -> t

  val to_string_hex: t -> string

  val shift_arithmetic_right: t -> int -> t
  val shift_arithmetic_left: t -> int -> t

  (* Comparison operators *)
  val eq: t -> t -> bool
  val gt: t -> t -> bool
  val gte: t -> t -> bool
  val lt: t -> t -> bool
  val lte: t -> t -> bool
end

module type ShiftAmountType = sig
  type t
  val to_int: t -> int
end

module IntegerOps (T: IntegerType) (S: ShiftAmountType) = struct
  include T

  let v (x:t) : Prims.int = Prims.parse_int (to_string x)

  (* Aliases *)
  let add_underspec = add
  let add_mod = add
  let sub_underspec = sub
  let sub_mod = sub
  let mul_underspec = mul
  let mul_mod = mul

  (* Conversions to Zarith's int *)
  let to_int (x:t) : Z.t = Z.of_string (to_string x)
  let of_int (x:Z.t) : t = of_string (Z.to_string x)
  let uint_to_t = of_int
  let __uint_to_t = uint_to_t
  let int_to_t = of_int
  let __uint_to_t = int_to_t

  let to_string_hex_pad i =
    let s0 = to_string_hex i in
    let len = (String.length s0 - 2) in
    let s1 = String.sub s0 2 len in (* Remove leading "0x" *)
    let zeroes = String.make ((Z.to_int n / 4) - len) '0' in
    zeroes ^ s1

  (* The shifts take a uint32 argument, so we need to convert *)
  let shift_right n i  = shift_arithmetic_right n (S.to_int i)
  let shift_left  n i  = shift_arithmetic_left n (S.to_int i)

  (* NOT Constant time operators *)
  let eq_mask  (a:t) (b:t) : t = if eq a b then ones else zero
  let gte_mask (a:t) (b:t) : t = if gte a b then ones else zero

  (* Infix notations *)
  let op_Plus_Hat                 = add
  let op_Plus_Question_Hat        = add_underspec
  let op_Plus_Percent_Hat         = add_mod
  let op_Subtraction_Hat          = sub
  let op_Subtraction_Question_Hat = sub_underspec
  let op_Subtraction_Percent_Hat  = sub_mod
  let op_Star_Hat                 = mul
  let op_Star_Question_Hat        = mul_underspec
  let op_Star_Percent_Hat         = mul_mod
  let op_Slash_Hat                = div
  let op_Percent_Hat              = rem
  let op_Hat_Hat                  = logxor
  let op_Amp_Hat                  = logand
  let op_Bar_Hat                  = logor
  let op_Less_Less_Hat            = shift_left
  let op_Greater_Greater_Hat      = shift_right
  let op_Equals_Hat               = eq
  let op_Greater_Hat              = gt
  let op_Greater_Equals_Hat       = gte
  let op_Less_Hat                 = lt
  let op_Less_Equals_Hat          = lte
end
