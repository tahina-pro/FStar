module PureQD.Example

module P = PureQD

type example' =
| Left':
    (u1: UInt8.t) ->
    (u2: UInt8.t) ->
    example'
| Center :
    (u: UInt8.t { UInt8.v u <= 127 } ) ->
    example'
| Right' of UInt16.t

let parse_example' : P.parser example' =
  P.parse_u8 `P.and_then` (fun j ->
    let j' = Int.Cast.uint8_to_uint32 j in
    if j' = 0ul
    then P.parse_synth (P.parse_nondep_then P.parse_u8 P.parse_u8) (fun (u1, u2) -> Left' u1 u2)
    else if j' = 1ul
    then P.parse_filter P.parse_u8 (fun v -> if UInt8.lt v (UInt8.uint_to_t 128) then Some (Center v) else None)
    else if j' = 2ul
    then P.parse_synth P.parse_u16 (fun v -> Right' v)
    else P.fail_parser
  )

let parse_list_of_examples : P.parser (list example') =
  P.parse_vlbytes1 (P.parse_list parse_example')
