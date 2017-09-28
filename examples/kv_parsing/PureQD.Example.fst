module PureQD.Example

module P = PureQD

type example' =
| Left':
    (u1: UInt8.t) ->
    (u2: UInt8.t) ->
    example'
| Right' of UInt16.t

let parse_example' : P.parser example' =
  P.parse_u8 `P.and_then` (fun j ->
    let j' = Int.Cast.uint8_to_uint32 j in
    if j' = 0ul
    then P.parse_synth (P.parse_nondep_then P.parse_u8 P.parse_u8) (fun (u1, u2) -> Left' u1 u2)
    else P.parse_synth P.parse_u16 (fun v -> Right' v)
  )

let parse_list_of_examples : P.parser (list example') =
  P.parse_vlbytes1 (P.parse_list parse_example')
