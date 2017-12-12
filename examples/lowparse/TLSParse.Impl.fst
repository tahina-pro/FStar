module TLSParse.Impl
open LowParse
include TLSParse.Spec

inline_for_extraction
let validate_protocolVersion : stateful_validator parse_protocolVersion =
  validate_u16_st

inline_for_extraction
let parse_protocolVersion_st : parser_st parse_protocolVersion =
  parse_u16_st

#set-options "--z3rlimit 128"

inline_for_extraction
let validate_random : stateful_validator parse_random =
  validate_array validate_u8_st parse_random_precond

inline_for_extraction
let validate_maybe_cipherSuite : stateful_validator parse_maybe_cipherSuite =
  validate_maybe_total_enum_key cipherSuite_enum (validate_nondep_then validate_u8_st validate_u8_st)

inline_for_extraction
let validate_maybe_extensionType : stateful_validator parse_maybe_extensionType =
  validate_maybe_total_enum_key extensionType_enum validate_u16_st

inline_for_extraction
let validate_extension : stateful_validator parse_extension =
  (
    validate_maybe_extensionType `validate_nondep_then` (
    validate_bounded_vlbytes 0ul 65535ul (validate_seq validate_u8_st)
  )) `validate_synth` synth_extension

inline_for_extraction
let validate_clientHello_legacy_session_id_t : stateful_validator parse_clientHello_legacy_session_id_t =
  validate_vlarray validate_u8_st clientHello_legacy_session_id_t_precond

#set-options "--initial_fuel 64 --max_fuel 64 --initial_ifuel 64 --max_ifuel 64 --z3rlimit 1024"

inline_for_extraction
let validate_clientHello : stateful_validator parse_clientHello =
  (
    validate_filter_st' parse_protocolVersion_st (fun (legacy_version: protocolVersion) -> legacy_version = 0x0303us) `validate_nondep_then` (
    validate_random `validate_nondep_then` (
    validate_clientHello_legacy_session_id_t `validate_nondep_then` (
    validate_bounded_vlbytes 2ul 65534ul (validate_seq validate_maybe_cipherSuite) `validate_nondep_then` (
    validate_bounded_vlbytes 1ul 255ul (validate_seq validate_u8_st) `validate_nondep_then` (
    validate_bounded_vlbytes 8ul 65534ul (validate_seq validate_extension)
  )))))) `validate_synth` synth_clientHello
