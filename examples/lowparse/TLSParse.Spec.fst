module TLSParse.Spec
open LowParse.Spec

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module L = FStar.List.Tot
module Seq = FStar.Seq
module U32 = FStar.UInt32

#reset-options "--z3rlimit 1024 --max_fuel 64 --max_ifuel 64 --initial_fuel 64 --initial_ifuel 64 --z3cliopt smt.arith.nl=false --z3refresh"

let protocolVersion : Type0 = U16.t

let parse_protocolVersion_kind = parse_u16_kind

let parse_protocolVersion : parser parse_protocolVersion_kind protocolVersion =
  parse_u16

let random : Type0 =
  assert_norm (array_type_of_parser_kind_precond parse_u8 32 == true);
  array_type_of_parser parse_u8 32

let parse_random_kind : parser_kind =
  assert_norm (array_type_of_parser_kind_precond parse_u8 32 == true);
  parse_array_kind parse_u8_kind 32

let parse_random : parser parse_random_kind random =
  assert_norm (array_type_of_parser_kind_precond parse_u8 32 == true);
  assert_norm (random == array_type_of_parser parse_u8 32);
  let p' : parser parse_random_kind (array_type_of_parser parse_u8 32) =
    parse_array parse_u8 32 ()
  in
  p'

type cipherSuite =
  | TLS_AES_128_GCM_SHA256
  | TLS_AES_256_GCM_SHA384
  | TLS_CHACHA20_POLY1305_SHA256
  | TLS_AES_128_CCM_SHA256
  | TLS_AES_128_CCM_8_SHA256

let cipherSuite_enum : total_enum cipherSuite (U8.t * U8.t) =
  let l = [
    TLS_AES_128_GCM_SHA256,       (0x13uy, 0x01uy);
    TLS_AES_256_GCM_SHA384,       (0x13uy, 0x02uy);
    TLS_CHACHA20_POLY1305_SHA256, (0x13uy, 0x03uy);
    TLS_AES_128_CCM_SHA256,       (0x13uy, 0x04uy);
    TLS_AES_128_CCM_8_SHA256,     (0x13uy, 0x05uy);
  ]
  in
  assert_norm (L.noRepeats (L.map fst l));
  assert_norm (L.noRepeats (L.map snd l));
  l

let parse_cipherSuite_kind = parse_filter_kind (and_then_kind parse_u8_kind parse_u8_kind)

let parse_cipherSuite : parser parse_cipherSuite_kind cipherSuite =
  parse_total_enum_key (nondep_then parse_u8 parse_u8) cipherSuite_enum

let maybe_cipherSuite = maybe_total_enum_key cipherSuite_enum

let parse_maybe_cipherSuite_kind = and_then_kind parse_u8_kind parse_u8_kind

let parse_maybe_cipherSuite : parser parse_maybe_cipherSuite_kind maybe_cipherSuite =
  parse_maybe_total_enum_key (nondep_then parse_u8 parse_u8) cipherSuite_enum

type extensionType =
  | EXT_server_name
  | EXT_max_fragment_length
  | EXT_status_request
  | EXT_supported_groups
  | EXT_signature_algorithms
  | EXT_use_srtp
  | EXT_heartbeat
  | EXT_application_layer_protocol_negotiation
  | EXT_signed_certificate_timestamp
  | EXT_client_certificate_type
  | EXT_server_certificate_type
  | EXT_padding
  | EXT_key_share
  | EXT_pre_shared_key
  | EXT_early_data
  | EXT_supported_versions
  | EXT_cookie
  | EXT_psk_key_exchange_modes
  | EXT_certificate_authorities
  | EXT_old_filters
  | EXT_post_handshake_auth

let extensionType_enum : total_enum extensionType U16.t =
  let l = [
    EXT_server_name,                             0us;
    EXT_max_fragment_length,                     1us;
    EXT_status_request,                          5us;
    EXT_supported_groups,                       10us;
    EXT_signature_algorithms,                   13us;
    EXT_use_srtp,                               14us;
    EXT_heartbeat,                              15us;
    EXT_application_layer_protocol_negotiation, 16us;
    EXT_signed_certificate_timestamp,           18us;
    EXT_client_certificate_type,                19us;
    EXT_server_certificate_type,                20us;
    EXT_padding,                                21us;
    EXT_key_share,                              40us;
    EXT_pre_shared_key,                         41us;
    EXT_early_data,                             42us;
    EXT_supported_versions,                     43us;
    EXT_cookie,                                 44us;
    EXT_psk_key_exchange_modes,                 45us;
    EXT_certificate_authorities,                47us;
    EXT_old_filters,                            48us;
    EXT_post_handshake_auth,                    49us;
  ]
  in
  assert_norm (L.noRepeats (L.map fst l));
  assert_norm (L.noRepeats (L.map snd l));
  l

let parse_extensionType_kind = parse_filter_kind parse_u16_kind

let parse_extensionType : parser parse_extensionType_kind extensionType =
  parse_total_enum_key parse_u16 extensionType_enum

type maybe_extensionType = maybe_total_enum_key extensionType_enum

let parse_maybe_extensionType_kind = parse_u16_kind

let parse_maybe_extensionType : parser parse_maybe_extensionType_kind maybe_extensionType =
  parse_maybe_total_enum_key parse_u16 extensionType_enum

noeq
type extension = {
  extension_type: maybe_extensionType;
  extension_data: Seq.seq byte;
}

let extension_presynth = (
  maybe_extensionType * (
  Seq.seq byte
))

module U32 = FStar.UInt32

let parse_extension_kind =
  parse_maybe_extensionType_kind `and_then_kind` (parse_bounded_vlbytes_kind 0 65535)

let parse_extension_presynth : parser parse_extension_kind extension_presynth =
  (
    parse_maybe_extensionType `nondep_then` (
    parse_bounded_vlbytes 0 65535 (parse_seq parse_u8)
  ))

let synth_extension (data: extension_presynth) : Tot extension =
  match data with (
    extension_type,
    extension_data
  ) -> {
    extension_type = extension_type;
    extension_data = extension_data;
  }

let parse_extension : parser parse_extension_kind extension =
  parse_extension_presynth `parse_synth` synth_extension

let clientHello_legacy_version_pred
  (legacy_version: protocolVersion)
: Tot bool
= legacy_version = 0x0303us

let clientHello_legacy_version_t = (legacy_version: protocolVersion { clientHello_legacy_version_pred legacy_version == true } )

let parse_clientHello_legacy_version_kind =
  parse_filter_kind parse_protocolVersion_kind

let parse_clientHello_legacy_version : parser parse_clientHello_legacy_version_kind clientHello_legacy_version_t =
  parse_filter parse_protocolVersion clientHello_legacy_version_pred

let clientHello_legacy_session_id_t : Type0 =
  assert_norm (vlarray_type_of_parser_kind_precond parse_u8 0 32 == true);
  vlarray_type_of_parser parse_u8 0 32

let parse_clientHello_legacy_session_id_kind =
  parse_bounded_vlbytes_kind 0 32

let parse_clientHello_legacy_session_id : parser parse_clientHello_legacy_session_id_kind clientHello_legacy_session_id_t =
  assert_norm (vlarray_type_of_parser_kind_precond parse_u8 0 32 == true);
  let p' : parser parse_clientHello_legacy_session_id_kind (vlarray_type_of_parser parse_u8 0 32) =
    parse_vlarray parse_u8 0 32 ()
  in
  p'

let clientHello_cipher_suites_t =
  assert_norm (vlarray_type_of_parser_kind_precond parse_maybe_cipherSuite 2 65534 == true);
  vlarray_type_of_parser parse_maybe_cipherSuite 2 65534

let parse_clientHello_cipher_suites_kind =
  assert_norm (vlarray_type_of_parser_kind_precond parse_maybe_cipherSuite 2 65534 == true);
  parse_bounded_vlbytes_kind 2 65534

let parse_clientHello_cipher_suites : parser parse_clientHello_cipher_suites_kind clientHello_cipher_suites_t =
  assert_norm (vlarray_type_of_parser_kind_precond parse_maybe_cipherSuite 2 65534 == true);
  let p' : parser parse_clientHello_cipher_suites_kind clientHello_cipher_suites_t =
    parse_vlarray parse_maybe_cipherSuite 2 65534 ()
  in
  p'

let clientHello_legacy_compression_methods_t =
  assert_norm (vlarray_type_of_parser_kind_precond parse_u8 1 255 == true);
  vlarray_type_of_parser parse_u8 1 255

let parse_clientHello_legacy_compression_methods_kind =
  parse_bounded_vlbytes_kind 1 255

let parse_clientHello_legacy_compression_methods : parser parse_clientHello_legacy_compression_methods_kind clientHello_legacy_compression_methods_t =
  assert_norm (vlarray_type_of_parser_kind_precond parse_u8 1 255 == true);
  let p' : parser parse_clientHello_legacy_compression_methods_kind clientHello_legacy_compression_methods_t =
    parse_vlarray parse_u8 1 255 ()
  in
  p'

let clientHello_extensions_t =
  Seq.seq extension

let parse_clientHello_extensions_kind =
  parse_bounded_vlbytes_kind 8 65534

let parse_clientHello_extensions : parser parse_clientHello_extensions_kind clientHello_extensions_t =
  parse_bounded_vlbytes 8 65534 (parse_seq parse_extension)

noeq
type clientHello = {
  legacy_version: clientHello_legacy_version_t;
  random: random;
  legacy_session_id: clientHello_legacy_session_id_t;
  cipher_suites: clientHello_cipher_suites_t;
  legacy_compression_methods: clientHello_legacy_compression_methods_t;
  extensions: clientHello_extensions_t;
}

type clientHello_presynth = (
  (clientHello_legacy_version_t) * (
  random * (
  clientHello_legacy_session_id_t * (
  clientHello_cipher_suites_t * (
  clientHello_legacy_compression_methods_t * (
  clientHello_extensions_t
  ))))))

let parse_clientHello_kind =
  parse_clientHello_legacy_version_kind `and_then_kind` (
  parse_random_kind `and_then_kind` (
  parse_clientHello_legacy_session_id_kind `and_then_kind` (
  parse_clientHello_cipher_suites_kind `and_then_kind` (
  parse_clientHello_legacy_compression_methods_kind `and_then_kind` (
  parse_clientHello_extensions_kind
  )))))

let parse_clientHello_presynth : parser _ (* parse_clientHello_kind *) clientHello_presynth =
//  coerce_parser clientHello_presynth
  (
    parse_clientHello_legacy_version `nondep_then` (
    parse_random `nondep_then` (
    parse_clientHello_legacy_session_id `nondep_then` (
    parse_clientHello_cipher_suites `nondep_then` (
    parse_clientHello_legacy_compression_methods `nondep_then` (
    parse_clientHello_extensions
  ))))))

let synth_clientHello (data: clientHello_presynth) : Tot clientHello = match data with (
    legacy_version, (
    random, (
    legacy_session_id, (
    cipher_suites, (
    legacy_compression_methods, (
    extensions
  )))))) -> {
    legacy_version = legacy_version;
    random = random;
    legacy_session_id = legacy_session_id;
    cipher_suites = cipher_suites;
    legacy_compression_methods = legacy_compression_methods;
    extensions = extensions;
  }

let parse_clientHello : parser _ clientHello =
  parse_clientHello_presynth `parse_synth` synth_clientHello
