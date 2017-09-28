module PureQD

val byte: Type0

let bytes = Seq.seq byte
/// the abstract model of input is a sequence of bytes, with a limit on size so
/// offsets always fit in a UInt32.t
let bytes32 = bs:bytes{Seq.length bs < pow2 32}

/// parse a value of type t
///
/// - the parser can fail (currently reporting an uninformative [None])
/// - it returns the parsed value as well as the number of bytes read
///   (this is intended to be the number of bytes to advance the input pointer)
///
/// note that the type does not forbid lookahead; the parser can depend on
/// values beyond the returned offset
///
/// these parsers are used as specifications, and thus use unrepresentable types
/// such as byte sequences and natural numbers and are always pure
let parser (t:Type) = b:bytes32 -> Tot (option (t * n:nat{n <= Seq.length b}))

/// monadic bind for the parser monad
val and_then : #t:Type -> #t':Type ->
                p:parser t ->
                p': (t -> parser t') ->
                parser t'

/// monadic return for the parser monad
unfold let parse_ret (#t:Type) (v:t) : parser t =
  fun _ -> Some (v, 0)

/// parser that always fails
let fail_parser #t : parser t = fun b -> None

/// parser that succeeds iff at the end-of-input
let parsing_done : parser unit =
  fun b -> if Seq.length b = 0 then Some ((), 0) else None

/// Parsers for integers
val parse_u8: parser UInt8.t
val parse_u16: parser UInt16.t
val parse_u32: parser UInt32.t

/// vlbytes
val parse_vlbytes1 (#t: Type0) (p: parser t) : parser t
val parse_vlbytes2 (#t: Type0) (p: parser t) : parser t
val parse_vlbytes4 (#t: Type0) (p: parser t) : parser t

/// Parse a list of data, until there is nothing left to read. This parser will mostly fail EXCEPT if the whole size is known and the slice has been suitably truncated beforehand, or if the elements of the list all have a known constant size.
val parse_list (#t: Type0) (p: parser t) : parser (list t)

/// Non-dependent parsing
val parse_nondep_then
  (#t1 #t2: Type0)
  (p1: parser t1)
  (p2: parser t2)
: Tot (parser (t1 * t2))

/// Parse some values, then check if they are valid, then transform them into a higher-level type
val parse_filter
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser t1)
  (f2: t1 -> Tot (option t2))
: Tot (parser t2)

/// Parse some values, then transform them into a higher-level type
val parse_synth
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser t1)
  (f2: t1 -> Tot t2)
: Tot (parser t2)
