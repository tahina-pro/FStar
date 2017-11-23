module LowParse.Impl.VLBytes.Part4

module S = LowParse.Slice

#set-options "--z3rlimit 128"

let point_to_vlbytes_contents_correct sz f #b #t p b h len b1 b' =
  S.is_concat_is_concat_gen b b1 b'

#reset-options
