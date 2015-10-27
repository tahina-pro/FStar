{
  open Parser

  module Option  = BatOption
  module String  = BatString
  module Hashtbl = BatHashtbl
  let keywords = Hashtbl.create 0

  let () =
    Hashtbl.add keywords "Var"        VAR;
    Hashtbl.add keywords "Name"       NAME;
    Hashtbl.add keywords "App"        APP;
    Hashtbl.add keywords "Abs"        ABS;
    Hashtbl.add keywords "Binder"     BINDER

}

(* -------------------------------------------------------------------- *)
let lower  = ['a'-'z']
let upper  = ['A'-'Z']
let letter = upper | lower
let digit  = ['0'-'9']

(* -------------------------------------------------------------------- *)
let truewhite = [' ']
let offwhite  = ['\t']
let anywhite  = truewhite | offwhite
let newline   = ('\n' | '\r' '\n')

let integer    = digit+

(* -------------------------------------------------------------------- *)
let ident_start_char       = letter  | '_'
let ident_char             = letter | digit  | '_' | '.'
let ident       = ident_start_char ident_char*

rule token = parse
 | ident as id
     { id |> Hashtbl.find_option keywords |> Option.default (IDENT id) }

 | integer as id
     { INT (int_of_string id) }

 | truewhite+
     { token lexbuf }

 | offwhite+
     { token lexbuf }

 | newline
     { Lexing.new_line lexbuf; token lexbuf }

 | '('         { LPAREN }
 | ')'         { RPAREN }
 | eof         { EOF }
