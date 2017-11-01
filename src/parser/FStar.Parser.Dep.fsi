#light "off"
module FStar.Parser.Dep
open FStar.ST
open FStar.All
open FStar
open FStar.Parser
open FStar.Parser.AST
open FStar.Parser.Parse
open FStar.Util
open FStar.Const
open FStar.String
open FStar.Ident
open FStar.Errors
module Const = FStar.Parser.Const
module BU = FStar.Util

type open_kind = | Open_module | Open_namespace

val lowercase_module_name : string -> string

val build_inclusion_candidates_list : unit -> list<(string * string)>

(* Given a filename, returns the list of automatically opened modules
and namespaces *)
val hard_coded_dependencies : string -> list<(lident * open_kind)>

val is_interface: string -> bool
val is_implementation: string -> bool
val cache_file_name: string -> string

type deps
val empty_deps : deps
val collect: list<string> -> list<string> * deps
val deps_of : deps -> string -> list<string>
val print : deps -> unit
val hash_dependences: deps -> string -> option<(list<string>)>
