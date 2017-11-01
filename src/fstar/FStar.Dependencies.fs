(*
   Copyright 2008-2016 Jonathan Protzenko, Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"

// A dependency-finding routine
module FStar.Dependencies
open FStar.ST
open FStar.All
open FStar
open FStar.Util
open FStar.Getopt
open FStar.Ident

(***********************************************************************)
(* Finding the transitive dependencies of a list of files               *)
(***********************************************************************)
let find_deps_if_needed files =
    let all_files, deps = Parser.Dep.collect files in
    match all_files with
    | [] ->
        Util.print_error "Dependency analysis failed; reverting to using only the files provided\n";
        files,
        deps
    | _ ->
        List.rev all_files,
        deps
