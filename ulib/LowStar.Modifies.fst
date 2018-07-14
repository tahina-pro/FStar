module LowStar.Modifies
include LowStar.Buffer

module MG = FStar.ModifiesGen
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32


let cloc_cls = cls

let cloc_of_loc l = l

let loc_of_cloc l = l

let loc_of_cloc_of_loc l = ()

let cloc_of_loc_of_cloc l = ()

let cloc_of_loc_none _ = ()

let cloc_of_loc_union _ _ = ()

let cloc_of_loc_addresses _ _ _ = ()

let cloc_of_loc_regions _ _ = ()

let loc_includes_to_cloc l1 l2 = ()

let loc_disjoint_to_cloc l1 l2 = ()

let modifies_to_cloc l h1 h2 = ()
