
open Prims

type decl =
| DFunction of (typ * lident * binder Prims.list * expr)
| DTypeAlias of (lident * typ)
| DGlobal of (lident * typ * expr)
| DTypeFlat of (lident * (ident * typ) Prims.list) 
 and expr =
| EBound of var
| EOpen of binder
| EQualified of lident
| EConstant of constant
| EUnit
| EApp of (expr * expr Prims.list)
| ELet of (binder * expr * expr)
| EIfThenElse of (expr * expr * expr * typ)
| ESequence of expr Prims.list
| EAssign of (expr * expr)
| EBufCreate of (expr * expr)
| EBufRead of (expr * expr)
| EBufWrite of (expr * expr * expr)
| EBufSub of (expr * expr)
| EBufBlit of (expr * expr * expr * expr * expr)
| EMatch of (expr * branches * typ)
| EOp of (op * width)
| ECast of (expr * typ)
| EPushFrame
| EPopFrame
| EBool of Prims.bool
| EAny
| EAbort
| EReturn of expr
| EFlat of (lident * (ident * expr) Prims.list)
| EField of (lident * expr * ident) 
 and op =
| Add
| AddW
| Sub
| SubW
| Div
| Mult
| Mod
| BOr
| BAnd
| BXor
| BShiftL
| BShiftR
| Eq
| Neq
| Lt
| Lte
| Gt
| Gte
| And
| Or
| Xor
| Not 
 and pattern =
| PUnit
| PBool of Prims.bool
| PVar of binder 
 and width =
| UInt8
| UInt16
| UInt32
| UInt64
| Int8
| Int16
| Int32
| Int64
| Bool 
 and binder =
{name : ident; typ : typ; mut : Prims.bool; mark : Prims.int; meta : meta Prims.option} 
 and meta =
| MetaSequence 
 and typ =
| TInt of width
| TBuf of typ
| TUnit
| TQualified of lident
| TBool
| TAny
| TArrow of (typ * typ)
| TZ 
 and program =
decl Prims.list 
 and branches =
branch Prims.list 
 and branch =
(pattern * expr) 
 and constant =
(width * Prims.string) 
 and var =
Prims.int 
 and ident =
Prims.string 
 and lident =
(ident Prims.list * ident)


let is_DFunction = (fun _discr_ -> (match (_discr_) with
| DFunction (_) -> begin
true
end
| _ -> begin
false
end))


let is_DTypeAlias = (fun _discr_ -> (match (_discr_) with
| DTypeAlias (_) -> begin
true
end
| _ -> begin
false
end))


let is_DGlobal = (fun _discr_ -> (match (_discr_) with
| DGlobal (_) -> begin
true
end
| _ -> begin
false
end))


let is_DTypeFlat = (fun _discr_ -> (match (_discr_) with
| DTypeFlat (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBound = (fun _discr_ -> (match (_discr_) with
| EBound (_) -> begin
true
end
| _ -> begin
false
end))


let is_EOpen = (fun _discr_ -> (match (_discr_) with
| EOpen (_) -> begin
true
end
| _ -> begin
false
end))


let is_EQualified = (fun _discr_ -> (match (_discr_) with
| EQualified (_) -> begin
true
end
| _ -> begin
false
end))


let is_EConstant = (fun _discr_ -> (match (_discr_) with
| EConstant (_) -> begin
true
end
| _ -> begin
false
end))


let is_EUnit = (fun _discr_ -> (match (_discr_) with
| EUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_EApp = (fun _discr_ -> (match (_discr_) with
| EApp (_) -> begin
true
end
| _ -> begin
false
end))


let is_ELet = (fun _discr_ -> (match (_discr_) with
| ELet (_) -> begin
true
end
| _ -> begin
false
end))


let is_EIfThenElse = (fun _discr_ -> (match (_discr_) with
| EIfThenElse (_) -> begin
true
end
| _ -> begin
false
end))


let is_ESequence = (fun _discr_ -> (match (_discr_) with
| ESequence (_) -> begin
true
end
| _ -> begin
false
end))


let is_EAssign = (fun _discr_ -> (match (_discr_) with
| EAssign (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufCreate = (fun _discr_ -> (match (_discr_) with
| EBufCreate (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufRead = (fun _discr_ -> (match (_discr_) with
| EBufRead (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufWrite = (fun _discr_ -> (match (_discr_) with
| EBufWrite (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufSub = (fun _discr_ -> (match (_discr_) with
| EBufSub (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufBlit = (fun _discr_ -> (match (_discr_) with
| EBufBlit (_) -> begin
true
end
| _ -> begin
false
end))


let is_EMatch = (fun _discr_ -> (match (_discr_) with
| EMatch (_) -> begin
true
end
| _ -> begin
false
end))


let is_EOp = (fun _discr_ -> (match (_discr_) with
| EOp (_) -> begin
true
end
| _ -> begin
false
end))


let is_ECast = (fun _discr_ -> (match (_discr_) with
| ECast (_) -> begin
true
end
| _ -> begin
false
end))


let is_EPushFrame = (fun _discr_ -> (match (_discr_) with
| EPushFrame (_) -> begin
true
end
| _ -> begin
false
end))


let is_EPopFrame = (fun _discr_ -> (match (_discr_) with
| EPopFrame (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBool = (fun _discr_ -> (match (_discr_) with
| EBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_EAny = (fun _discr_ -> (match (_discr_) with
| EAny (_) -> begin
true
end
| _ -> begin
false
end))


let is_EAbort = (fun _discr_ -> (match (_discr_) with
| EAbort (_) -> begin
true
end
| _ -> begin
false
end))


let is_EReturn = (fun _discr_ -> (match (_discr_) with
| EReturn (_) -> begin
true
end
| _ -> begin
false
end))


let is_EFlat = (fun _discr_ -> (match (_discr_) with
| EFlat (_) -> begin
true
end
| _ -> begin
false
end))


let is_EField = (fun _discr_ -> (match (_discr_) with
| EField (_) -> begin
true
end
| _ -> begin
false
end))


let is_Add = (fun _discr_ -> (match (_discr_) with
| Add (_) -> begin
true
end
| _ -> begin
false
end))


let is_AddW = (fun _discr_ -> (match (_discr_) with
| AddW (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub (_) -> begin
true
end
| _ -> begin
false
end))


let is_SubW = (fun _discr_ -> (match (_discr_) with
| SubW (_) -> begin
true
end
| _ -> begin
false
end))


let is_Div = (fun _discr_ -> (match (_discr_) with
| Div (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mult = (fun _discr_ -> (match (_discr_) with
| Mult (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod (_) -> begin
true
end
| _ -> begin
false
end))


let is_BOr = (fun _discr_ -> (match (_discr_) with
| BOr (_) -> begin
true
end
| _ -> begin
false
end))


let is_BAnd = (fun _discr_ -> (match (_discr_) with
| BAnd (_) -> begin
true
end
| _ -> begin
false
end))


let is_BXor = (fun _discr_ -> (match (_discr_) with
| BXor (_) -> begin
true
end
| _ -> begin
false
end))


let is_BShiftL = (fun _discr_ -> (match (_discr_) with
| BShiftL (_) -> begin
true
end
| _ -> begin
false
end))


let is_BShiftR = (fun _discr_ -> (match (_discr_) with
| BShiftR (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eq = (fun _discr_ -> (match (_discr_) with
| Eq (_) -> begin
true
end
| _ -> begin
false
end))


let is_Neq = (fun _discr_ -> (match (_discr_) with
| Neq (_) -> begin
true
end
| _ -> begin
false
end))


let is_Lt = (fun _discr_ -> (match (_discr_) with
| Lt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Lte = (fun _discr_ -> (match (_discr_) with
| Lte (_) -> begin
true
end
| _ -> begin
false
end))


let is_Gt = (fun _discr_ -> (match (_discr_) with
| Gt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Gte = (fun _discr_ -> (match (_discr_) with
| Gte (_) -> begin
true
end
| _ -> begin
false
end))


let is_And = (fun _discr_ -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))


let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
true
end
| _ -> begin
false
end))


let is_Xor = (fun _discr_ -> (match (_discr_) with
| Xor (_) -> begin
true
end
| _ -> begin
false
end))


let is_Not = (fun _discr_ -> (match (_discr_) with
| Not (_) -> begin
true
end
| _ -> begin
false
end))


let is_PUnit = (fun _discr_ -> (match (_discr_) with
| PUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_PBool = (fun _discr_ -> (match (_discr_) with
| PBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_PVar = (fun _discr_ -> (match (_discr_) with
| PVar (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt8 = (fun _discr_ -> (match (_discr_) with
| UInt8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt16 = (fun _discr_ -> (match (_discr_) with
| UInt16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt32 = (fun _discr_ -> (match (_discr_) with
| UInt32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt64 = (fun _discr_ -> (match (_discr_) with
| UInt64 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int8 = (fun _discr_ -> (match (_discr_) with
| Int8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int16 = (fun _discr_ -> (match (_discr_) with
| Int16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int32 = (fun _discr_ -> (match (_discr_) with
| Int32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int64 = (fun _discr_ -> (match (_discr_) with
| Int64 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Bool = (fun _discr_ -> (match (_discr_) with
| Bool (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))


let is_MetaSequence = (fun _discr_ -> (match (_discr_) with
| MetaSequence (_) -> begin
true
end
| _ -> begin
false
end))


let is_TInt = (fun _discr_ -> (match (_discr_) with
| TInt (_) -> begin
true
end
| _ -> begin
false
end))


let is_TBuf = (fun _discr_ -> (match (_discr_) with
| TBuf (_) -> begin
true
end
| _ -> begin
false
end))


let is_TUnit = (fun _discr_ -> (match (_discr_) with
| TUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_TQualified = (fun _discr_ -> (match (_discr_) with
| TQualified (_) -> begin
true
end
| _ -> begin
false
end))


let is_TBool = (fun _discr_ -> (match (_discr_) with
| TBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_TAny = (fun _discr_ -> (match (_discr_) with
| TAny (_) -> begin
true
end
| _ -> begin
false
end))


let is_TArrow = (fun _discr_ -> (match (_discr_) with
| TArrow (_) -> begin
true
end
| _ -> begin
false
end))


let is_TZ = (fun _discr_ -> (match (_discr_) with
| TZ (_) -> begin
true
end
| _ -> begin
false
end))


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_80_12) -> begin
_80_12
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_80_15) -> begin
_80_15
end))


let ___DGlobal____0 = (fun projectee -> (match (projectee) with
| DGlobal (_80_18) -> begin
_80_18
end))


let ___DTypeFlat____0 = (fun projectee -> (match (projectee) with
| DTypeFlat (_80_21) -> begin
_80_21
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_80_24) -> begin
_80_24
end))


let ___EOpen____0 = (fun projectee -> (match (projectee) with
| EOpen (_80_27) -> begin
_80_27
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_80_30) -> begin
_80_30
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_80_33) -> begin
_80_33
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_80_36) -> begin
_80_36
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_80_39) -> begin
_80_39
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_80_42) -> begin
_80_42
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_80_45) -> begin
_80_45
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_80_48) -> begin
_80_48
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_80_51) -> begin
_80_51
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_80_54) -> begin
_80_54
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_80_57) -> begin
_80_57
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_80_60) -> begin
_80_60
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_80_63) -> begin
_80_63
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_80_66) -> begin
_80_66
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_80_69) -> begin
_80_69
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_80_72) -> begin
_80_72
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_80_75) -> begin
_80_75
end))


let ___EReturn____0 = (fun projectee -> (match (projectee) with
| EReturn (_80_78) -> begin
_80_78
end))


let ___EFlat____0 = (fun projectee -> (match (projectee) with
| EFlat (_80_81) -> begin
_80_81
end))


let ___EField____0 = (fun projectee -> (match (projectee) with
| EField (_80_84) -> begin
_80_84
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_80_87) -> begin
_80_87
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_80_90) -> begin
_80_90
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_80_94) -> begin
_80_94
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_80_97) -> begin
_80_97
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_80_100) -> begin
_80_100
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_80_103) -> begin
_80_103
end))


type version =
Prims.int


let current_version : version = 9


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _80_109 -> (match (_80_109) with
| (x, _80_106, _80_108) -> begin
x
end))


let snd3 = (fun _80_115 -> (match (_80_115) with
| (_80_111, x, _80_114) -> begin
x
end))


let thd3 = (fun _80_121 -> (match (_80_121) with
| (_80_117, _80_119, x) -> begin
x
end))


let mk_width : Prims.string  ->  width Prims.option = (fun _80_1 -> (match (_80_1) with
| "UInt8" -> begin
Some (UInt8)
end
| "UInt16" -> begin
Some (UInt16)
end
| "UInt32" -> begin
Some (UInt32)
end
| "UInt64" -> begin
Some (UInt64)
end
| "Int8" -> begin
Some (Int8)
end
| "Int16" -> begin
Some (Int16)
end
| "Int32" -> begin
Some (Int32)
end
| "Int64" -> begin
Some (Int64)
end
| _80_132 -> begin
None
end))


let mk_bool_op : Prims.string  ->  op Prims.option = (fun _80_2 -> (match (_80_2) with
| "op_Negation" -> begin
Some (Not)
end
| "op_AmpAmp" -> begin
Some (And)
end
| "op_BarBar" -> begin
Some (Or)
end
| "op_Equality" -> begin
Some (Eq)
end
| "op_disEquality" -> begin
Some (Neq)
end
| _80_140 -> begin
None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))


let mk_op : Prims.string  ->  op Prims.option = (fun _80_3 -> (match (_80_3) with
| ("add") | ("op_Plus_Hat") -> begin
Some (Add)
end
| ("add_mod") | ("op_Plus_Percent_Hat") -> begin
Some (AddW)
end
| ("sub") | ("op_Subtraction_Hat") -> begin
Some (Sub)
end
| ("sub_mod") | ("op_Subtraction_Percent_Hat") -> begin
Some (SubW)
end
| ("mul") | ("op_Star_Hat") -> begin
Some (Mult)
end
| ("div") | ("op_Slash_Hat") -> begin
Some (Div)
end
| ("rem") | ("op_Percent_Hat") -> begin
Some (Mod)
end
| ("logor") | ("op_Bar_Hat") -> begin
Some (BOr)
end
| ("logxor") | ("op_Hat_Hat") -> begin
Some (BXor)
end
| ("logand") | ("op_Amp_Hat") -> begin
Some (BAnd)
end
| ("shift_right") | ("op_Greater_Greater_Hat") -> begin
Some (BShiftR)
end
| ("shift_left") | ("op_Less_Less_Hat") -> begin
Some (BShiftL)
end
| ("eq") | ("op_Equals_Hat") -> begin
Some (Eq)
end
| ("op_Greater_Hat") | ("gt") -> begin
Some (Gt)
end
| ("op_Greater_Equal_Hat") | ("gte") -> begin
Some (Gte)
end
| ("op_Less_Hat") | ("lt") -> begin
Some (Lt)
end
| ("op_Less_Equal_Hat") | ("lte") -> begin
Some (Lte)
end
| _80_178 -> begin
None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_op op) <> None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> None))


type env =
{names : name Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let _80_191 = env
in {names = ({pretty = x; mut = is_mut})::env.names; module_name = _80_191.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _172_539 = (find_name env x)
in _172_539.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _80_207 -> begin
(let _172_547 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _172_547))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _80_220 -> (match (_80_220) with
| ((name, _80_216), _80_219) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _80_222 -> (match (_80_222) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _80_231 = m
in (match (_80_231) with
| ((prefix, final), _80_228, _80_230) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _80_241 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _172_582 = (translate_module m)
in Some (_172_582)))
end)
with
| e -> begin
(

let _80_237 = (let _172_584 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _172_584))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _80_247 -> (match (_80_247) with
| (module_name, modul, _80_246) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _80_254 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_, _, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], FStar_Extraction_ML_Syntax.MLTY_Fun (_, _, t)); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let _80_328 = ()
in try
(match (()) with
| () -> begin
(

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let rec find_return_type = (fun _80_4 -> (match (_80_4) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_80_342, _80_344, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _172_591 = (find_return_type t)
in (translate_type env _172_591))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let body = if (flavor = FStar_Extraction_ML_Syntax.Assumed) then begin
EAbort
end else begin
(translate_expr env body)
end
in (

let name = ((env.module_name), (name))
in Some (DFunction (((t), (name), (binders), (body)))))))))))
end)
with
| e -> begin
(

let _80_334 = (let _172_593 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _172_593))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_366); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _80_359; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _80_356})::[]) -> begin
(

let _80_372 = ()
in try
(match (()) with
| () -> begin
(

let t = (translate_type env t)
in (

let expr = (translate_expr env expr)
in (

let name = ((env.module_name), (name))
in Some (DGlobal (((name), (t), (expr)))))))
end)
with
| e -> begin
(

let _80_378 = (let _172_596 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" name _172_596))
in None)
end)
end
| FStar_Extraction_ML_Syntax.MLM_Let (_80_386, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_398); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _80_394; FStar_Extraction_ML_Syntax.mllb_def = _80_392; FStar_Extraction_ML_Syntax.print_typ = _80_390})::_80_388) -> begin
(

let _80_404 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _80_411 = (match (ts) with
| Some (idents, t) -> begin
(let _172_599 = (let _172_597 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _172_597))
in (let _172_598 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _172_599 _172_598)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_80_414) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_80_417) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (let _172_602 = (let _172_601 = (let _172_600 = (translate_type env t)
in ((name), (_172_600)))
in DTypeAlias (_172_601))
in Some (_172_602)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, [], Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (let _172_607 = (let _172_606 = (let _172_605 = (FStar_List.map (fun _80_439 -> (match (_80_439) with
| (f, t) -> begin
(let _172_604 = (translate_type env t)
in ((f), (_172_604)))
end)) fields)
in ((name), (_172_605)))
in DTypeFlat (_172_606))
in Some (_172_607)))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((name, _80_444, _80_446))::_80_441) -> begin
(

let _80_450 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _80_454 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_80_457) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_80_460) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (_80_468) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Var]")
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _80_472, t2) -> begin
(let _172_612 = (let _172_611 = (translate_type env t1)
in (let _172_610 = (translate_type env t2)
in ((_172_611), (_172_610))))
in TArrow (_172_612))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool") -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt8.t") -> begin
TInt (UInt8)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt16.t") -> begin
TInt (UInt16)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt32.t") -> begin
TInt (UInt32)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt64.t") -> begin
TInt (UInt64)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int8.t") -> begin
TInt (Int8)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int16.t") -> begin
TInt (Int16)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int32.t") -> begin
TInt (Int32)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int64.t") -> begin
TInt (Int64)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
(let _172_613 = (translate_type env arg)
in TBuf (_172_613))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.UInt8.t") -> begin
TInt (UInt8)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.UInt16.t") -> begin
TInt (UInt16)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.UInt32.t") -> begin
TInt (UInt32)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.UInt64.t") -> begin
TInt (UInt64)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.Int8.t") -> begin
TInt (Int8)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.Int16.t") -> begin
TInt (Int16)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.Int32.t") -> begin
TInt (Int32)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.Int64.t") -> begin
TInt (Int64)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.SBuffer.buffer") -> begin
(let _172_614 = (translate_type env arg)
in TBuf (_172_614))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_80_559)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_80_565, (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (_80_572) -> begin
(FStar_All.failwith "todo: translate_type [MLTY_Tuple]")
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _80_582 -> (match (_80_582) with
| ((name, _80_579), typ) -> begin
(let _172_619 = (translate_type env typ)
in {name = name; typ = _172_619; mut = false; mark = 0; meta = None})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _80_591) -> begin
(let _172_622 = (find env name)
in EBound (_172_622))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _172_625 = (let _172_624 = (FStar_Util.must (mk_op op))
in (let _172_623 = (FStar_Util.must (mk_width m))
in ((_172_624), (_172_623))))
in EOp (_172_625))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Hacl")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _172_628 = (let _172_627 = (FStar_Util.must (mk_op op))
in (let _172_626 = (FStar_Util.must (mk_width m))
in ((_172_627), (_172_626))))
in EOp (_172_628))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _172_630 = (let _172_629 = (FStar_Util.must (mk_bool_op op))
in ((_172_629), (Bool)))
in EOp (_172_630))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _80_623); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let _80_653 = if (flavor = FStar_Extraction_ML_Syntax.Mutable) then begin
(let _172_632 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.salloc") -> begin
t
end
| _80_637 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in (let _172_631 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_80_643, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _80_641; FStar_Extraction_ML_Syntax.loc = _80_639} -> begin
body
end
| _80_650 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in ((_172_632), (_172_631))))
end else begin
((typ), (body))
end
in (match (_80_653) with
| (typ, body) -> begin
(

let is_mut = (flavor = FStar_Extraction_ML_Syntax.Mutable)
in (

let binder = (let _172_633 = (translate_type env typ)
in {name = name; typ = _172_633; mut = is_mut; mark = 0; meta = None})
in (

let body = (translate_expr env body)
in (

let env = (extend env name is_mut)
in (

let continuation = (translate_expr env continuation)
in ELet (((binder), (body), (continuation))))))))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) -> begin
(

let t = e.FStar_Extraction_ML_Syntax.mlty
in (let _172_637 = (let _172_636 = (translate_expr env expr)
in (let _172_635 = (translate_branches env t branches)
in (let _172_634 = (translate_type env t)
in ((_172_636), (_172_635), (_172_634)))))
in EMatch (_172_637)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_667; FStar_Extraction_ML_Syntax.loc = _80_665}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _80_677); FStar_Extraction_ML_Syntax.mlty = _80_674; FStar_Extraction_ML_Syntax.loc = _80_672})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Bang") && (is_mutable env v)) -> begin
(let _172_638 = (find env v)
in EBound (_172_638))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_687; FStar_Extraction_ML_Syntax.loc = _80_685}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _80_698); FStar_Extraction_ML_Syntax.mlty = _80_695; FStar_Extraction_ML_Syntax.loc = _80_693})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _172_642 = (let _172_641 = (let _172_639 = (find env v)
in EBound (_172_639))
in (let _172_640 = (translate_expr env e)
in ((_172_641), (_172_640))))
in EAssign (_172_642))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_708; FStar_Extraction_ML_Syntax.loc = _80_706}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") -> begin
(let _172_645 = (let _172_644 = (translate_expr env e1)
in (let _172_643 = (translate_expr env e2)
in ((_172_644), (_172_643))))
in EBufRead (_172_645))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_720; FStar_Extraction_ML_Syntax.loc = _80_718}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _172_648 = (let _172_647 = (translate_expr env e1)
in (let _172_646 = (translate_expr env e2)
in ((_172_647), (_172_646))))
in EBufCreate (_172_648))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_732; FStar_Extraction_ML_Syntax.loc = _80_730}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _172_651 = (let _172_650 = (translate_expr env e1)
in (let _172_649 = (translate_expr env e2)
in ((_172_650), (_172_649))))
in EBufSub (_172_651))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_745; FStar_Extraction_ML_Syntax.loc = _80_743}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _172_654 = (let _172_653 = (translate_expr env e1)
in (let _172_652 = (translate_expr env e2)
in ((_172_653), (_172_652))))
in EBufSub (_172_654))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_757; FStar_Extraction_ML_Syntax.loc = _80_755}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") -> begin
(let _172_658 = (let _172_657 = (translate_expr env e1)
in (let _172_656 = (translate_expr env e2)
in (let _172_655 = (translate_expr env e3)
in ((_172_657), (_172_656), (_172_655)))))
in EBufWrite (_172_658))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_770; FStar_Extraction_ML_Syntax.loc = _80_768}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.SBuffer.index") -> begin
(let _172_661 = (let _172_660 = (translate_expr env e1)
in (let _172_659 = (translate_expr env e2)
in ((_172_660), (_172_659))))
in EBufRead (_172_661))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_782; FStar_Extraction_ML_Syntax.loc = _80_780}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.SBuffer.create") -> begin
(let _172_664 = (let _172_663 = (translate_expr env e1)
in (let _172_662 = (translate_expr env e2)
in ((_172_663), (_172_662))))
in EBufCreate (_172_664))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_794; FStar_Extraction_ML_Syntax.loc = _80_792}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.SBuffer.sub") -> begin
(let _172_667 = (let _172_666 = (translate_expr env e1)
in (let _172_665 = (translate_expr env e2)
in ((_172_666), (_172_665))))
in EBufSub (_172_667))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_807; FStar_Extraction_ML_Syntax.loc = _80_805}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.SBuffer.offset") -> begin
(let _172_670 = (let _172_669 = (translate_expr env e1)
in (let _172_668 = (translate_expr env e2)
in ((_172_669), (_172_668))))
in EBufSub (_172_670))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_819; FStar_Extraction_ML_Syntax.loc = _80_817}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.SBuffer.upd") -> begin
(let _172_674 = (let _172_673 = (translate_expr env e1)
in (let _172_672 = (translate_expr env e2)
in (let _172_671 = (translate_expr env e3)
in ((_172_673), (_172_672), (_172_671)))))
in EBufWrite (_172_674))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_832; FStar_Extraction_ML_Syntax.loc = _80_830}, (_80_837)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_844; FStar_Extraction_ML_Syntax.loc = _80_842}, (_80_849)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_856; FStar_Extraction_ML_Syntax.loc = _80_854}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _172_680 = (let _172_679 = (translate_expr env e1)
in (let _172_678 = (translate_expr env e2)
in (let _172_677 = (translate_expr env e3)
in (let _172_676 = (translate_expr env e4)
in (let _172_675 = (translate_expr env e5)
in ((_172_679), (_172_678), (_172_677), (_172_676), (_172_675)))))))
in EBufBlit (_172_680))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_871; FStar_Extraction_ML_Syntax.loc = _80_869}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Hacl.SBuffer.blit") -> begin
(let _172_686 = (let _172_685 = (translate_expr env e1)
in (let _172_684 = (translate_expr env e2)
in (let _172_683 = (translate_expr env e3)
in (let _172_682 = (translate_expr env e4)
in (let _172_681 = (translate_expr env e5)
in ((_172_685), (_172_684), (_172_683), (_172_682), (_172_681)))))))
in EBufBlit (_172_686))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _80_886; FStar_Extraction_ML_Syntax.loc = _80_884}, (_80_891)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.HST.get") -> begin
EConstant (((UInt8), ("0")))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _80_898; FStar_Extraction_ML_Syntax.loc = _80_896}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _172_688 = (FStar_Util.must (mk_width m))
in (let _172_687 = (FStar_Util.must (mk_op op))
in (mk_op_app env _172_688 _172_687 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Hacl")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _80_912; FStar_Extraction_ML_Syntax.loc = _80_910}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _172_690 = (FStar_Util.must (mk_width m))
in (let _172_689 = (FStar_Util.must (mk_op op))
in (mk_op_app env _172_690 _172_689 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _80_926; FStar_Extraction_ML_Syntax.loc = _80_924}, args) when (is_bool_op op) -> begin
(let _172_691 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _172_691 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _172_693 = (let _172_692 = (FStar_Util.must (mk_width m))
in ((_172_692), (c)))
in EConstant (_172_693))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _80_985; FStar_Extraction_ML_Syntax.loc = _80_983}, (arg)::[]) -> begin
if (FStar_Util.ends_with c "uint64") then begin
(let _172_695 = (let _172_694 = (translate_expr env arg)
in ((_172_694), (TInt (UInt64))))
in ECast (_172_695))
end else begin
if (FStar_Util.ends_with c "uint32") then begin
(let _172_697 = (let _172_696 = (translate_expr env arg)
in ((_172_696), (TInt (UInt32))))
in ECast (_172_697))
end else begin
if (FStar_Util.ends_with c "uint16") then begin
(let _172_699 = (let _172_698 = (translate_expr env arg)
in ((_172_698), (TInt (UInt16))))
in ECast (_172_699))
end else begin
if (FStar_Util.ends_with c "uint8") then begin
(let _172_701 = (let _172_700 = (translate_expr env arg)
in ((_172_700), (TInt (UInt8))))
in ECast (_172_701))
end else begin
if (FStar_Util.ends_with c "int64") then begin
(let _172_703 = (let _172_702 = (translate_expr env arg)
in ((_172_702), (TInt (Int64))))
in ECast (_172_703))
end else begin
if (FStar_Util.ends_with c "int32") then begin
(let _172_705 = (let _172_704 = (translate_expr env arg)
in ((_172_704), (TInt (Int32))))
in ECast (_172_705))
end else begin
if (FStar_Util.ends_with c "int16") then begin
(let _172_707 = (let _172_706 = (translate_expr env arg)
in ((_172_706), (TInt (Int16))))
in ECast (_172_707))
end else begin
if (FStar_Util.ends_with c "int8") then begin
(let _172_709 = (let _172_708 = (translate_expr env arg)
in ((_172_708), (TInt (Int8))))
in ECast (_172_709))
end else begin
(let _172_710 = (FStar_Util.format1 "Unrecognized function from Cast module: %s\n" c)
in (FStar_All.failwith _172_710))
end
end
end
end
end
end
end
end
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Hacl")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _80_1001; FStar_Extraction_ML_Syntax.loc = _80_999}, (arg)::[]) -> begin
if (FStar_Util.ends_with c "uint64") then begin
(let _172_712 = (let _172_711 = (translate_expr env arg)
in ((_172_711), (TInt (UInt64))))
in ECast (_172_712))
end else begin
if (FStar_Util.ends_with c "uint32") then begin
(let _172_714 = (let _172_713 = (translate_expr env arg)
in ((_172_713), (TInt (UInt32))))
in ECast (_172_714))
end else begin
if (FStar_Util.ends_with c "uint16") then begin
(let _172_716 = (let _172_715 = (translate_expr env arg)
in ((_172_715), (TInt (UInt16))))
in ECast (_172_716))
end else begin
if (FStar_Util.ends_with c "uint8") then begin
(let _172_718 = (let _172_717 = (translate_expr env arg)
in ((_172_717), (TInt (UInt8))))
in ECast (_172_718))
end else begin
if (FStar_Util.ends_with c "int64") then begin
(let _172_720 = (let _172_719 = (translate_expr env arg)
in ((_172_719), (TInt (Int64))))
in ECast (_172_720))
end else begin
if (FStar_Util.ends_with c "int32") then begin
(let _172_722 = (let _172_721 = (translate_expr env arg)
in ((_172_721), (TInt (Int32))))
in ECast (_172_722))
end else begin
if (FStar_Util.ends_with c "int16") then begin
(let _172_724 = (let _172_723 = (translate_expr env arg)
in ((_172_723), (TInt (Int16))))
in ECast (_172_724))
end else begin
if (FStar_Util.ends_with c "int8") then begin
(let _172_726 = (let _172_725 = (translate_expr env arg)
in ((_172_725), (TInt (Int8))))
in ECast (_172_726))
end else begin
(let _172_727 = (FStar_Util.format1 "Unrecognized function from Cast module: %s\n" c)
in (FStar_All.failwith _172_727))
end
end
end
end
end
end
end
end
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _80_1016; FStar_Extraction_ML_Syntax.loc = _80_1014}, args) -> begin
(let _172_729 = (let _172_728 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_172_728)))
in EApp (_172_729))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _172_732 = (let _172_731 = (translate_expr env e)
in (let _172_730 = (translate_type env t_to)
in ((_172_731), (_172_730))))
in ECast (_172_732))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_80_1031, fields) -> begin
(let _172_737 = (let _172_736 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _172_735 = (FStar_List.map (fun _80_1037 -> (match (_80_1037) with
| (field, expr) -> begin
(let _172_734 = (translate_expr env expr)
in ((field), (_172_734)))
end)) fields)
in ((_172_736), (_172_735))))
in EFlat (_172_737))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(let _172_740 = (let _172_739 = (assert_lid e.FStar_Extraction_ML_Syntax.mlty)
in (let _172_738 = (translate_expr env e)
in ((_172_739), (_172_738), ((Prims.snd path)))))
in EField (_172_740))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_80_1043) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = e; FStar_Extraction_ML_Syntax.mlty = _80_1048; FStar_Extraction_ML_Syntax.loc = _80_1046}, _80_1052) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_App]")
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_80_1056) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_CTor (_80_1059) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_CTor]")
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _172_741 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_172_741))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (_80_1064) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Tuple]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_80_1067) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_80_1070) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_80_1073) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_80_1076) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : FStar_Extraction_ML_Syntax.mlty  ->  lident = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named ([], lid) -> begin
lid
end
| _80_1084 -> begin
(FStar_All.failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env t branches -> (FStar_List.map (translate_branch env t) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env t _80_1093 -> (match (_80_1093) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _80_1096 = (translate_pat env t pat)
in (match (_80_1096) with
| (env, pat) -> begin
(let _172_749 = (translate_expr env expr)
in ((pat), (_172_749)))
end))
end else begin
(FStar_All.failwith "todo: translate_branch")
end
end))
and translate_pat : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  (env * pattern) = (fun env t p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Unit) -> begin
((env), (PUnit))
end
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (b)) -> begin
((env), (PBool (b)))
end
| FStar_Extraction_ML_Syntax.MLP_Var (name, _80_1107) -> begin
(

let env = (extend env name false)
in (let _172_755 = (let _172_754 = (let _172_753 = (translate_type env t)
in {name = name; typ = _172_753; mut = false; mark = 0; meta = None})
in PVar (_172_754))
in ((env), (_172_755))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Wild]")
end
| FStar_Extraction_ML_Syntax.MLP_Const (_80_1113) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_CTor (_80_1116) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_CTor]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_80_1119) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end
| FStar_Extraction_ML_Syntax.MLP_Record (_80_1122) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Record]")
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (_80_1125) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Tuple]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_80_1133)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_80_1138) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_80_1141) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_80_1144) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_80_1147) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_80_1150, None) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _172_762 = (let _172_761 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_172_761)))
in EApp (_172_762)))




