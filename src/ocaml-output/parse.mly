%{
(*
 We are expected to have only 6 shift-reduce conflicts in ML and 8 in F#.
 A lot (176) of end-of-stream conflicts are also reported and
 should be investigated...
*)
(* (c) Microsoft Corporation. All rights reserved *)
open Prims
open FStar_Pervasives
open FStar_Errors
open FStar_List
open FStar_Util
open FStar_Range
open FStar_Options
(* TODO : these files should be deprecated and removed *)
open FStar_Syntax_Syntax
open FStar_Parser_Const
open FStar_Syntax_Util
open FStar_Parser_AST
open FStar_Parser_Util
open FStar_Const
open FStar_Ident
open FStar_String

let logic_qualifier_deprecation_warning =
  "logic qualifier is deprecated, please remove it from the source program. In case your program verifies with the qualifier annotated but not without it, please try to minimize the example and file a github issue"

let mk_meta_tac m = Meta m

let old_attribute_syntax_warning =
  "The `[@ ...]` syntax of attributes is deprecated. \
   Use `[@@ a1; a2; ...; an]`, a semi-colon separated list of attributes, instead"

let none_to_empty_list x = 
  match x with
  | None -> []
  | Some l -> l

%}
%start inputFragment
%start term
%start warn_error_list
%token AMP
%token AND
%token AS
%token ASSERT
%token ASSUME
%token ATTRIBUTES
%token BACKTICK
%token BACKTICK_AT
%token BACKTICK_HASH
%token BACKTICK_PERC
%token BANG_LBRACE
%token BAR
%token BAR_RBRACE
%token BAR_RBRACK
%token BEGIN
%token BY
%token <bytes> BYTEARRAY
%token CALC
%token <char> CHAR
%token CLASS
%token COLON
%token COLON_COLON
%token COLON_EQUALS
%token COMMA
%token CONJUNCTION
%token DECREASES
%token DEFAULT
%token DISJUNCTION
%token DOLLAR
%token DOT
%token DOT_LBRACK
%token DOT_LBRACK_BAR
%token DOT_LENS_PAREN_LEFT
%token DOT_LPAREN
%token EFFECT
%token ELSE
%token END
%token ENSURES
%token EOF
%token EQUALS
%token EXCEPTION
%token EXISTS
%token FALSE
%token FORALL
%token FRIEND
%token FUN
%token FUNCTION
%token HASH
%token <string> IDENT
%token <float> IEEE64
%token IF
%token IFF
%token IMPLIES
%token IN
%token INCLUDE
%token INLINE
%token INLINE_FOR_EXTRACTION
%token INSTANCE
%token <string * bool> INT
%token <string * bool> INT16
%token <string * bool> INT32
%token <string * bool> INT64
%token <string * bool> INT8
%token IRREDUCIBLE
%token LARROW
%token LAYERED_EFFECT
%token LBRACE
%token LBRACE_BAR
%token LBRACE_COLON_PATTERN
%token LBRACK
%token LBRACK_AT
%token LBRACK_AT_AT
%token LBRACK_AT_AT_AT
%token LBRACK_BAR
%token LENS_PAREN_LEFT
%token LENS_PAREN_RIGHT
%token <bool> LET
%token LOGIC
%token LONG_LEFT_ARROW
%token LPAREN
%token LPAREN_RPAREN
%token MATCH
%token MINUS
%token MODULE
%token <string> NAME
%token NEW
%token NEW_EFFECT
%token NOEQUALITY
%token NOEXTRACT
%token OF
%token OPAQUE
%token OPEN
%token <string> OPINFIX0a
%token <string> OPINFIX0b
%token <string> OPINFIX0c
%token <string> OPINFIX0d
%token <string> OPINFIX1
%token <string> OPINFIX2
%token <string> OPINFIX3
%token <string> OPINFIX4
%token <string> OPPREFIX
%token <string> OP_MIXFIX_ACCESS
%token <string> OP_MIXFIX_ASSIGNMENT
%token PERCENT_LBRACK
%token PIPE_RIGHT
%token POLYMONADIC_BIND
%token POLYMONADIC_SUBCOMP
%token PRAGMALIGHT
%token PRAGMA_POP_OPTIONS
%token PRAGMA_PUSH_OPTIONS
%token PRAGMA_RESET_OPTIONS
%token PRAGMA_RESTART_SOLVER
%token PRAGMA_SET_OPTIONS
%token PRIVATE
%token QMARK
%token QMARK_DOT
%token QUOTE
%token <string> RANGE
%token RANGE_OF
%token RARROW
%token RBRACE
%token RBRACK
%token <string> REAL
%token REC
%token REFLECTABLE
%token REIFIABLE
%token REIFY
%token REQUIRES
%token RETURNS
%token RPAREN
%token SEMICOLON
%token SEMICOLON_SEMICOLON
%token SET_RANGE_OF
%token SPLICE
%token SQUIGGLY_RARROW
%token <string> STRING
%token SUBKIND
%token SUBTYPE
%token SUB_EFFECT
%token SYNTH
%token THEN
%token <string> TILDE
%token TOTAL
%token TRUE
%token TRY
%token <string> TVAR
%token TYPE
%token TYP_APP_GREATER
%token TYP_APP_LESS
%token <string> UINT16
%token <string> UINT32
%token <string> UINT64
%token <string> UINT8
%token UNDERSCORE
%token UNFOLD
%token UNFOLDABLE
%token UNIV_HASH
%token UNOPTEQUALITY
%token VAL
%token WHEN
%token WITH
%nonassoc THEN
%nonassoc ELSE
%right COLON_COLON
%right AMP
%nonassoc COLON_EQUALS
%left OPINFIX0a
%left OPINFIX0b
%left EQUALS OPINFIX0c
%left OPINFIX0d
%left PIPE_RIGHT
%right OPINFIX1
%left MINUS OPINFIX2 QUOTE
%left OPINFIX3
%left BACKTICK
%left BACKTICK_AT BACKTICK_HASH
%right OPINFIX4
%type <FStar_Parser_AST.inputFragment> inputFragment
%type <FStar_Ident.ident> lident
%type <FStar_Parser_AST.term> term
%type <(FStar_Errors.flag * string) list> warn_error_list
%%

option___anonymous_1_:
  
    {    ( None )}
| OF typ
    {let (_1, t) = ((), $2) in
let x =                                                (t) in
    ( Some x )}

option___anonymous_2_:
  
    {    ( None )}
| OF typ
    {let (_1, t) = ((), $2) in
let x =                                          (t) in
    ( Some x )}

option___anonymous_5_:
  
    {    ( None )}
| BY thunk_atomicTerm_
    {let (_1, tactic) = ((), $2) in
let x =                                                                       (tactic) in
    ( Some x )}

option___anonymous_6_:
  
    {    ( None )}
| BY thunk_typ_
    {let (_1, tactic) = ((), $2) in
let x =                                                                    (tactic) in
    ( Some x )}

option___anonymous_8_:
  
    {    ( None )}
| BY thunk2_typ_
    {let (_1, tactic) = ((), $2) in
let x =                                                                 (tactic) in
    ( Some x )}

option___anonymous_9_:
  
    {    ( None )}
| LBRACE noSeqTerm RBRACE
    {let (_1, e, _3) = ((), $2, ()) in
let x =
  let phi =                 ( {e with level=Formula} ) in
                                               (phi)
in
    ( Some x )}

option_ascribeKind_:
  
    {    ( None )}
| ascribeKind
    {let x = $1 in
    ( Some x )}

option_ascribeTyp_:
  
    {    ( None )}
| ascribeTyp
    {let x = $1 in
    ( Some x )}

option_fsTypeArgs_:
  
    {    ( None )}
| fsTypeArgs
    {let x = $1 in
    ( Some x )}

option_match_returning_:
  
    {    ( None )}
| match_returning
    {let x = $1 in
    ( Some x )}

option_pair_hasSort_simpleTerm__:
  
    {    ( None )}
| hasSort simpleTerm
    {let (x, y) = ($1, $2) in
let x =     ( (x, y) ) in
    ( Some x )}

option_string_:
  
    {    ( None )}
| string
    {let x = $1 in
    ( Some x )}

option_term_:
  
    {    ( None )}
| term
    {let x = $1 in
    ( Some x )}

boption_SQUIGGLY_RARROW_:
  
    {    ( false )}
| SQUIGGLY_RARROW
    {let _1 = () in
    ( true )}

boption___anonymous_0_:
  
    {    ( false )}
| PRAGMALIGHT STRING
    {let (_1, _2) = ((), $2) in
let _1 =                                         ( ) in
    ( true )}

loption_separated_nonempty_list_COMMA_appTerm__:
  
    {    ( [] )}
| separated_nonempty_list_COMMA_appTerm_
    {let x = $1 in
    ( x )}

loption_separated_nonempty_list_SEMICOLON_ident__:
  
    {    ( [] )}
| separated_nonempty_list_SEMICOLON_ident_
    {let x = $1 in
    ( x )}

loption_separated_nonempty_list_SEMICOLON_tuplePattern__:
  
    {    ( [] )}
| separated_nonempty_list_SEMICOLON_tuplePattern_
    {let x = $1 in
    ( x )}

list___anonymous_10_:
  
    {    ( [] )}
| DOT qlident list___anonymous_10_
    {let (_1, id, xs) = ((), $2, $3) in
let x =                                                     (id) in
    ( x :: xs )}

list___anonymous_4_:
  
    {    ( [] )}
| binder list___anonymous_4_
    {let (b, xs) = ($1, $2) in
let x =                            ([b]) in
    ( x :: xs )}
| multiBinder list___anonymous_4_
    {let (bs, xs) = ($1, $2) in
let x =                                                   (bs) in
    ( x :: xs )}

list_argTerm_:
  
    {    ( [] )}
| argTerm list_argTerm_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_atomicTerm_:
  
    {    ( [] )}
| atomicTerm list_atomicTerm_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_attr_letbinding_:
  
    {    ( [] )}
| attr_letbinding list_attr_letbinding_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_calcStep_:
  
    {    ( [] )}
| calcStep list_calcStep_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_constructorDecl_:
  
    {    ( [] )}
| constructorDecl list_constructorDecl_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_decl_:
  
    {    ( [] )}
| decl list_decl_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_decoration_:
  
    {    ( [] )}
| decoration list_decoration_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_multiBinder_:
  
    {    ( [] )}
| multiBinder list_multiBinder_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_aqualifiedWithAttrs_lident__:
  aqualifiedWithAttrs_lident_
    {let x = $1 in
    ( [ x ] )}
| aqualifiedWithAttrs_lident_ nonempty_list_aqualifiedWithAttrs_lident__
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_aqualifiedWithAttrs_lidentOrUnderscore__:
  aqualifiedWithAttrs_lidentOrUnderscore_
    {let x = $1 in
    ( [ x ] )}
| aqualifiedWithAttrs_lidentOrUnderscore_ nonempty_list_aqualifiedWithAttrs_lidentOrUnderscore__
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_atomicPattern_:
  atomicPattern
    {let x = $1 in
    ( [ x ] )}
| atomicPattern nonempty_list_atomicPattern_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_atomicTerm_:
  atomicTerm
    {let x = $1 in
    ( [ x ] )}
| atomicTerm nonempty_list_atomicTerm_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_atomicUniverse_:
  atomicUniverse
    {let x = $1 in
    ( [ x ] )}
| atomicUniverse nonempty_list_atomicUniverse_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_dotOperator_:
  DOT_LPAREN term RPAREN
    {let (_1, e, _3) = ((), $2, ()) in
let x =                              ( mk_ident (".()", rhs parseState 1), e, rhs2 parseState 1 3 ) in
    ( [ x ] )}
| DOT_LBRACK term RBRACK
    {let (_1, e, _3) = ((), $2, ()) in
let x =                              ( mk_ident (".[]", rhs parseState 1), e, rhs2 parseState 1 3 ) in
    ( [ x ] )}
| DOT_LBRACK_BAR term BAR_RBRACK
    {let (_1, e, _3) = ((), $2, ()) in
let x =                                      ( mk_ident (".[||]", rhs parseState 1), e, rhs2 parseState 1 3 ) in
    ( [ x ] )}
| DOT_LENS_PAREN_LEFT term LENS_PAREN_RIGHT
    {let (_1, e, _3) = ((), $2, ()) in
let x =                                                 ( mk_ident (".(||)", rhs parseState 1), e, rhs2 parseState 1 3 ) in
    ( [ x ] )}
| DOT_LPAREN term RPAREN nonempty_list_dotOperator_
    {let (_1, e, _3, xs) = ((), $2, (), $4) in
let x =                              ( mk_ident (".()", rhs parseState 1), e, rhs2 parseState 1 3 ) in
    ( x :: xs )}
| DOT_LBRACK term RBRACK nonempty_list_dotOperator_
    {let (_1, e, _3, xs) = ((), $2, (), $4) in
let x =                              ( mk_ident (".[]", rhs parseState 1), e, rhs2 parseState 1 3 ) in
    ( x :: xs )}
| DOT_LBRACK_BAR term BAR_RBRACK nonempty_list_dotOperator_
    {let (_1, e, _3, xs) = ((), $2, (), $4) in
let x =                                      ( mk_ident (".[||]", rhs parseState 1), e, rhs2 parseState 1 3 ) in
    ( x :: xs )}
| DOT_LENS_PAREN_LEFT term LENS_PAREN_RIGHT nonempty_list_dotOperator_
    {let (_1, e, _3, xs) = ((), $2, (), $4) in
let x =                                                 ( mk_ident (".(||)", rhs parseState 1), e, rhs2 parseState 1 3 ) in
    ( x :: xs )}

nonempty_list_patternOrMultibinder_:
  patternOrMultibinder
    {let x = $1 in
    ( [ x ] )}
| patternOrMultibinder nonempty_list_patternOrMultibinder_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

separated_nonempty_list_AND_letbinding_:
  letbinding
    {let x = $1 in
    ( [ x ] )}
| letbinding AND separated_nonempty_list_AND_letbinding_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_AND_typeDecl_:
  typeDecl
    {let x = $1 in
    ( [ x ] )}
| typeDecl AND separated_nonempty_list_AND_typeDecl_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_BAR_tuplePattern_:
  tuplePattern
    {let x = $1 in
    ( [ x ] )}
| tuplePattern BAR separated_nonempty_list_BAR_tuplePattern_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_appTerm_:
  appTerm
    {let x = $1 in
    ( [ x ] )}
| appTerm COMMA separated_nonempty_list_COMMA_appTerm_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_atomicTerm_:
  atomicTerm
    {let x = $1 in
    ( [ x ] )}
| atomicTerm COMMA separated_nonempty_list_COMMA_atomicTerm_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_constructorPattern_:
  constructorPattern
    {let x = $1 in
    ( [ x ] )}
| constructorPattern COMMA separated_nonempty_list_COMMA_constructorPattern_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_tmEq_:
  tmEq
    {let x = $1 in
    ( [ x ] )}
| tmEq COMMA separated_nonempty_list_COMMA_tmEq_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_tvar_:
  tvar
    {let x = $1 in
    ( [ x ] )}
| tvar COMMA separated_nonempty_list_COMMA_tvar_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_DISJUNCTION_conjunctivePat_:
  conjunctivePat
    {let x = $1 in
    ( [ x ] )}
| conjunctivePat DISJUNCTION separated_nonempty_list_DISJUNCTION_conjunctivePat_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_SEMICOLON_appTerm_:
  appTerm
    {let x = $1 in
    ( [ x ] )}
| appTerm SEMICOLON separated_nonempty_list_SEMICOLON_appTerm_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_SEMICOLON_effectDecl_:
  effectDecl
    {let x = $1 in
    ( [ x ] )}
| effectDecl SEMICOLON separated_nonempty_list_SEMICOLON_effectDecl_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_SEMICOLON_ident_:
  ident
    {let x = $1 in
    ( [ x ] )}
| ident SEMICOLON separated_nonempty_list_SEMICOLON_ident_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_SEMICOLON_tuplePattern_:
  tuplePattern
    {let x = $1 in
    ( [ x ] )}
| tuplePattern SEMICOLON separated_nonempty_list_SEMICOLON_tuplePattern_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

inputFragment:
  boption___anonymous_0_ list_decl_ EOF
    {let (is_light, decls, _3) = ($1, $2, ()) in
      (
        as_frag is_light (rhs parseState 1) decls
      )}

pragma:
  PRAGMA_SET_OPTIONS string
    {let (_1, s) = ((), $2) in
      ( SetOptions s )}
| PRAGMA_RESET_OPTIONS option_string_
    {let (_1, s_opt) = ((), $2) in
      ( ResetOptions s_opt )}
| PRAGMA_PUSH_OPTIONS option_string_
    {let (_1, s_opt) = ((), $2) in
      ( PushOptions s_opt )}
| PRAGMA_POP_OPTIONS
    {let _1 = () in
      ( PopOptions )}
| PRAGMA_RESTART_SOLVER
    {let _1 = () in
      ( RestartSolver )}

attribute:
  LBRACK_AT list_atomicTerm_ RBRACK
    {let (_1, x, _3) = ((), $2, ()) in
      (
        let _ =
            match x with
            | _::_::_ ->
                  log_issue (lhs parseState) (Warning_DeprecatedAttributeSyntax,
                                              old_attribute_syntax_warning)
            | _ -> () in
         x
      )}
| LBRACK_AT_AT right_flexible_list_SEMICOLON_noSeqTerm_ RBRACK
    {let (_1, l, _3) = ((), $2, ()) in
let x =                                                 ( l ) in
      ( x )}

decoration:
  attribute
    {let x = $1 in
      ( DeclAttributes x )}
| qualifier
    {let x = $1 in
      ( Qualifier x )}

decl:
  ASSUME uident COLON noSeqTerm
    {let (_1, lid, _3, e) = ((), $2, (), $4) in
let phi =                 ( {e with level=Formula} ) in
      ( mk_decl (Assume(lid, phi)) (rhs2 parseState 1 4) [ Qualifier Assumption ] )}
| list_decoration_ rawDecl
    {let (ds, decl) = ($1, $2) in
      ( mk_decl decl (rhs parseState 2) ds )}
| list_decoration_ typeclassDecl
    {let (ds, decl) = ($1, $2) in
      ( let (decl, extra_attrs) = decl in
        let d = mk_decl decl (rhs parseState 2) ds in
        { d with attrs = extra_attrs @ d.attrs }
      )}

typeclassDecl:
  CLASS typeDecl
    {let (_1, tcdef) = ((), $2) in
      (
        (* Only a single type decl allowed, but construct it the same as for multiple ones.
         * Only difference is the `true` below marking that this a class so desugaring
         * adds the needed %splice. *)
        let d = Tycon (false, true, [tcdef]) in

        (* No attrs yet, but perhaps we want a `class` attribute *)
        (d, [])
      )}
| INSTANCE letqualifier letbinding
    {let (_1, q, lb) = ((), $2, $3) in
      (
        (* Making a single letbinding *)
        let r = rhs2 parseState 1 3 in
        let lbs = focusLetBindings [lb] r in (* lbs is a singleton really *)
        let d = TopLevelLet(q, lbs) in

        (* Slapping a `tcinstance` attribute to it *)
        let at = mk_term (Var tcinstance_lid) r Type_level in

        (d, [at])
      )}

rawDecl:
  pragma
    {let p = $1 in
      ( Pragma p )}
| OPEN quident
    {let (_1, uid) = ((), $2) in
      ( Open uid )}
| FRIEND quident
    {let (_1, uid) = ((), $2) in
      ( Friend uid )}
| INCLUDE quident
    {let (_1, uid) = ((), $2) in
      ( Include uid )}
| MODULE uident EQUALS quident
    {let (_1, uid1, _3, uid2) = ((), $2, (), $4) in
      ( ModuleAbbrev(uid1, uid2) )}
| MODULE qlident
    {let (_1, _2) = ((), $2) in
      ( raise_error (Fatal_SyntaxError, "Syntax error: expected a module name") (rhs parseState 2) )}
| MODULE quident
    {let (_1, uid) = ((), $2) in
      (  TopLevelModule uid )}
| TYPE separated_nonempty_list_AND_typeDecl_
    {let (_1, tcdefs) = ((), $2) in
      ( Tycon (false, false, tcdefs) )}
| EFFECT uident typars EQUALS typ
    {let (_1, uid, tparams, _4, t) = ((), $2, $3, (), $5) in
      ( Tycon(true, false, [(TyconAbbrev(uid, tparams, None, t))]) )}
| LET letqualifier separated_nonempty_list_AND_letbinding_
    {let (_1, q, lbs) = ($1, $2, $3) in
      (
        let r = rhs2 parseState 1 3 in
        let lbs = focusLetBindings lbs r in
        if q <> Rec && List.length lbs <> 1
        then raise_error (Fatal_MultipleLetBinding, "Unexpected multiple let-binding (Did you forget some rec qualifier ?)") r;
        TopLevelLet(q, lbs)
      )}
| VAL constant
    {let (_1, c) = ((), $2) in
      (
        (* This is just to provide a better error than "syntax error" *)
        raise_error (Fatal_SyntaxError, "Syntax error: constants are not allowed in val declarations") (rhs2 parseState 1 2)
      )}
| VAL lidentOrOperator list_multiBinder_ COLON typ
    {let (_1, lid, bss, _4, t) = ((), $2, $3, (), $5) in
      (
        let t = match flatten bss with
          | [] -> t
          | bs -> mk_term (Product(bs, t)) (rhs2 parseState 3 5) Type_level
        in Val(lid, t)
      )}
| SPLICE LBRACK loption_separated_nonempty_list_SEMICOLON_ident__ RBRACK thunk_atomicTerm_
    {let (_1, _2, xs, _4, t) = ((), (), $3, (), $5) in
let ids =     ( xs ) in
      ( Splice (ids, t) )}
| EXCEPTION uident option___anonymous_1_
    {let (_1, lid, t_opt) = ((), $2, $3) in
      ( Exception(lid, t_opt) )}
| NEW_EFFECT newEffect
    {let (_1, ne) = ((), $2) in
      ( NewEffect ne )}
| LAYERED_EFFECT effectDefinition
    {let (_1, ne) = ((), $2) in
      ( LayeredEffect ne )}
| EFFECT layeredEffectDefinition
    {let (_1, ne) = ((), $2) in
      ( LayeredEffect ne )}
| SUB_EFFECT subEffect
    {let (_1, se) = ((), $2) in
      ( SubEffect se )}
| POLYMONADIC_BIND polymonadic_bind
    {let (_1, b) = ((), $2) in
      ( Polymonadic_bind b )}
| POLYMONADIC_SUBCOMP polymonadic_subcomp
    {let (_1, c) = ((), $2) in
      ( Polymonadic_subcomp c )}

typeDecl:
  ident typars option_ascribeKind_ typeDefinition
    {let (lid, tparams, ascr_opt, tcdef) = ($1, $2, $3, $4) in
      ( tcdef lid tparams ascr_opt )}

typars:
  tvarinsts
    {let x = $1 in
                             ( x )}
| binders
    {let x = $1 in
                             ( x )}

tvarinsts:
  TYP_APP_LESS separated_nonempty_list_COMMA_tvar_ TYP_APP_GREATER
    {let (_1, tvs, _3) = ((), $2, ()) in
      ( map (fun tv -> mk_binder (TVariable(tv)) (range_of_id tv) Kind None) tvs )}

typeDefinition:
  
    {      ( (fun id binders kopt -> check_id id; TyconAbstract(id, binders, kopt)) )}
| EQUALS typ
    {let (_1, t) = ((), $2) in
      ( (fun id binders kopt ->  check_id id; TyconAbbrev(id, binders, kopt, t)) )}
| EQUALS LBRACE right_flexible_nonempty_list_SEMICOLON_recordFieldDecl_ RBRACE
    {let (_1, _2, record_field_decls, _4) = ((), (), $3, ()) in
      ( (fun id binders kopt -> check_id id; TyconRecord(id, binders, kopt, record_field_decls)) )}
| EQUALS list_constructorDecl_
    {let (_1, ct_decls) = ((), $2) in
      ( (fun id binders kopt -> check_id id; TyconVariant(id, binders, kopt, ct_decls)) )}

recordFieldDecl:
  aqualifiedWithAttrs_lident_ COLON typ
    {let (qualified_lid, _2, t) = ($1, (), $3) in
      ( 
        let (qual, attrs), lid = qualified_lid in
        (lid, qual, attrs, t) 
      )}

constructorDecl:
  BAR uident COLON typ
    {let (_1, uid, _3, t) = ((), $2, (), $4) in
                                              ( (uid, Some t, false) )}
| BAR uident option___anonymous_2_
    {let (_1, uid, t_opt) = ((), $2, $3) in
                                              ( (uid, t_opt, true) )}

attr_letbinding:
  AND letbinding
    {let (_2, lb) = ((), $2) in
let attr =     ( None ) in
    ( attr, lb )}
| attribute AND letbinding
    {let (x, _2, lb) = ($1, (), $3) in
let attr =     ( Some x ) in
    ( attr, lb )}

letbinding:
  maybeFocus lidentOrOperator nonempty_list_patternOrMultibinder_ option_ascribeTyp_ EQUALS term
    {let (focus_opt, lid, lbp, ascr_opt, _5, tm) = ($1, $2, $3, $4, (), $6) in
      (
        let pat = mk_pattern (PatVar(lid, None, [])) (rhs parseState 2) in
        let pat = mk_pattern (PatApp (pat, flatten lbp)) (rhs2 parseState 1 3) in
        let pos = rhs2 parseState 1 6 in
        match ascr_opt with
        | None -> (focus_opt, (pat, tm))
        | Some t -> (focus_opt, (mk_pattern (PatAscribed(pat, t)) pos, tm))
      )}
| maybeFocus tuplePattern ascribeTyp EQUALS term
    {let (focus_opt, pat, ascr, _4, tm) = ($1, $2, $3, (), $5) in
      ( focus_opt, (mk_pattern (PatAscribed(pat, ascr)) (rhs2 parseState 1 4), tm) )}
| maybeFocus tuplePattern EQUALS term
    {let (focus_opt, pat, _3, tm) = ($1, $2, (), $4) in
      ( focus_opt, (pat, tm) )}

newEffect:
  effectRedefinition
    {let ed = $1 in
    ( ed )}
| effectDefinition
    {let ed = $1 in
    ( ed )}

effectRedefinition:
  uident EQUALS simpleTerm
    {let (lid, _2, t) = ($1, (), $3) in
    ( RedefineEffect(lid, [], t) )}

effectDefinition:
  LBRACE uident binders COLON tmArrow_tmNoEq_ WITH separated_nonempty_list_SEMICOLON_effectDecl_ RBRACE
    {let (_1, lid, bs, _4, typ, _6, eds, _8) = ((), $2, $3, (), $5, (), $7, ()) in
    ( DefineEffect(lid, bs, typ, eds) )}

layeredEffectDefinition:
  LBRACE uident binders WITH tmNoEq RBRACE
    {let (_1, lid, bs, _4, r, _6) = ((), $2, $3, (), $5, ()) in
    (
      let typ =  (* bs -> Effect *)
        let first_b, last_b =
          match bs with
          | [] ->
             raise_error (Fatal_SyntaxError,
                          "Syntax error: unexpected empty binders list in the layered effect definition")
                         (range_of_id lid)
          | _ -> hd bs, last bs |> must in
        let r = union_ranges first_b.brange last_b.brange in
        mk_term (Product (bs, mk_term (Name (lid_of_str "Effect")) r Type_level)) r Type_level in
      let rec decls (r:term) =
        match r.tm with
        | Paren r -> decls r
        | Record (None, flds) ->
           flds |> List.map (fun (lid, t) ->
                              mk_decl (Tycon (false,
                                              false,
                                              [TyconAbbrev (ident_of_lid lid, [], None, t)]))
                                      t.range [])
        | _ ->
           raise_error (Fatal_SyntaxError,
                        "Syntax error: layered effect combinators should be declared as a record")
                       r.range in
      DefineEffect (lid, [], typ, decls r) )}

effectDecl:
  lident binders EQUALS simpleTerm
    {let (lid, action_params, _3, t) = ($1, $2, (), $4) in
    ( mk_decl (Tycon (false, false, [TyconAbbrev(lid, action_params, None, t)])) (rhs2 parseState 1 3) [] )}

subEffect:
  quident SQUIGGLY_RARROW quident EQUALS simpleTerm
    {let (src_eff, _2, tgt_eff, _4, lift) = ($1, (), $3, (), $5) in
      ( { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift } )}
| quident SQUIGGLY_RARROW quident LBRACE IDENT EQUALS simpleTerm RBRACE
    {let (src_eff, _2, tgt_eff, _4, x, _2_inlined1, y, _7) = ($1, (), $3, (), $5, (), $7, ()) in
let lift2_opt =     ( None ) in
let lift1 =     ( (x, y) ) in
     (
       match lift2_opt with
       | None ->
          begin match lift1 with
          | ("lift", lift) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = LiftForFree lift }
          | ("lift_wp", lift_wp) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift_wp }
          | _ ->
             raise_error (Fatal_UnexpectedIdentifier, "Unexpected identifier; expected {'lift', and possibly 'lift_wp'}") (lhs parseState)
          end
       | Some (id2, tm2) ->
          let (id1, tm1) = lift1 in
          let lift, lift_wp = match (id1, id2) with
                  | "lift_wp", "lift" -> tm1, tm2
                  | "lift", "lift_wp" -> tm2, tm1
                  | _ -> raise_error (Fatal_UnexpectedIdentifier, "Unexpected identifier; expected {'lift', 'lift_wp'}") (lhs parseState)
          in
          { msource = src_eff; mdest = tgt_eff; lift_op = ReifiableLift (lift, lift_wp) }
     )}
| quident SQUIGGLY_RARROW quident LBRACE IDENT EQUALS simpleTerm SEMICOLON IDENT EQUALS simpleTerm RBRACE
    {let (src_eff, _2, tgt_eff, _4, x, _2_inlined1, y, _1, id, _2_inlined2, y_inlined1, _7) = ($1, (), $3, (), $5, (), $7, (), $9, (), $11, ()) in
let lift2_opt =
  let y = y_inlined1 in
  let x =
    let x =                                                           (id) in
        ( (x, y) )
  in
      ( Some x )
in
let lift1 =     ( (x, y) ) in
     (
       match lift2_opt with
       | None ->
          begin match lift1 with
          | ("lift", lift) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = LiftForFree lift }
          | ("lift_wp", lift_wp) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift_wp }
          | _ ->
             raise_error (Fatal_UnexpectedIdentifier, "Unexpected identifier; expected {'lift', and possibly 'lift_wp'}") (lhs parseState)
          end
       | Some (id2, tm2) ->
          let (id1, tm1) = lift1 in
          let lift, lift_wp = match (id1, id2) with
                  | "lift_wp", "lift" -> tm1, tm2
                  | "lift", "lift_wp" -> tm2, tm1
                  | _ -> raise_error (Fatal_UnexpectedIdentifier, "Unexpected identifier; expected {'lift', 'lift_wp'}") (lhs parseState)
          in
          { msource = src_eff; mdest = tgt_eff; lift_op = ReifiableLift (lift, lift_wp) }
     )}

polymonadic_bind:
  LPAREN quident COMMA quident RPAREN PIPE_RIGHT quident EQUALS simpleTerm
    {let (_1, m_eff, _3, n_eff, _5, _6, p_eff, _8, bind) = ((), $2, (), $4, (), (), $7, (), $9) in
      ( (m_eff, n_eff, p_eff, bind) )}

polymonadic_subcomp:
  quident SUBTYPE quident EQUALS simpleTerm
    {let (m_eff, _2, n_eff, _4, subcomp) = ($1, (), $3, (), $5) in
    ( (m_eff, n_eff, subcomp) )}

qualifier:
  ASSUME
    {let _1 = () in
                  ( Assumption )}
| INLINE
    {let _1 = () in
                  (
    raise_error (Fatal_InlineRenamedAsUnfold, "The 'inline' qualifier has been renamed to 'unfold'") (lhs parseState)
   )}
| UNFOLDABLE
    {let _1 = () in
                  (
              raise_error (Fatal_UnfoldableDeprecated, "The 'unfoldable' qualifier is no longer denotable; it is the default qualifier so just omit it") (lhs parseState)
   )}
| INLINE_FOR_EXTRACTION
    {let _1 = () in
                          (
     Inline_for_extraction
  )}
| UNFOLD
    {let _1 = () in
           (
     Unfold_for_unification_and_vcgen
  )}
| IRREDUCIBLE
    {let _1 = () in
                  ( Irreducible )}
| NOEXTRACT
    {let _1 = () in
                  ( NoExtract )}
| DEFAULT
    {let _1 = () in
                  ( DefaultEffect )}
| TOTAL
    {let _1 = () in
                  ( TotalEffect )}
| PRIVATE
    {let _1 = () in
                  ( Private )}
| NOEQUALITY
    {let _1 = () in
                  ( Noeq )}
| UNOPTEQUALITY
    {let _1 = () in
                  ( Unopteq )}
| NEW
    {let _1 = () in
                  ( New )}
| LOGIC
    {let _1 = () in
                  ( log_issue (lhs parseState) (Warning_logicqualifier,
                                                logic_qualifier_deprecation_warning);
                    Logic )}
| OPAQUE
    {let _1 = () in
                  ( Opaque )}
| REIFIABLE
    {let _1 = () in
                  ( Reifiable )}
| REFLECTABLE
    {let _1 = () in
                  ( Reflectable )}

maybeFocus:
  boption_SQUIGGLY_RARROW_
    {let b = $1 in
                               ( b )}

letqualifier:
  REC
    {let _1 = () in
                ( Rec )}
| 
    {                ( NoLetQualifier )}

aqual:
  HASH LBRACK thunk_tmNoEq_ RBRACK
    {let (_1, _2, t, _4) = ((), (), $3, ()) in
                                       ( mk_meta_tac t )}
| HASH
    {let _1 = () in
              ( Implicit )}
| DOLLAR
    {let _1 = () in
              ( Equality )}

binderAttributes:
  LBRACK_AT_AT_AT right_flexible_list_SEMICOLON_noSeqTerm_ RBRACK
    {let (_1, l, _3) = ((), $2, ()) in
let t =                                                 ( l ) in
                                               ( t )}

disjunctivePattern:
  separated_nonempty_list_BAR_tuplePattern_
    {let pats = $1 in
                                                    ( pats )}

tuplePattern:
  separated_nonempty_list_COMMA_constructorPattern_
    {let pats = $1 in
      ( match pats with | [x] -> x | l -> mk_pattern (PatTuple (l, false)) (rhs parseState 1) )}

constructorPattern:
  constructorPattern COLON_COLON constructorPattern
    {let (pat, _2, pats) = ($1, (), $3) in
      ( mk_pattern (consPat (rhs parseState 3) pat pats) (rhs2 parseState 1 3) )}
| quident nonempty_list_atomicPattern_
    {let (uid, args) = ($1, $2) in
      (
        let head_pat = mk_pattern (PatName uid) (rhs parseState 1) in
        mk_pattern (PatApp (head_pat, args)) (rhs2 parseState 1 2)
      )}
| atomicPattern
    {let pat = $1 in
      ( pat )}

atomicPattern:
  LPAREN tuplePattern COLON simpleArrow refineOpt RPAREN
    {let (_1, pat, _3, t, phi_opt, _6) = ((), $2, (), $4, $5, ()) in
      (
        let pos_t = rhs2 parseState 2 4 in
        let pos = rhs2 parseState 1 6 in
        mkRefinedPattern pat t true phi_opt pos_t pos
      )}
| LBRACK loption_separated_nonempty_list_SEMICOLON_tuplePattern__ RBRACK
    {let (_1, xs, _3) = ((), $2, ()) in
let pats =     ( xs ) in
      ( mk_pattern (PatList pats) (rhs2 parseState 1 3) )}
| LBRACE right_flexible_nonempty_list_SEMICOLON_fieldPattern_ RBRACE
    {let (_1, record_pat, _3) = ((), $2, ()) in
      ( mk_pattern (PatRecord record_pat) (rhs2 parseState 1 3) )}
| LENS_PAREN_LEFT constructorPattern COMMA separated_nonempty_list_COMMA_constructorPattern_ LENS_PAREN_RIGHT
    {let (_1, pat0, _3, pats, _5) = ((), $2, (), $4, ()) in
      ( mk_pattern (PatTuple(pat0::pats, true)) (rhs2 parseState 1 5) )}
| LPAREN tuplePattern RPAREN
    {let (_1, pat, _3) = ((), $2, ()) in
                                     ( pat )}
| tvar
    {let tv = $1 in
                              ( mk_pattern (PatTvar (tv, None, [])) (rhs parseState 1) )}
| LPAREN OPPREFIX RPAREN
    {let (_1, op, _3) = ((), $2, ()) in
let op =     ( mk_ident (op, rhs parseState 1) ) in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN binop_name RPAREN
    {let (_1, op, _3) = ((), $2, ()) in
let op =     ( op ) in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN TILDE RPAREN
    {let (_1, op, _3) = ((), $2, ()) in
let op =     ( mk_ident (op, rhs parseState 1) ) in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| UNDERSCORE
    {let _1 = () in
      ( mk_pattern (PatWild (None, [])) (rhs parseState 1) )}
| HASH UNDERSCORE
    {let (_1, _2) = ((), ()) in
      ( mk_pattern (PatWild (Some Implicit, [])) (rhs parseState 1) )}
| constant
    {let c = $1 in
      ( mk_pattern (PatConst c) (rhs parseState 1) )}
| aqualifiedWithAttrs_lident_
    {let qual_id = $1 in
    (
      let (aqual, attrs), lid = qual_id in
      mk_pattern (PatVar (lid, aqual, attrs)) (rhs parseState 1) )}
| quident
    {let uid = $1 in
      ( mk_pattern (PatName uid) (rhs parseState 1) )}

fieldPattern:
  qlident EQUALS tuplePattern
    {let (x, _2, y) = ($1, (), $3) in
let p =     ( (x, y) ) in
      ( p )}
| qlident
    {let lid = $1 in
      ( lid, mk_pattern (PatVar (ident_of_lid lid, None, [])) (rhs parseState 1) )}

patternOrMultibinder:
  LBRACE_BAR UNDERSCORE COLON simpleArrow BAR_RBRACE
    {let (_1, _2, _3, t, _5) = ((), (), (), $4, ()) in
      ( let mt = mk_term (Var tcresolve_lid) (rhs parseState 4) Type_level in
        let w = mk_pattern (PatWild (Some (mk_meta_tac mt), []))
                                 (rhs2 parseState 1 5) in
        let asc = (t, None) in
        [mk_pattern (PatAscribed(w, asc)) (rhs2 parseState 1 5)]
      )}
| LBRACE_BAR lident COLON simpleArrow BAR_RBRACE
    {let (_1, i, _3, t, _5) = ((), $2, (), $4, ()) in
      ( let mt = mk_term (Var tcresolve_lid) (rhs parseState 4) Type_level in
        let w = mk_pattern (PatVar (i, Some (mk_meta_tac mt), []))
                                 (rhs2 parseState 1 5) in
        let asc = (t, None) in
        [mk_pattern (PatAscribed(w, asc)) (rhs2 parseState 1 5)]
      )}
| LBRACE_BAR simpleArrow BAR_RBRACE
    {let (_1, t, _3) = ((), $2, ()) in
      ( let mt = mk_term (Var tcresolve_lid) (rhs parseState 2) Type_level in
        let w = mk_pattern (PatVar (gen (rhs2 parseState 1 3), Some (mk_meta_tac mt), []))
                                 (rhs2 parseState 1 3) in
        let asc = (t, None) in
        [mk_pattern (PatAscribed(w, asc)) (rhs2 parseState 1 3)]
      )}
| atomicPattern
    {let pat = $1 in
                      ( [pat] )}
| LPAREN aqualifiedWithAttrs_lident_ nonempty_list_aqualifiedWithAttrs_lident__ COLON simpleArrow refineOpt RPAREN
    {let (_1, qual_id0, qual_ids, _4, t, r, _7) = ((), $2, $3, (), $5, $6, ()) in
      (
        let pos = rhs2 parseState 1 7 in
        let t_pos = rhs parseState 5 in
        let qual_ids = qual_id0 :: qual_ids in
        List.map (fun ((aq, attrs), x) -> mkRefinedPattern (mk_pattern (PatVar (x, aq, attrs)) pos) t false r t_pos pos) qual_ids
      )}

binder:
  aqualifiedWithAttrs_lidentOrUnderscore_
    {let aqualifiedWithAttrs_lid = $1 in
     (
       let (q, attrs), lid = aqualifiedWithAttrs_lid in
       mk_binder_with_attrs (Variable lid) (rhs parseState 1) Type_level q attrs
     )}
| tvar
    {let tv = $1 in
             ( mk_binder (TVariable tv) (rhs parseState 1) Kind None  )}

multiBinder:
  LBRACE_BAR lidentOrUnderscore COLON simpleArrow BAR_RBRACE
    {let (_1, id, _3, t, _5) = ((), $2, (), $4, ()) in
      ( let mt = mk_term (Var tcresolve_lid) (rhs parseState 4) Type_level in
        let r = rhs2 parseState 1 5 in
        [mk_binder (Annotated (id, t)) r Type_level (Some (mk_meta_tac mt))]
      )}
| LBRACE_BAR simpleArrow BAR_RBRACE
    {let (_1, t, _3) = ((), $2, ()) in
      ( let mt = mk_term (Var tcresolve_lid) (rhs parseState 2) Type_level in
        let r = rhs2 parseState 1 3 in
        let id = gen r in
        [mk_binder (Annotated (id, t)) r Type_level (Some (mk_meta_tac mt))]
      )}
| LPAREN nonempty_list_aqualifiedWithAttrs_lidentOrUnderscore__ COLON simpleArrow refineOpt RPAREN
    {let (_1, qual_ids, _3, t, r, _6) = ((), $2, (), $4, $5, ()) in
     (
       let should_bind_var = match qual_ids with | [ _ ] -> true | _ -> false in
       List.map (fun ((q, attrs), x) ->
         mkRefinedBinder x t should_bind_var r (rhs2 parseState 1 6) q attrs) qual_ids
     )}

binders:
  list___anonymous_4_
    {let bss = $1 in
                                                        ( flatten bss )}

aqualifiedWithAttrs_lident_:
  aqual binderAttributes lident
    {let (aq, attrs, x) = ($1, $2, $3) in
                                        ( (Some aq, attrs), x )}
| aqual lident
    {let (aq, x) = ($1, $2) in
                 ( (Some aq, []), x )}
| binderAttributes lident
    {let (attrs, x) = ($1, $2) in
                               ( (None, attrs), x )}
| lident
    {let x = $1 in
        ( (None, []), x )}

aqualifiedWithAttrs_lidentOrUnderscore_:
  aqual binderAttributes lidentOrUnderscore
    {let (aq, attrs, x) = ($1, $2, $3) in
                                        ( (Some aq, attrs), x )}
| aqual lidentOrUnderscore
    {let (aq, x) = ($1, $2) in
                 ( (Some aq, []), x )}
| binderAttributes lidentOrUnderscore
    {let (attrs, x) = ($1, $2) in
                               ( (None, attrs), x )}
| lidentOrUnderscore
    {let x = $1 in
        ( (None, []), x )}

qlident:
  path_lident_
    {let ids = $1 in
                     ( lid_of_ids ids )}

quident:
  path_uident_
    {let ids = $1 in
                     ( lid_of_ids ids )}

path_lident_:
  lident
    {let id = $1 in
          ( [id] )}
| uident DOT path_lident_
    {let (uid, _2, p) = ($1, (), $3) in
                              ( uid::p )}

path_uident_:
  uident
    {let id = $1 in
          ( [id] )}
| uident DOT path_uident_
    {let (uid, _2, p) = ($1, (), $3) in
                              ( uid::p )}

ident:
  lident
    {let x = $1 in
             ( x )}
| uident
    {let x = $1 in
              ( x )}

lidentOrOperator:
  IDENT
    {let id = $1 in
    ( mk_ident(id, rhs parseState 1) )}
| LPAREN OPPREFIX RPAREN
    {let (_1, op, _3) = ((), $2, ()) in
let id =     ( mk_ident (op, rhs parseState 1) ) in
    ( mk_ident (compile_op' (string_of_id id) (range_of_id id), range_of_id id) )}
| LPAREN binop_name RPAREN
    {let (_1, op, _3) = ((), $2, ()) in
let id =     ( op ) in
    ( mk_ident (compile_op' (string_of_id id) (range_of_id id), range_of_id id) )}
| LPAREN TILDE RPAREN
    {let (_1, op, _3) = ((), $2, ()) in
let id =     ( mk_ident (op, rhs parseState 1) ) in
    ( mk_ident (compile_op' (string_of_id id) (range_of_id id), range_of_id id) )}

lidentOrUnderscore:
  IDENT
    {let id = $1 in
             ( mk_ident(id, rhs parseState 1))}
| UNDERSCORE
    {let _1 = () in
               ( gen (rhs parseState 1) )}

lident:
  IDENT
    {let id = $1 in
             ( mk_ident(id, rhs parseState 1))}

uident:
  NAME
    {let id = $1 in
            ( mk_ident(id, rhs parseState 1) )}

tvar:
  TVAR
    {let tv = $1 in
            ( mk_ident(tv, rhs parseState 1) )}

thunk_atomicTerm_:
  atomicTerm
    {let t = $1 in
                ( mk_term (Abs ([mk_pattern (PatWild (None, [])) (rhs parseState 3)], t)) (rhs parseState 3) Expr )}

thunk_tmNoEq_:
  tmNoEq
    {let t = $1 in
                ( mk_term (Abs ([mk_pattern (PatWild (None, [])) (rhs parseState 3)], t)) (rhs parseState 3) Expr )}

thunk_typ_:
  typ
    {let t = $1 in
                ( mk_term (Abs ([mk_pattern (PatWild (None, [])) (rhs parseState 3)], t)) (rhs parseState 3) Expr )}

thunk2_typ_:
  typ
    {let t = $1 in
     ( let u = mk_term (Const Const_unit) (rhs parseState 3) Expr in
       let t = mk_term (Seq (u, t)) (rhs parseState 3) Expr in
       mk_term (Abs ([mk_pattern (PatWild (None, [])) (rhs parseState 3)], t)) (rhs parseState 3) Expr )}

ascribeTyp:
  COLON tmArrow_tmNoEq_ option___anonymous_5_
    {let (_1, t, tacopt) = ((), $2, $3) in
                                                                                ( t, tacopt )}

ascribeKind:
  COLON kind
    {let (_1, k) = ((), $2) in
                  ( k )}

kind:
  tmArrow_tmNoEq_
    {let t = $1 in
                      ( {t with level=Kind} )}

term:
  noSeqTerm
    {let e = $1 in
      ( e )}
| noSeqTerm SEMICOLON term
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Seq(e1, e2)) (rhs2 parseState 1 3) Expr )}
| noSeqTerm SEMICOLON_SEMICOLON term
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Bind(gen (rhs parseState 2), e1, e2)) (rhs2 parseState 1 3) Expr )}
| lidentOrUnderscore LONG_LEFT_ARROW noSeqTerm SEMICOLON term
    {let (x, _2, e1, _4, e2) = ($1, (), $3, (), $5) in
      ( mk_term (Bind(x, e1, e2)) (rhs2 parseState 1 5) Expr )}

match_returning:
  RETURNS tmIff
    {let (_1, t) = ((), $2) in
                    (t)}

noSeqTerm:
  typ
    {let t = $1 in
           ( t )}
| tmIff SUBTYPE tmIff option___anonymous_6_
    {let (e, _2, t, tactic_opt) = ($1, (), $3, $4) in
      ( mk_term (Ascribed(e,{t with level=Expr},tactic_opt)) (rhs2 parseState 1 4) Expr )}
| atomicTermNotQUident DOT_LPAREN term RPAREN LARROW noSeqTerm
    {let (e1, _1, e, _3_inlined1, _3, e3) = ($1, (), $3, (), (), $6) in
let op_expr =                              ( mk_ident (".()", rhs parseState 1), e, rhs2 parseState 1 3 ) in
      (
        let (op, e2, _) = op_expr in
        let opid = mk_ident (string_of_id op ^ "<-", range_of_id op) in
        mk_term (Op(opid, [ e1; e2; e3 ])) (rhs2 parseState 1 4) Expr
      )}
| atomicTermNotQUident DOT_LBRACK term RBRACK LARROW noSeqTerm
    {let (e1, _1, e, _3_inlined1, _3, e3) = ($1, (), $3, (), (), $6) in
let op_expr =                              ( mk_ident (".[]", rhs parseState 1), e, rhs2 parseState 1 3 ) in
      (
        let (op, e2, _) = op_expr in
        let opid = mk_ident (string_of_id op ^ "<-", range_of_id op) in
        mk_term (Op(opid, [ e1; e2; e3 ])) (rhs2 parseState 1 4) Expr
      )}
| atomicTermNotQUident DOT_LBRACK_BAR term BAR_RBRACK LARROW noSeqTerm
    {let (e1, _1, e, _3_inlined1, _3, e3) = ($1, (), $3, (), (), $6) in
let op_expr =                                      ( mk_ident (".[||]", rhs parseState 1), e, rhs2 parseState 1 3 ) in
      (
        let (op, e2, _) = op_expr in
        let opid = mk_ident (string_of_id op ^ "<-", range_of_id op) in
        mk_term (Op(opid, [ e1; e2; e3 ])) (rhs2 parseState 1 4) Expr
      )}
| atomicTermNotQUident DOT_LENS_PAREN_LEFT term LENS_PAREN_RIGHT LARROW noSeqTerm
    {let (e1, _1, e, _3_inlined1, _3, e3) = ($1, (), $3, (), (), $6) in
let op_expr =                                                 ( mk_ident (".(||)", rhs parseState 1), e, rhs2 parseState 1 3 ) in
      (
        let (op, e2, _) = op_expr in
        let opid = mk_ident (string_of_id op ^ "<-", range_of_id op) in
        mk_term (Op(opid, [ e1; e2; e3 ])) (rhs2 parseState 1 4) Expr
      )}
| REQUIRES typ
    {let (_1, t) = ((), $2) in
      ( mk_term (Requires(t, None)) (rhs2 parseState 1 2) Type_level )}
| ENSURES typ
    {let (_1, t) = ((), $2) in
      ( mk_term (Ensures(t, None)) (rhs2 parseState 1 2) Type_level )}
| DECREASES typ
    {let (_1, t) = ((), $2) in
      ( mk_term (Decreases (t, None)) (rhs2 parseState 1 2) Type_level )}
| ATTRIBUTES nonempty_list_atomicTerm_
    {let (_1, es) = ((), $2) in
      ( mk_term (Attributes es) (rhs2 parseState 1 2) Type_level )}
| IF noSeqTerm option_match_returning_ THEN noSeqTerm ELSE noSeqTerm
    {let (_1, e1, ret_opt, _4, e2, _6, e3) = ((), $2, $3, (), $5, (), $7) in
      ( mk_term (If(e1, ret_opt, e2, e3)) (rhs2 parseState 1 7) Expr )}
| IF noSeqTerm option_match_returning_ THEN noSeqTerm
    {let (_1, e1, ret_opt, _4, e2) = ((), $2, $3, (), $5) in
      (
        let e3 = mk_term (Const Const_unit) (rhs2 parseState 1 5) Expr in
        mk_term (If(e1, ret_opt, e2, e3)) (rhs2 parseState 1 5) Expr
      )}
| TRY term WITH reverse_left_flexible_nonempty_list_BAR_patternBranch_
    {let (_1, e1, _3, xs) = ((), $2, (), $4) in
let pbs =    ( List.rev xs ) in
      (
         let branches = focusBranches (pbs) (rhs2 parseState 1 4) in
         mk_term (TryWith(e1, branches)) (rhs2 parseState 1 4) Expr
      )}
| MATCH term option_match_returning_ WITH reverse_left_flexible_list_BAR___anonymous_7_
    {let (_1, e, ret_opt, _4, xs) = ((), $2, $3, (), $5) in
let pbs =    ( List.rev xs ) in
      (
        let branches = focusBranches pbs (rhs2 parseState 1 5) in
        mk_term (Match(e, ret_opt, branches)) (rhs2 parseState 1 5) Expr
      )}
| LET OPEN term IN term
    {let (_1, _2, t, _4, e) = ($1, (), $3, (), $5) in
      (
            match t.tm with
            | Ascribed(r, rty, None) ->
              mk_term (LetOpenRecord(r, rty, e)) (rhs2 parseState 1 5) Expr

            | Name uid ->
              mk_term (LetOpen(uid, e)) (rhs2 parseState 1 5) Expr

            | _ ->
              raise_error (Fatal_SyntaxError, "Syntax error: local opens expects either opening\n\
                                               a module or namespace using `let open T in e`\n\
                                               or, a record type with `let open e <: t in e'`")
                          (rhs parseState 3)
      )}
| LET letqualifier letbinding list_attr_letbinding_ IN term
    {let (_2, q, lb, lbs, _6, e) = ($1, $2, $3, $4, (), $6) in
let attrs =     ( None ) in
      (
        let lbs = (attrs, lb)::lbs in
        let lbs = focusAttrLetBindings lbs (rhs2 parseState 2 3) in
        mk_term (Let(q, lbs, e)) (rhs2 parseState 1 6) Expr
      )}
| attribute LET letqualifier letbinding list_attr_letbinding_ IN term
    {let (x, _2, q, lb, lbs, _6, e) = ($1, $2, $3, $4, $5, (), $7) in
let attrs =     ( Some x ) in
      (
        let lbs = (attrs, lb)::lbs in
        let lbs = focusAttrLetBindings lbs (rhs2 parseState 2 3) in
        mk_term (Let(q, lbs, e)) (rhs2 parseState 1 6) Expr
      )}
| FUNCTION reverse_left_flexible_nonempty_list_BAR_patternBranch_
    {let (_1, xs) = ((), $2) in
let pbs =    ( List.rev xs ) in
      (
        let branches = focusBranches pbs (rhs2 parseState 1 2) in
        mk_function branches (lhs parseState) (rhs2 parseState 1 2)
      )}
| ASSUME atomicTerm
    {let (_1, e) = ((), $2) in
      ( let a = set_lid_range assume_lid (rhs parseState 1) in
        mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [e] (rhs2 parseState 1 2)
      )}
| ASSERT atomicTerm option___anonymous_8_
    {let (_1, e, tactic_opt) = ((), $2, $3) in
      (
        match tactic_opt with
        | None ->
          let a = set_lid_range assert_lid (rhs parseState 1) in
          mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [e] (rhs2 parseState 1 2)
        | Some tac ->
          let a = set_lid_range assert_by_tactic_lid (rhs parseState 1) in
          mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [e; tac] (rhs2 parseState 1 4)
      )}
| UNDERSCORE BY thunk_atomicTerm_
    {let (_1, _2, tactic) = ((), (), $3) in
     (
         let a = set_lid_range synth_lid (rhs parseState 1) in
         mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [tactic] (rhs2 parseState 1 2)
     )}
| SYNTH atomicTerm
    {let (_1, tactic) = ((), $2) in
     (
         let a = set_lid_range synth_lid (rhs parseState 1) in
         mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [tactic] (rhs2 parseState 1 2)
     )}
| CALC atomicTerm LBRACE noSeqTerm SEMICOLON list_calcStep_ RBRACE
    {let (_1, rel, _3, init, _5, steps, _7) = ((), $2, (), $4, (), $6, ()) in
     (
         mk_term (CalcProof (rel, init, steps)) (rhs2 parseState 1 7) Expr
     )}

calcRel:
  binop_name
    {let i = $1 in
                 ( mk_term (Op (i, [])) (rhs parseState 1) Expr )}
| BACKTICK qlident BACKTICK
    {let (_1, id, _3) = ((), $2, ()) in
                                 ( mk_term (Var id) (rhs2 parseState 2 4) Un )}
| atomicTerm
    {let t = $1 in
                 ( t )}

calcStep:
  calcRel LBRACE option_term_ RBRACE noSeqTerm SEMICOLON
    {let (rel, _2, justif, _4, next, _6) = ($1, (), $3, (), $5, ()) in
     (
         let justif =
             match justif with
             | Some t -> t
             | None -> mk_term (Const Const_unit) (rhs2 parseState 2 4) Expr
         in
         CalcStep (rel, justif, next)
     )}

typ:
  simpleTerm
    {let t = $1 in
                 ( t )}
| FORALL binders DOT trigger noSeqTerm
    {let (_1, bs, _3, trigger, e) = ((), $2, (), $4, $5) in
let q =            ( fun x -> QForall x ) in
      (
        match bs with
        | [] ->
          raise_error (Fatal_MissingQuantifierBinder, "Missing binders for a quantifier") (rhs2 parseState 1 3)
        | _ ->
          let idents = idents_of_binders bs (rhs2 parseState 1 3) in
          mk_term (q (bs, (idents, trigger), e)) (rhs2 parseState 1 5) Formula
      )}
| EXISTS binders DOT trigger noSeqTerm
    {let (_1, bs, _3, trigger, e) = ((), $2, (), $4, $5) in
let q =            ( fun x -> QExists x) in
      (
        match bs with
        | [] ->
          raise_error (Fatal_MissingQuantifierBinder, "Missing binders for a quantifier") (rhs2 parseState 1 3)
        | _ ->
          let idents = idents_of_binders bs (rhs2 parseState 1 3) in
          mk_term (q (bs, (idents, trigger), e)) (rhs2 parseState 1 5) Formula
      )}

trigger:
  
    {      ( [] )}
| LBRACE_COLON_PATTERN disjunctivePats RBRACE
    {let (_1, pats, _3) = ((), $2, ()) in
                                                     ( pats )}

disjunctivePats:
  separated_nonempty_list_DISJUNCTION_conjunctivePat_
    {let pats = $1 in
                                                              ( pats )}

conjunctivePat:
  separated_nonempty_list_SEMICOLON_appTerm_
    {let pats = $1 in
                                                              ( pats )}

simpleTerm:
  tmIff
    {let e = $1 in
            ( e )}
| FUN nonempty_list_patternOrMultibinder_ RARROW term
    {let (_1, pats, _3, e) = ((), $2, (), $4) in
      ( mk_term (Abs(flatten pats, e)) (rhs2 parseState 1 4) Un )}

maybeFocusArrow:
  RARROW
    {let _1 = () in
                    ( false )}
| SQUIGGLY_RARROW
    {let _1 = () in
                    ( true )}

patternBranch:
  disjunctivePattern maybeFocusArrow term
    {let (pat, focus, e) = ($1, $2, $3) in
let when_opt =                          ( None ) in
      (
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 1)
        in
        (focus, (pat, when_opt, e))
      )}
| disjunctivePattern WHEN tmFormula maybeFocusArrow term
    {let (pat, _1, e_inlined1, focus, e) = ($1, (), $3, $4, $5) in
let when_opt =
  let e = e_inlined1 in
                           ( Some e )
in
      (
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 1)
        in
        (focus, (pat, when_opt, e))
      )}

tmIff:
  tmImplies IFF tmIff
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("<==>", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Formula )}
| tmImplies
    {let e = $1 in
                ( e )}

tmImplies:
  tmArrow_tmFormula_ IMPLIES tmImplies
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("==>", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Formula )}
| tmArrow_tmFormula_
    {let e = $1 in
      ( e )}

tmArrow_tmFormula_:
  LBRACE_BAR tmFormula BAR_RBRACE RARROW tmArrow_tmFormula_
    {let (_1, t, _3, _2, tgt) = ((), $2, (), (), $5) in
let dom =       ( let mt = mk_term (Var tcresolve_lid) (rhs parseState 4) Type_level in
        ((Some (mk_meta_tac mt), []), t)
      ) in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| LPAREN aqual tmFormula RPAREN RARROW tmArrow_tmFormula_
    {let (_1, q, dom_tm, _5, _2, tgt) = ((), $2, $3, (), (), $6) in
let dom =
  let attrs_opt =     ( None ) in
                                                                          ( (Some q, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| LPAREN aqual binderAttributes tmFormula RPAREN RARROW tmArrow_tmFormula_
    {let (_1, q, x, dom_tm, _5, _2, tgt) = ((), $2, $3, $4, (), (), $7) in
let dom =
  let attrs_opt =     ( Some x ) in
                                                                          ( (Some q, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| tmFormula RARROW tmArrow_tmFormula_
    {let (dom_tm, _2, tgt) = ($1, (), $3) in
let dom =
  let attrs_opt =     ( None ) in
  let aq_opt =     ( None ) in
                                                                          ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| binderAttributes tmFormula RARROW tmArrow_tmFormula_
    {let (x, dom_tm, _2, tgt) = ($1, $2, (), $4) in
let dom =
  let attrs_opt =     ( Some x ) in
  let aq_opt =     ( None ) in
                                                                          ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| aqual tmFormula RARROW tmArrow_tmFormula_
    {let (x, dom_tm, _2, tgt) = ($1, $2, (), $4) in
let dom =
  let attrs_opt =     ( None ) in
  let aq_opt =     ( Some x ) in
                                                                          ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| aqual binderAttributes tmFormula RARROW tmArrow_tmFormula_
    {let (x, x_inlined1, dom_tm, _2, tgt) = ($1, $2, $3, (), $5) in
let dom =
  let attrs_opt =
    let x = x_inlined1 in
        ( Some x )
  in
  let aq_opt =     ( Some x ) in
                                                                          ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| tmFormula
    {let e = $1 in
         ( e )}

tmArrow_tmNoEq_:
  LBRACE_BAR tmNoEq BAR_RBRACE RARROW tmArrow_tmNoEq_
    {let (_1, t, _3, _2, tgt) = ((), $2, (), (), $5) in
let dom =       ( let mt = mk_term (Var tcresolve_lid) (rhs parseState 4) Type_level in
        ((Some (mk_meta_tac mt), []), t)
      ) in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| LPAREN aqual tmNoEq RPAREN RARROW tmArrow_tmNoEq_
    {let (_1, q, dom_tm, _5, _2, tgt) = ((), $2, $3, (), (), $6) in
let dom =
  let attrs_opt =     ( None ) in
                                                                          ( (Some q, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| LPAREN aqual binderAttributes tmNoEq RPAREN RARROW tmArrow_tmNoEq_
    {let (_1, q, x, dom_tm, _5, _2, tgt) = ((), $2, $3, $4, (), (), $7) in
let dom =
  let attrs_opt =     ( Some x ) in
                                                                          ( (Some q, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| tmNoEq RARROW tmArrow_tmNoEq_
    {let (dom_tm, _2, tgt) = ($1, (), $3) in
let dom =
  let attrs_opt =     ( None ) in
  let aq_opt =     ( None ) in
                                                                          ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| binderAttributes tmNoEq RARROW tmArrow_tmNoEq_
    {let (x, dom_tm, _2, tgt) = ($1, $2, (), $4) in
let dom =
  let attrs_opt =     ( Some x ) in
  let aq_opt =     ( None ) in
                                                                          ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| aqual tmNoEq RARROW tmArrow_tmNoEq_
    {let (x, dom_tm, _2, tgt) = ($1, $2, (), $4) in
let dom =
  let attrs_opt =     ( None ) in
  let aq_opt =     ( Some x ) in
                                                                          ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| aqual binderAttributes tmNoEq RARROW tmArrow_tmNoEq_
    {let (x, x_inlined1, dom_tm, _2, tgt) = ($1, $2, $3, (), $5) in
let dom =
  let attrs_opt =
    let x = x_inlined1 in
        ( Some x )
  in
  let aq_opt =     ( Some x ) in
                                                                          ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )
in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| tmNoEq
    {let e = $1 in
         ( e )}

simpleArrow:
  simpleArrowDomain RARROW simpleArrow
    {let (dom, _2, tgt) = ($1, (), $3) in
     (
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| tmEqNoRefinement
    {let e = $1 in
                       ( e )}

simpleArrowDomain:
  LBRACE_BAR tmEqNoRefinement BAR_RBRACE
    {let (_1, t, _3) = ((), $2, ()) in
      ( let mt = mk_term (Var tcresolve_lid) (rhs parseState 4) Type_level in
        ((Some (mk_meta_tac mt), []), t)
      )}
| tmEqNoRefinement
    {let dom_tm = $1 in
let attrs_opt =     ( None ) in
let aq_opt =     ( None ) in
                                                                                      ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )}
| binderAttributes tmEqNoRefinement
    {let (x, dom_tm) = ($1, $2) in
let attrs_opt =     ( Some x ) in
let aq_opt =     ( None ) in
                                                                                      ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )}
| aqual tmEqNoRefinement
    {let (x, dom_tm) = ($1, $2) in
let attrs_opt =     ( None ) in
let aq_opt =     ( Some x ) in
                                                                                      ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )}
| aqual binderAttributes tmEqNoRefinement
    {let (x, x_inlined1, dom_tm) = ($1, $2, $3) in
let attrs_opt =
  let x = x_inlined1 in
      ( Some x )
in
let aq_opt =     ( Some x ) in
                                                                                      ( (aq_opt, none_to_empty_list attrs_opt), dom_tm )}

tmFormula:
  tmFormula DISJUNCTION tmConjunction
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("\\/", rhs parseState 2), [e1;e2])) (rhs2 parseState 1 3) Formula )}
| tmConjunction
    {let e = $1 in
                    ( e )}

tmConjunction:
  tmConjunction CONJUNCTION tmTuple
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("/\\", rhs parseState 2), [e1;e2])) (rhs2 parseState 1 3) Formula )}
| tmTuple
    {let e = $1 in
              ( e )}

tmTuple:
  separated_nonempty_list_COMMA_tmEq_
    {let el = $1 in
      (
        match el with
          | [x] -> x
          | components -> mkTuple components (rhs2 parseState 1 1)
      )}

tmEqWith_appTerm_:
  tmEqWith_appTerm_ EQUALS tmEqWith_appTerm_
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("=", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_appTerm_ COLON_EQUALS tmEqWith_appTerm_
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident(":=", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_appTerm_ PIPE_RIGHT tmEqWith_appTerm_
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("|>", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_appTerm_ OPINFIX0a tmEqWith_appTerm_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_appTerm_ OPINFIX0b tmEqWith_appTerm_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_appTerm_ OPINFIX0c tmEqWith_appTerm_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_appTerm_ OPINFIX0d tmEqWith_appTerm_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_appTerm_ OPINFIX1 tmEqWith_appTerm_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_appTerm_ OPINFIX2 tmEqWith_appTerm_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_appTerm_ MINUS tmEqWith_appTerm_
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("-", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| MINUS tmEqWith_appTerm_
    {let (_1, e) = ((), $2) in
      ( mk_uminus e (rhs parseState 1) (rhs2 parseState 1 2) Expr )}
| QUOTE tmEqWith_appTerm_
    {let (_1, e) = ((), $2) in
      ( mk_term (Quote (e, Dynamic)) (rhs2 parseState 1 3) Un )}
| BACKTICK tmEqWith_appTerm_
    {let (_1, e) = ((), $2) in
      ( mk_term (Quote (e, Static)) (rhs2 parseState 1 3) Un )}
| BACKTICK_AT atomicTerm
    {let (_1, e) = ((), $2) in
      ( let q = mk_term (Quote (e, Dynamic)) (rhs2 parseState 1 3) Un in
        mk_term (Antiquote q) (rhs2 parseState 1 3) Un )}
| BACKTICK_HASH atomicTerm
    {let (_1, e) = ((), $2) in
      ( mk_term (Antiquote e) (rhs2 parseState 1 3) Un )}
| tmNoEqWith_appTerm_
    {let e = $1 in
      ( e )}

tmEqWith_tmRefinement_:
  tmEqWith_tmRefinement_ EQUALS tmEqWith_tmRefinement_
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("=", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_tmRefinement_ COLON_EQUALS tmEqWith_tmRefinement_
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident(":=", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_tmRefinement_ PIPE_RIGHT tmEqWith_tmRefinement_
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("|>", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_tmRefinement_ OPINFIX0a tmEqWith_tmRefinement_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_tmRefinement_ OPINFIX0b tmEqWith_tmRefinement_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_tmRefinement_ OPINFIX0c tmEqWith_tmRefinement_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_tmRefinement_ OPINFIX0d tmEqWith_tmRefinement_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_tmRefinement_ OPINFIX1 tmEqWith_tmRefinement_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_tmRefinement_ OPINFIX2 tmEqWith_tmRefinement_
    {let (e1, op, e2) = ($1, $2, $3) in
let op =      ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEqWith_tmRefinement_ MINUS tmEqWith_tmRefinement_
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("-", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| MINUS tmEqWith_tmRefinement_
    {let (_1, e) = ((), $2) in
      ( mk_uminus e (rhs parseState 1) (rhs2 parseState 1 2) Expr )}
| QUOTE tmEqWith_tmRefinement_
    {let (_1, e) = ((), $2) in
      ( mk_term (Quote (e, Dynamic)) (rhs2 parseState 1 3) Un )}
| BACKTICK tmEqWith_tmRefinement_
    {let (_1, e) = ((), $2) in
      ( mk_term (Quote (e, Static)) (rhs2 parseState 1 3) Un )}
| BACKTICK_AT atomicTerm
    {let (_1, e) = ((), $2) in
      ( let q = mk_term (Quote (e, Dynamic)) (rhs2 parseState 1 3) Un in
        mk_term (Antiquote q) (rhs2 parseState 1 3) Un )}
| BACKTICK_HASH atomicTerm
    {let (_1, e) = ((), $2) in
      ( mk_term (Antiquote e) (rhs2 parseState 1 3) Un )}
| tmNoEqWith_tmRefinement_
    {let e = $1 in
      ( e )}

tmNoEqWith_appTerm_:
  tmNoEqWith_appTerm_ COLON_COLON tmNoEqWith_appTerm_
    {let (e1, _2, e2) = ($1, (), $3) in
      ( consTerm (rhs parseState 2) e1 e2 )}
| tmNoEqWith_appTerm_ AMP tmNoEqWith_appTerm_
    {let (e1, _2, e2) = ($1, (), $3) in
      (
            let dom =
               match extract_named_refinement e1 with
               | Some (x, t, f) ->
                 let dom = mkRefinedBinder x t true f (rhs parseState 1) None [] in
                 Inl dom
               | _ ->
                 Inr e1
            in
            let tail = e2 in
            let dom, res =
                match tail.tm with
                | Sum(dom', res) -> dom::dom', res
                | _ -> [dom], tail
            in
            mk_term (Sum(dom, res)) (rhs2 parseState 1 3) Type_level
      )}
| tmNoEqWith_appTerm_ OPINFIX3 tmNoEqWith_appTerm_
    {let (e1, op, e2) = ($1, $2, $3) in
      ( mk_term (Op(mk_ident(op, rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmNoEqWith_appTerm_ BACKTICK tmNoEqWith_appTerm_ BACKTICK tmNoEqWith_appTerm_
    {let (e1, _2, op, _4, e2) = ($1, (), $3, (), $5) in
      ( mkApp op [ e1, Infix; e2, Nothing ] (rhs2 parseState 1 5) )}
| tmNoEqWith_appTerm_ OPINFIX4 tmNoEqWith_appTerm_
    {let (e1, op, e2) = ($1, $2, $3) in
      ( mk_term (Op(mk_ident(op, rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| LBRACE recordExp RBRACE
    {let (_1, e, _3) = ((), $2, ()) in
                              ( e )}
| BACKTICK_PERC atomicTerm
    {let (_1, e) = ((), $2) in
      ( mk_term (VQuote e) (rhs2 parseState 1 3) Un )}
| TILDE atomicTerm
    {let (op, e) = ($1, $2) in
      ( mk_term (Op(mk_ident (op, rhs parseState 1), [e])) (rhs2 parseState 1 2) Formula )}
| appTerm
    {let e = $1 in
        ( e )}

tmNoEqWith_tmRefinement_:
  tmNoEqWith_tmRefinement_ COLON_COLON tmNoEqWith_tmRefinement_
    {let (e1, _2, e2) = ($1, (), $3) in
      ( consTerm (rhs parseState 2) e1 e2 )}
| tmNoEqWith_tmRefinement_ AMP tmNoEqWith_tmRefinement_
    {let (e1, _2, e2) = ($1, (), $3) in
      (
            let dom =
               match extract_named_refinement e1 with
               | Some (x, t, f) ->
                 let dom = mkRefinedBinder x t true f (rhs parseState 1) None [] in
                 Inl dom
               | _ ->
                 Inr e1
            in
            let tail = e2 in
            let dom, res =
                match tail.tm with
                | Sum(dom', res) -> dom::dom', res
                | _ -> [dom], tail
            in
            mk_term (Sum(dom, res)) (rhs2 parseState 1 3) Type_level
      )}
| tmNoEqWith_tmRefinement_ OPINFIX3 tmNoEqWith_tmRefinement_
    {let (e1, op, e2) = ($1, $2, $3) in
      ( mk_term (Op(mk_ident(op, rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmNoEqWith_tmRefinement_ BACKTICK tmNoEqWith_tmRefinement_ BACKTICK tmNoEqWith_tmRefinement_
    {let (e1, _2, op, _4, e2) = ($1, (), $3, (), $5) in
      ( mkApp op [ e1, Infix; e2, Nothing ] (rhs2 parseState 1 5) )}
| tmNoEqWith_tmRefinement_ OPINFIX4 tmNoEqWith_tmRefinement_
    {let (e1, op, e2) = ($1, $2, $3) in
      ( mk_term (Op(mk_ident(op, rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| LBRACE recordExp RBRACE
    {let (_1, e, _3) = ((), $2, ()) in
                              ( e )}
| BACKTICK_PERC atomicTerm
    {let (_1, e) = ((), $2) in
      ( mk_term (VQuote e) (rhs2 parseState 1 3) Un )}
| TILDE atomicTerm
    {let (op, e) = ($1, $2) in
      ( mk_term (Op(mk_ident (op, rhs parseState 1), [e])) (rhs2 parseState 1 2) Formula )}
| tmRefinement
    {let e = $1 in
        ( e )}

binop_name:
  OPINFIX0a
    {let o = $1 in
                             ( mk_ident (o, rhs parseState 1) )}
| OPINFIX0b
    {let o = $1 in
                             ( mk_ident (o, rhs parseState 1) )}
| OPINFIX0c
    {let o = $1 in
                             ( mk_ident (o, rhs parseState 1) )}
| EQUALS
    {let o = () in
                             ( mk_ident ("=", rhs parseState 1) )}
| OPINFIX0d
    {let o = $1 in
                             ( mk_ident (o, rhs parseState 1) )}
| OPINFIX1
    {let o = $1 in
                             ( mk_ident (o, rhs parseState 1) )}
| OPINFIX2
    {let o = $1 in
                             ( mk_ident (o, rhs parseState 1) )}
| OPINFIX3
    {let o = $1 in
                             ( mk_ident (o, rhs parseState 1) )}
| OPINFIX4
    {let o = $1 in
                             ( mk_ident (o, rhs parseState 1) )}
| IMPLIES
    {let o = () in
                             ( mk_ident ("==>", rhs parseState 1) )}
| CONJUNCTION
    {let o = () in
                             ( mk_ident ("/\\", rhs parseState 1) )}
| DISJUNCTION
    {let o = () in
                             ( mk_ident ("\\/", rhs parseState 1) )}
| IFF
    {let o = () in
                             ( mk_ident ("<==>", rhs parseState 1) )}
| PIPE_RIGHT
    {let o = () in
                             ( mk_ident ("|>", rhs parseState 1) )}
| COLON_EQUALS
    {let o = () in
                             ( mk_ident (":=", rhs parseState 1) )}
| COLON_COLON
    {let o = () in
                             ( mk_ident ("::", rhs parseState 1) )}
| OP_MIXFIX_ASSIGNMENT
    {let o = $1 in
                             ( mk_ident (o, rhs parseState 1) )}
| OP_MIXFIX_ACCESS
    {let o = $1 in
                             ( mk_ident (o, rhs parseState 1) )}

tmEqNoRefinement:
  tmEqWith_appTerm_
    {let e = $1 in
                        ( e )}

tmEq:
  tmEqWith_tmRefinement_
    {let e = $1 in
                              ( e )}

tmNoEq:
  tmNoEqWith_tmRefinement_
    {let e = $1 in
                               ( e )}

tmRefinement:
  lidentOrUnderscore COLON appTerm refineOpt
    {let (id, _2, e, phi_opt) = ($1, (), $3, $4) in
      (
        let t = match phi_opt with
          | None -> NamedTyp(id, e)
          | Some phi -> Refine(mk_binder (Annotated(id, e)) (rhs2 parseState 1 3) Type_level None, phi)
        in mk_term t (rhs2 parseState 1 4) Type_level
      )}
| appTerm
    {let e = $1 in
               ( e )}

refineOpt:
  option___anonymous_9_
    {let phi_opt = $1 in
                                                    (phi_opt)}

recordExp:
  right_flexible_nonempty_list_SEMICOLON_simpleDef_
    {let record_fields = $1 in
      ( mk_term (Record (None, record_fields)) (rhs parseState 1) Expr )}
| appTerm WITH right_flexible_nonempty_list_SEMICOLON_simpleDef_
    {let (e, _2, record_fields) = ($1, (), $3) in
      ( mk_term (Record (Some e, record_fields)) (rhs2 parseState 1 3) Expr )}

simpleDef:
  qlident EQUALS noSeqTerm
    {let (x, _2, y) = ($1, (), $3) in
let e =     ( (x, y) ) in
                                                 ( e )}
| qlident
    {let lid = $1 in
                ( lid, mk_term (Name (lid_of_ids [ ident_of_lid lid ])) (rhs parseState 1) Un )}

appTerm:
  indexingTerm list_argTerm_
    {let (head, args) = ($1, $2) in
      ( mkApp head (map (fun (x,y) -> (y,x)) args) (rhs2 parseState 1 2) )}

argTerm:
  indexingTerm
    {let y = $1 in
let x =
  let x =          ( Nothing ) in
      ( (x, y) )
in
                                    ( x )}
| HASH indexingTerm
    {let (_1, y) = ((), $2) in
let x =
  let x =          ( Hash ) in
      ( (x, y) )
in
                                    ( x )}
| universe
    {let u = $1 in
               ( u )}

indexingTerm:
  atomicTermNotQUident nonempty_list_dotOperator_
    {let (e1, op_exprs) = ($1, $2) in
      (
        List.fold_left (fun e1 (op, e2, r) ->
            mk_term (Op(op, [ e1; e2 ])) (union_ranges e1.range r) Expr)
            e1 op_exprs
      )}
| atomicTerm
    {let e = $1 in
    ( e )}

atomicTerm:
  atomicTermNotQUident
    {let x = $1 in
    ( x )}
| atomicTermQUident
    {let x = $1 in
    ( x )}
| opPrefixTerm_atomicTermQUident_
    {let x = $1 in
    ( x )}

atomicTermQUident:
  quident
    {let id = $1 in
    (
        let t = Name id in
        let e = mk_term t (rhs parseState 1) Un in
              e
    )}
| quident DOT_LPAREN term RPAREN
    {let (id, _2, t, _4) = ($1, (), $3, ()) in
    (
      mk_term (LetOpen (id, t)) (rhs2 parseState 1 4) Expr
    )}

atomicTermNotQUident:
  UNDERSCORE
    {let _1 = () in
               ( mk_term Wild (rhs parseState 1) Un )}
| tvar
    {let tv = $1 in
                ( mk_term (Tvar tv) (rhs parseState 1) Type_level )}
| constant
    {let c = $1 in
               ( mk_term (Const c) (rhs parseState 1) Expr )}
| opPrefixTerm_atomicTermNotQUident_
    {let x = $1 in
    ( x )}
| LPAREN OPPREFIX RPAREN
    {let (_1, op, _3) = ((), $2, ()) in
let op =     ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN binop_name RPAREN
    {let (_1, op, _3) = ((), $2, ()) in
let op =     ( op ) in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN TILDE RPAREN
    {let (_1, op, _3) = ((), $2, ()) in
let op =     ( mk_ident (op, rhs parseState 1) ) in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LENS_PAREN_LEFT tmEq COMMA separated_nonempty_list_COMMA_tmEq_ LENS_PAREN_RIGHT
    {let (_1, e0, _3, el, _5) = ((), $2, (), $4, ()) in
      ( mkDTuple (e0::el) (rhs2 parseState 1 5) )}
| projectionLHS list___anonymous_10_
    {let (e, field_projs) = ($1, $2) in
      ( fold_left (fun e lid -> mk_term (Project(e, lid)) (rhs2 parseState 1 2) Expr ) e field_projs )}
| BEGIN term END
    {let (_1, e, _3) = ((), $2, ()) in
      ( e )}

opPrefixTerm_atomicTermNotQUident_:
  OPPREFIX atomicTermNotQUident
    {let (op, e) = ($1, $2) in
      ( mk_term (Op(mk_ident(op, rhs parseState 1), [e])) (rhs2 parseState 1 2) Expr )}

opPrefixTerm_atomicTermQUident_:
  OPPREFIX atomicTermQUident
    {let (op, e) = ($1, $2) in
      ( mk_term (Op(mk_ident(op, rhs parseState 1), [e])) (rhs2 parseState 1 2) Expr )}

projectionLHS:
  qidentWithTypeArgs_qlident_option_fsTypeArgs__
    {let e = $1 in
      ( e )}
| qidentWithTypeArgs_quident_some_fsTypeArgs__
    {let e = $1 in
      ( e )}
| LPAREN term option_pair_hasSort_simpleTerm__ RPAREN
    {let (_1, e, sort_opt, _4) = ((), $2, $3, ()) in
      (
        (* Note: we have to keep the parentheses here. Consider t * u * v. This
         * is parsed as Op2( *, Op2( *, t, u), v). The desugaring phase then looks
         * up * and figures out that it hasn't been overridden, meaning that
         * it's a tuple type, and proceeds to flatten out the whole tuple. Now
         * consider (t * u) * v. We keep the Paren node, which prevents the
         * flattening from happening, hence ensuring the proper type is
         * generated. *)
        let e1 = match sort_opt with
          | None -> e
          | Some (level, t) -> mk_term (Ascribed(e,{t with level=level},None)) (rhs2 parseState 1 4) level
        in mk_term (Paren e1) (rhs2 parseState 1 4) (e.level)
      )}
| LBRACK_BAR right_flexible_list_SEMICOLON_noSeqTerm_ BAR_RBRACK
    {let (_1, l, _3) = ((), $2, ()) in
let es =                                                 ( l ) in
      (
        let l = mkConsList (rhs2 parseState 1 3) es in
        let pos = (rhs2 parseState 1 3) in
        mkExplicitApp (mk_term (Var (array_of_list_lid)) pos Expr) [l] pos
      )}
| LBRACK right_flexible_list_SEMICOLON_noSeqTerm_ RBRACK
    {let (_1, l, _3) = ((), $2, ()) in
let es =                                                 ( l ) in
      ( mkConsList (rhs2 parseState 1 3) es )}
| PERCENT_LBRACK right_flexible_list_SEMICOLON_noSeqTerm_ RBRACK
    {let (_1, l, _3) = ((), $2, ()) in
let es =                                                 ( l ) in
      ( mk_term (LexList es) (rhs2 parseState 1 3) Type_level )}
| BANG_LBRACE loption_separated_nonempty_list_COMMA_appTerm__ RBRACE
    {let (_1, xs, _3) = ((), $2, ()) in
let es =     ( xs ) in
      ( mkRefSet (rhs2 parseState 1 3) es )}
| quident QMARK_DOT lident
    {let (ns, _2, id) = ($1, (), $3) in
      ( mk_term (Projector (ns, id)) (rhs2 parseState 1 3) Expr )}
| quident QMARK
    {let (lid, _2) = ($1, ()) in
      ( mk_term (Discrim lid) (rhs2 parseState 1 2) Un )}

fsTypeArgs:
  TYP_APP_LESS separated_nonempty_list_COMMA_atomicTerm_ TYP_APP_GREATER
    {let (_1, targs, _3) = ((), $2, ()) in
    (targs)}

qidentWithTypeArgs_qlident_option_fsTypeArgs__:
  qlident option_fsTypeArgs_
    {let (id, targs_opt) = ($1, $2) in
      (
        let t = if is_name id then Name id else Var id in
        let e = mk_term t (rhs parseState 1) Un in
        match targs_opt with
        | None -> e
        | Some targs -> mkFsTypApp e targs (rhs2 parseState 1 2)
      )}

qidentWithTypeArgs_quident_some_fsTypeArgs__:
  quident some_fsTypeArgs_
    {let (id, targs_opt) = ($1, $2) in
      (
        let t = if is_name id then Name id else Var id in
        let e = mk_term t (rhs parseState 1) Un in
        match targs_opt with
        | None -> e
        | Some targs -> mkFsTypApp e targs (rhs2 parseState 1 2)
      )}

hasSort:
  SUBKIND
    {let _1 = () in
            ( Type_level )}

constant:
  LPAREN_RPAREN
    {let _1 = () in
                  ( Const_unit )}
| INT
    {let n = $1 in
     (
        if snd n then
          log_issue (lhs parseState) (Error_OutOfRange, "This number is outside the allowable range for representable integer constants");
        Const_int (fst n, None)
     )}
| CHAR
    {let c = $1 in
           ( Const_char c )}
| STRING
    {let s = $1 in
             ( Const_string (s,lhs(parseState)) )}
| BYTEARRAY
    {let bs = $1 in
                 ( Const_bytearray (bs,lhs(parseState)) )}
| TRUE
    {let _1 = () in
         ( Const_bool true )}
| FALSE
    {let _1 = () in
          ( Const_bool false )}
| REAL
    {let r = $1 in
           ( Const_real r )}
| IEEE64
    {let f = $1 in
             ( Const_float f )}
| UINT8
    {let n = $1 in
            ( Const_int (n, Some (Unsigned, Int8)) )}
| INT8
    {let n = $1 in
      (
        if snd n then
          log_issue (lhs(parseState)) (Error_OutOfRange, "This number is outside the allowable range for 8-bit signed integers");
        Const_int (fst n, Some (Signed, Int8))
      )}
| UINT16
    {let n = $1 in
             ( Const_int (n, Some (Unsigned, Int16)) )}
| INT16
    {let n = $1 in
      (
        if snd n then
          log_issue (lhs(parseState)) (Error_OutOfRange, "This number is outside the allowable range for 16-bit signed integers");
        Const_int (fst n, Some (Signed, Int16))
      )}
| UINT32
    {let n = $1 in
             ( Const_int (n, Some (Unsigned, Int32)) )}
| INT32
    {let n = $1 in
      (
        if snd n then
          log_issue (lhs(parseState)) (Error_OutOfRange, "This number is outside the allowable range for 32-bit signed integers");
        Const_int (fst n, Some (Signed, Int32))
      )}
| UINT64
    {let n = $1 in
             ( Const_int (n, Some (Unsigned, Int64)) )}
| INT64
    {let n = $1 in
      (
        if snd n then
          log_issue (lhs(parseState)) (Error_OutOfRange, "This number is outside the allowable range for 64-bit signed integers");
        Const_int (fst n, Some (Signed, Int64))
      )}
| REIFY
    {let _1 = () in
            ( Const_reify )}
| RANGE_OF
    {let _1 = () in
                 ( Const_range_of )}
| SET_RANGE_OF
    {let _1 = () in
                 ( Const_set_range_of )}

universe:
  UNIV_HASH atomicUniverse
    {let (_1, ua) = ((), $2) in
                                ( (UnivApp, ua) )}

universeFrom:
  atomicUniverse
    {let ua = $1 in
                      ( ua )}
| universeFrom OPINFIX2 universeFrom
    {let (u1, op_plus, u2) = ($1, $2, $3) in
       (
         if op_plus <> "+"
         then log_issue (rhs parseState 2) (Error_OpPlusInUniverse, ("The operator " ^ op_plus ^ " was found in universe context."
                           ^ "The only allowed operator in that context is +."));
         mk_term (Op(mk_ident (op_plus, rhs parseState 2), [u1 ; u2])) (rhs2 parseState 1 3) Expr
       )}
| ident nonempty_list_atomicUniverse_
    {let (max, us) = ($1, $2) in
      (
        if string_of_id max <> string_of_lid max_lid
        then log_issue (rhs parseState 1) (Error_InvalidUniverseVar, "A lower case ident " ^ string_of_id max ^
                          " was found in a universe context. " ^
                          "It should be either max or a universe variable 'usomething.");
        let max = mk_term (Var (lid_of_ids [max])) (rhs parseState 1) Expr in
        mkApp max (map (fun u -> u, Nothing) us) (rhs2 parseState 1 2)
      )}

atomicUniverse:
  UNDERSCORE
    {let _1 = () in
      ( mk_term Wild (rhs parseState 1) Expr )}
| INT
    {let n = $1 in
      (
        if snd n then
          log_issue (lhs(parseState)) (Error_OutOfRange, "This number is outside the allowable range for representable integer constants");
        mk_term (Const (Const_int (fst n, None))) (rhs parseState 1) Expr
      )}
| lident
    {let u = $1 in
             ( mk_term (Uvar u) (range_of_id u) Expr )}
| LPAREN universeFrom RPAREN
    {let (_1, u, _3) = ((), $2, ()) in
    ( u (*mk_term (Paren u) (rhs2 parseState 1 3) Expr*) )}

warn_error_list:
  warn_error EOF
    {let (e, _2) = ($1, ()) in
                     ( e )}

warn_error:
  flag range
    {let (f, r) = ($1, $2) in
    ( [(f, r)] )}
| flag range warn_error
    {let (f, r, e) = ($1, $2, $3) in
    ( (f, r) :: e )}

flag:
  OPINFIX1
    {let op = $1 in
    ( if op = "@" then CAlwaysError else failwith (format1 "unexpected token %s in warn-error list" op))}
| OPINFIX2
    {let op = $1 in
    ( if op = "+" then CWarning else failwith (format1 "unexpected token %s in warn-error list" op))}
| MINUS
    {let _1 = () in
          ( CSilent )}

range:
  INT
    {let i = $1 in
    ( format2 "%s..%s" (fst i) (fst i) )}
| RANGE
    {let r = $1 in
    ( r )}

string:
  STRING
    {let s = $1 in
             ( s )}

some_fsTypeArgs_:
  fsTypeArgs
    {let x = $1 in
        ( Some x )}

right_flexible_list_SEMICOLON_fieldPattern_:
  
    {        ( [] )}
| fieldPattern
    {let x = $1 in
        ( [x] )}
| fieldPattern SEMICOLON right_flexible_list_SEMICOLON_fieldPattern_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

right_flexible_list_SEMICOLON_noSeqTerm_:
  
    {        ( [] )}
| noSeqTerm
    {let x = $1 in
        ( [x] )}
| noSeqTerm SEMICOLON right_flexible_list_SEMICOLON_noSeqTerm_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

right_flexible_list_SEMICOLON_recordFieldDecl_:
  
    {        ( [] )}
| recordFieldDecl
    {let x = $1 in
        ( [x] )}
| recordFieldDecl SEMICOLON right_flexible_list_SEMICOLON_recordFieldDecl_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

right_flexible_list_SEMICOLON_simpleDef_:
  
    {        ( [] )}
| simpleDef
    {let x = $1 in
        ( [x] )}
| simpleDef SEMICOLON right_flexible_list_SEMICOLON_simpleDef_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

right_flexible_nonempty_list_SEMICOLON_fieldPattern_:
  fieldPattern
    {let x = $1 in
        ( [x] )}
| fieldPattern SEMICOLON right_flexible_list_SEMICOLON_fieldPattern_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

right_flexible_nonempty_list_SEMICOLON_recordFieldDecl_:
  recordFieldDecl
    {let x = $1 in
        ( [x] )}
| recordFieldDecl SEMICOLON right_flexible_list_SEMICOLON_recordFieldDecl_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

right_flexible_nonempty_list_SEMICOLON_simpleDef_:
  simpleDef
    {let x = $1 in
        ( [x] )}
| simpleDef SEMICOLON right_flexible_list_SEMICOLON_simpleDef_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

reverse_left_flexible_list_BAR___anonymous_7_:
  
    {   ( [] )}
| patternBranch
    {let pb = $1 in
let x =                                                                                                    (pb) in
   ( [x] )}
| reverse_left_flexible_list_BAR___anonymous_7_ BAR patternBranch
    {let (xs, _2, pb) = ($1, (), $3) in
let x =                                                                                                    (pb) in
   ( x :: xs )}

reverse_left_flexible_nonempty_list_BAR_patternBranch_:
  patternBranch
    {let x = $1 in
let _1 =     ( None ) in
   ( [x] )}
| BAR patternBranch
    {let (x_inlined1, x) = ((), $2) in
let _1 =
  let x = x_inlined1 in
      ( Some x )
in
   ( [x] )}
| reverse_left_flexible_nonempty_list_BAR_patternBranch_ BAR patternBranch
    {let (xs, _2, x) = ($1, (), $3) in
   ( x :: xs )}

%%


