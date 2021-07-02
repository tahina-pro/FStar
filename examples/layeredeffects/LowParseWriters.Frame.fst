module LowParseWriters.Frame

open LowParseWriters.NoHoare

module U32 = FStar.UInt32

#set-options "--ide_id_info_off"

irreducible let framing : unit = ()
irreducible let __reduce__ : unit = ()

let valid_rewrite_pair (p p1 p2:parser)
  : Lemma (requires valid_rewrite_prop p1 p2)
          (ensures valid_rewrite_prop (p `parse_pair` p1) (p `parse_pair` p2))
= valid_rewrite_parse_pair_compat_l p #p1 #p2 ()

let maybe_emp (framed:bool) (p:parser) = if framed then p == parse_empty else True

(** Framing tactic for parsers **)

open FStar.Tactics

let rec filter_goals (l:list goal) : Tac (list goal) =
  match l with
  | [] -> []
  | hd::tl ->
    let tl = filter_goals tl in
    match term_as_formula' (goal_type hd) with
    | App t _ -> if term_eq t (`squash) then hd::tl else tl
    | _ -> tl

(* Reification *)

/// We define a small language to handle arbitrary separation logic predicates.
/// Separation logic predicates are encoded as atoms for which equality is decidable,
/// here represented as integers
let atom : eqtype = int

/// Reflecting the structure of our separation logic on atmos
type exp : Type =
  | Unit : exp
  | Mult : exp -> exp -> exp
  | Atom : atom -> exp

/// A map from atoms to the terms they represent.
/// The second component of the term corresponds to a default element,
/// ensuring we never raise an exception when trying to access an element in the map
let amap (a:Type) = list (atom * a) * a

/// An empty atom map: The list map is empty
let const (#a:Type) (xa:a) : amap a = ([], xa)

/// Accessing an element in the atom map
let select (#a:Type) (x:atom) (am:amap a) : Tot a =
  match List.Tot.Base.assoc #atom #a x (fst am) with
  | Some a -> a
  | _ -> snd am

/// Updating the atom map. Since select finds the first element corresponding to
/// the atom in the list and we do not have any remove function,
/// we can simply append the new element at the head without removing any possible
/// previous element
let update (#a:Type) (x:atom) (xa:a) (am:amap a) : amap a =
  (x, xa)::fst am, snd am


/// Finds the position of first occurrence of x in xs.
/// This is now specialized to terms and their funny term_eq.
let rec where_aux (n:nat) (x:term) (xs:list term) :
    Tot (option nat) (decreases xs) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

let fatom (t:term) (ts:list term) (am:amap term) : Tac (exp * list term * amap term) =
  match where t ts with
  | Some v -> (Atom v, ts, am)
  | None ->
    let vfresh = List.Tot.Base.length ts in
    let t = norm_term [iota; zeta] t in
    (Atom vfresh, ts @ [t], update vfresh t am)

/// Transforimg a term into the corresponding list of atoms
/// If the atomic terms were already present in the map [am], then
/// they correspond to the same atoms
/// This expects that mult, unit, and t have already been normalized
let rec reification (ts:list term) (am:amap term) (t:term) : Tac (exp * list term * amap term)
  = let hd, tl = collect_app t in
    match inspect hd, tl with
    | Tv_FVar fv, [(t1, Q_Explicit); (t2, Q_Explicit)] ->
      if term_eq (pack (Tv_FVar fv)) (`parse_pair) then (
        let (e1, ts, am) = reification ts am t1 in
        let (e2, ts, am) = reification ts am t2 in
        (Mult e1 e2, ts, am)
      ) else fatom t ts am
    | _, _ ->
      if term_eq t (`parse_empty)
      then (Unit, ts, am)
      else fatom t ts am


let rec mdenote (am:amap parser) (e:exp) : parser =
  match e with
  | Unit -> parse_empty
  | Atom x -> select x am
  | Mult e1 e2 -> (mdenote am e1) `parse_pair` (mdenote am e2)

let rec xsdenote (am:amap parser) (xs:list atom) : parser =
  match xs with
  | [] -> parse_empty
  | [x] -> select x am
  | x::xs' -> (select x am) `parse_pair` (xsdenote am xs')

// Do a flatten composed with a rev, to simplify matching later on
let rec flatten (e:exp) : list atom =
  match e with
  | Unit -> []
  | Atom x -> [x]
  | Mult e1 e2 -> flatten e2 @ flatten e1


/// Meta-F* internal: Transforms the atom map into a term
let rec convert_map (m : list (atom * term)) : term =
  match m with
  | [] -> `[]
  | (a, t)::ps ->
      let a = pack_ln (Tv_Const (C_Int a)) in
      (* let t = norm_term [delta] t in *)
      `((`#a, (`#t)) :: (`#(convert_map ps)))


/// `am` is an amap (basically a list) of terms, each representing a value
/// of type `a` (whichever we are canonicalizing). This functions converts
/// `am` into a single `term` of type `amap a`, suitable to call `mdenote` with *)
let convert_am (am : amap term) : term =
  let (map, def) = am in
  (* let def = norm_term [delta] def in *)
  `( (`#(convert_map map), `#def) )

/// Transforms a term representatoin into a term through quotation
let rec quote_exp (e:exp) : term =
    match e with
    | Unit -> (`Unit)
    | Mult e1 e2 -> (`Mult (`#(quote_exp e1)) (`#(quote_exp e2)))
    | Atom n -> let nt = pack_ln (Tv_Const (C_Int n)) in
                (`Atom (`#nt))

let rec quote_atoms (l:list atom) = match l with
  | [] -> `[]
  | hd::tl -> let nt = pack_ln (Tv_Const (C_Int hd)) in
              (`Cons (`#nt) (`#(quote_atoms tl)))

/// Some internal normalization steps to make reflection of vprops into atoms and atom permutation go smoothly.
/// In particular, all the sorting/list functions are entirely reduced
let normal_tac_steps = [primops; iota; zeta; delta_only [
          `%mdenote; `%select; `%List.Tot.Base.assoc; `%List.Tot.Base.append;
          `%flatten; `%xsdenote;
          `%fst; `%__proj__Mktuple2__item___1;
          `%snd; `%__proj__Mktuple2__item___2;]]

/// The normalization function, using the above normalization steps
let normal_tac (#a:Type) (x:a) : a = FStar.Pervasives.norm normal_tac_steps x

/// Helper lemma to establish relation between normalized and initial values
let normal_elim (x:Type0) : Lemma
  (requires x)
  (ensures normal_tac x)
  = ()

let monoid_reflect (am:amap parser) (e1 e2:exp)
    (_ : squash (xsdenote am (flatten e1) `valid_rewrite_prop` xsdenote am (flatten e2)))
       : squash (mdenote am e1 `valid_rewrite_prop` mdenote am e2) =
    admit()


/// Counts the number of unification variables corresponding to vprops in the term [t]
let rec parser_uvars (t:term) : Tac int =
  match inspect t with
  | Tv_Uvar _ _ -> 1
  | Tv_App _ _ ->
    let hd, args = collect_app t in
    if term_eq hd (`parse_pair) then

      // Only count the number of unresolved slprops, not program implicits
      fold_left (fun n (x, _) -> n + parser_uvars x) 0 args
    else if is_uvar hd then 1
    else 0
  | _ -> 0

let rec list_to_string (xs:list atom) (am:amap term) : Tac string =
  match xs with
  | [] -> "end"
  | hd::tl -> term_to_string (select hd am) ^ " " ^ list_to_string tl am

let rec dismiss_parsers () : Tac unit =
  match term_as_formula' (cur_goal ()) with
    | App t _ -> if term_eq t (`squash) then () else (dismiss(); dismiss_parsers ())
    | _ -> dismiss(); dismiss_parsers ()

let solve_goal (t1 t2:term) : Tac unit =
  norm [delta_attr [`%__reduce__]];
  let am = const (`parse_empty) in (* empty map *)
  let (r1, ts, am) = reification [] am (norm_term [delta_attr [`%__reduce__]] t1) in
  let (r2, ts, am) = reification ts am (norm_term [delta_attr [`%__reduce__]] t2) in

  let am = convert_am am in
  let r1 = quote_exp r1 in
  let r2 = quote_exp r2 in

  let g = `(normal_tac (mdenote (`#am) (`#r1)
                 `valid_rewrite_prop`
               mdenote(`#am) (`#r2))) in

  change_sq g;
  apply_lemma (`normal_elim);
  apply (`monoid_reflect );

  norm normal_tac_steps;

  ignore (repeat (fun _ -> apply_lemma (`valid_rewrite_pair); dismiss_parsers ()));

  or_else (fun _ -> apply_lemma (`valid_rewrite_refl))
          (fun _ -> 
          or_else
            (fun _ -> apply_lemma (`valid_rewrite_emp_l))
            (fun _ -> apply_lemma (`valid_rewrite_emp_r)))


let rec solve_next (l:list goal) : Tac unit = match l with
  | [] -> fail "didn't find a constraint to schedule"
  | hd::tl -> match term_as_formula' (cur_goal ()) with
    | App _ t ->
      let _, args = collect_app t in
      begin match args with
        | [(t1, _); (t2, _)] ->
          let n1 = parser_uvars t1 in
          let n2 = parser_uvars t2 in
          if n1 + n2 <= 1 then (
            focus (fun _ -> solve_goal t1 t2)
          ) else (
            later ();
            solve_next tl
          )
        | _ -> fail "ill-formed goal"
      end
    | _ -> fail "ill-formed goal"

let rec solve () : Tac unit =
  match goals () with
  | [] -> ()
  | l -> solve_next l; solve ()

/// Solve the maybe_emp goals:
/// Normalize to unfold maybe_emp and the reduce the if/then/else, and
/// solve the goal (either an equality through trefl, or True through trivial)
let rec solve_maybe_emps (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (cur_goal ()) in (
    match f with
    | App _ t ->
      let hd, args = collect_app t in
      if term_eq hd (`maybe_emp) then
        (norm [delta_only [`%maybe_emp]; iota; zeta; primops; simplify];
         or_else trivial trefl)
      else later()
    | _ -> later()
    );
    solve_maybe_emps tl


[@@ resolve_implicits; framing]
let resolve () : Tac unit =
  let gs = filter_goals (goals ()) in
  set_goals gs;
  solve_maybe_emps (goals ());
  solve ()

(** End tactic **)

val repr (a:Type u#a) (framed:bool) (r_in:parser) (r_out:parser) (l:memory_invariant) : Tot Type
let repr a r_in r_out l = admit()

let returnc
  (t: Type)
  (x: t)
  (r: parser)
  (inv: memory_invariant)
: Tot (repr t true r r inv)
= admit()

val bind (a:Type) (b:Type)
  (ff fg:eqtype_as_type bool)
  (r_in_f:parser) (r_out_f: parser)
  (r_in_g:parser) (r_out_g:parser)
  (#[@@@ framing] frame_f:parser)
  (#[@@@ framing] frame_g:parser)
  (#[@@@ framing] _ : squash (maybe_emp ff frame_f))
  (#[@@@ framing] _ : squash (maybe_emp fg frame_g))
  (#[@@@ framing] _ : squash (valid_rewrite_prop (frame_f `parse_pair` r_out_f) (frame_g `parse_pair` r_in_g)))
  (l: memory_invariant)
  (f : repr a ff r_in_f r_out_f l)
  (g : (x: a -> repr b fg r_in_g r_out_g l))
: (repr b true (frame_f `parse_pair` r_in_f) (frame_g `parse_pair` r_out_g) l)
let bind a b r_in_f r_out_f r_in_g r_out_g l f g = admit()

val subcomp (a:Type)
  (r_in r_in':parser) (r_out r_out':parser)
  (ff fg:eqtype_as_type bool)
  (#[@@@ framing] _ : squash (valid_rewrite_prop r_in r_in'))
  (#[@@@ framing] _ : squash (valid_rewrite_prop r_out r_out'))
  (l:memory_invariant)
  (f:repr a ff r_in r_out l)
  : (repr a fg r_in' r_out' l)
let subcomp a r_in r_out r_out' l f = admit()

layered_effect {
  FWriteBase : a:Type -> (f:bool) -> (pin: parser) -> (pout: parser) -> (memory_invariant) -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp
}

effect FWrite (a:Type) (pin:parser) (pout:parser) (l:memory_invariant) =
  FWriteBase a false pin pout l

val lift_pure_write (a:Type) (wp:pure_wp a)
  (l: memory_invariant)
  (f: eqtype_as_type unit -> PURE a wp)
: Pure (repr a false parse_empty parse_empty l)
  (requires (wp (fun _ -> True)))
  (ensures (fun _ -> True))
let lift_pure_write a wp l f = admit()

sub_effect PURE ~> FWriteBase = lift_pure_write

assume val parse_u32 : parser

noeq
type example = { left: U32.t; right: U32.t }

[@@__reduce__]
let parse_example = parse_u32 `parse_pair` parse_u32

assume val write_u32
  (#inv: _)
  (x: U32.t)
: FWrite unit parse_empty parse_u32 inv

let write_example
  inv
  (left right: U32.t)
: FWrite unit parse_empty parse_example inv
=
  write_u32 left;
  write_u32 right

let write_three
  inv
  (left right: U32.t)
: FWrite unit parse_empty (parse_u32 `parse_pair` parse_u32 `parse_pair` parse_u32) inv
=
  write_u32 left;
  write_u32 right;
  write_u32 right


assume
val parse_vllist
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: Tot parser

assume
val write_vllist_nil
  (#inv: memory_invariant)
  (p: parser)
  (max: U32.t { U32.v max > 0 })
: FWrite unit parse_empty (parse_vllist p 0ul max) inv

assume
val extend_vllist_snoc
  (#inv: memory_invariant)
  (p: parser)
  (min: U32.t)
  (max: U32.t { U32.v min <= U32.v max /\ U32.v max > 0 })
: FWrite unit (parse_vllist p min max `parse_pair` p) (parse_vllist p min max) inv


let write_one_int
  inv
  (x y: U32.t)
  (max: U32.t { U32.v max > 0 })
: FWrite unit parse_empty (parse_vllist parse_u32 0ul max) inv
= write_vllist_nil _ _;
  write_u32 x;
  extend_vllist_snoc _ _ _

let write_two_ints
  inv
  (x y: U32.t)
  (max: U32.t { U32.v max > 0 })
: FWrite unit parse_empty (parse_vllist parse_u32 0ul max) inv
= write_vllist_nil parse_u32 max;
  write_u32 x;
  extend_vllist_snoc parse_u32 0ul max;
  write_u32 y;
  extend_vllist_snoc parse_u32 0ul max

// let write_two_examples
//   inv
//   (left1 right1 left2 right2: U32.t)
//   (max: U32.t { U32.v max > 0 })
// : TWrite unit parse_empty (parse_vllist parse_example 0ul max) inv
// = write_vllist_nil parse_example max;
//   frame (fun _ -> write_example _ left1 right1);
//   extend_vllist_snoc _ _ _;
//   frame (fun _ -> write_example _ left2 right2);
//   extend_vllist_snoc _ _ _

(* TODO: trying to rewrite write_example with write_u32 for individual fields instead of write_example will trigger associativity issues such as:

// parse_empty
write_vllist_nil parse_example max;
// parse_vllist parse_example min max;
frame (fun _ -> write_u32 left1);
// parse_vllist parse_example min max `parse_pair` parse_u32
frame (fun _ -> write_u32 right1);
// (parse_vllist parse_example min max `parse_pair` parse_u32) `parse_pair` parse_u32
// by LowParseWriters.NoHoare.subcomp2 and some associativity, we should have:
// parse_vllist parse_example min max `parse_pair` parse_example
extend_vllist_snoc _ _;
// parse_vllist parse_example min max
// etc.

Ideally, we should have associativity. (but NOT commutativity, of course, since data must be written in order.)
