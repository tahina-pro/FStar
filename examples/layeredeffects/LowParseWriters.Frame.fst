module LowParseWriters.Frame

open LowParseWriters.NoHoare

module U32 = FStar.UInt32

#set-options "--ide_id_info_off"

irreducible let framing : unit = ()
irreducible let __reduce__ : unit = ()
let last (#a:Type) (x:a) : a = x

let valid_rewrite_pair (p p1 p2:parser)
  : Lemma (requires valid_rewrite_prop p1 p2)
          (ensures valid_rewrite_prop (p1 `parse_pair` p) (p2 `parse_pair` p))
= valid_rewrite_parse_pair_compat_r p #p1 #p2 ()

let valid_rewrite_pair_l (p p1 p2:parser)
  : Lemma (requires valid_rewrite_prop p1 p2)
          (ensures valid_rewrite_prop (p `parse_pair` p1) (p `parse_pair` p2))
= valid_rewrite_parse_pair_compat_l p #p1 #p2 ()

let valid_rewrite_trans (p1 p2 p3:parser)
  : Lemma (requires valid_rewrite_prop p1 p2 /\ valid_rewrite_prop p2 p3)
          (ensures valid_rewrite_prop p1 p3)
  = valid_rewrite_compose #p1 #p2 () #p3 ()

let valid_rewrite_trans4 (p1 p2 p3 p4:parser)
  : Lemma (requires valid_rewrite_prop p1 p2 /\ valid_rewrite_prop p2 p3 /\ valid_rewrite_prop p3 p4)
          (ensures valid_rewrite_prop p1 p4)
  = valid_rewrite_trans p1 p2 p3;
    valid_rewrite_trans p1 p3 p4

let valid_rewrite_cong (p1 p1' p2 p2':parser)
  : Lemma (requires valid_rewrite_prop p1 p1' /\ valid_rewrite_prop p2 p2')
          (ensures valid_rewrite_prop (p1 `parse_pair` p2) (p1' `parse_pair` p2'))
  = valid_rewrite_pair p2 p1 p1';
    valid_rewrite_pair_l p1' p2 p2';
    valid_rewrite_trans
      (p1 `parse_pair` p2)
      (p1' `parse_pair` p2)
      (p1' `parse_pair` p2')

let maybe_emp (framed:bool) (p:parser) = if framed then p == parse_empty else True

(** Framing tactic for parsers **)

open FStar.Tactics

let rec filter_goals (l:list goal) : Tac (list goal * list goal) =
  match l with
  | [] -> [], []
  | hd::tl ->
    let tl1, tl2 = filter_goals tl in
    match term_as_formula' (goal_type hd) with
    | App t r -> if term_eq t (`squash) then (
          let name, _ = collect_app r in
          if term_eq name (`last) then
            tl1, hd::tl2
          else hd::tl1, tl2
        ) else tl1, tl2
    | _ -> tl1, tl2

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

let rec size (e:exp) : pos = match e with
  | Unit -> 1
  | Atom _ -> 1
  | Mult e1 e2 -> size e1 + size e2

let rec right_assoc (e:exp) : Tot (e':exp{size e == size e'})  (decreases (size e)) =
  match e with
  | Unit -> Unit
  | Atom x -> Atom x
  | Mult e1 e2 ->
    match right_assoc e2 with
    | Unit -> Mult (right_assoc e1) Unit
    | Atom x -> Mult (right_assoc e1) (Atom x)
    | Mult e1' e2' -> Mult (right_assoc (Mult e1 e1')) e2'


let rec xsdenote (xs:list atom) : exp =
  match xs with
  | [] -> Unit
  | [x] -> Atom x
  | x::xs' -> Mult (Atom x) (xsdenote xs')

let rec flatten (e:exp) : list atom =
  match e with
  | Unit -> []
  | Atom x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2



/// Meta-F* internal: Transforms the atom map into a term
let rec convert_map (m : list (atom * term)) : term =
  match m with
  | [] -> `[]
  | (a, t)::ps ->
      let a = pack_ln (Tv_Const (C_Int a)) in
      `((`#a, (`#t)) :: (`#(convert_map ps)))


/// `am` is an amap (basically a list) of terms, each representing a value
/// of type `a` (whichever we are canonicalizing). This functions converts
/// `am` into a single `term` of type `amap a`, suitable to call `mdenote` with *)
let convert_am (am : amap term) : term =
  let (map, def) = am in
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
          `%flatten; `%xsdenote; `%right_assoc;
          `%fst; `%__proj__Mktuple2__item___1;
          `%snd; `%__proj__Mktuple2__item___2;]]

/// The normalization function, using the above normalization steps
let normal_tac (#a:Type) (x:a) : a = FStar.Pervasives.norm normal_tac_steps x

/// Helper lemma to establish relation between normalized and initial values
let normal_elim (x:Type0) : Lemma
  (requires x)
  (ensures normal_tac x)
  = ()

let rec lemma_right_assoc (am:amap parser) (e:exp)
  : Lemma (ensures
      mdenote am (right_assoc e) `valid_rewrite_prop` mdenote am e /\
      mdenote am e `valid_rewrite_prop` mdenote am (right_assoc e))
          (decreases size e)
  = match e with
    | Unit -> ()
    | Atom _ -> ()
    | Mult e1 e2 -> match right_assoc e2 with
      | Unit ->
        lemma_right_assoc am e1;
        valid_rewrite_pair parse_empty (mdenote am (right_assoc e1)) (mdenote am e1);
        valid_rewrite_pair parse_empty (mdenote am e1) (mdenote am (right_assoc e1))
      | Atom x ->
        lemma_right_assoc am e1;
        valid_rewrite_pair (select x am) (mdenote am (right_assoc e1)) (mdenote am e1);
        valid_rewrite_pair (select x am) (mdenote am e1) (mdenote am (right_assoc e1))
      | Mult e1' e2' ->
        assert (mdenote am (right_assoc e) ==
          mdenote am (right_assoc (Mult e1 e1')) `parse_pair` mdenote am e2');
        lemma_right_assoc am (Mult e1 e1');
        valid_rewrite_pair (mdenote am e2')
          (mdenote am (right_assoc (Mult e1 e1')))
          (mdenote am (Mult e1 e1'));
        assert (mdenote am (right_assoc e) `valid_rewrite_prop`
          (mdenote am (Mult e1 e1') `parse_pair` mdenote am e2'));
        let _ = valid_rewrite_parse_pair_assoc_1 (mdenote am e1) (mdenote am e1') (mdenote am e2') in
        valid_rewrite_trans
          (mdenote am (right_assoc e))
          (mdenote am (Mult e1 e1') `parse_pair` mdenote am e2')
          (mdenote am e1 `parse_pair` mdenote am (right_assoc e2));

        lemma_right_assoc am e2;
        valid_rewrite_pair_l (mdenote am e1) (mdenote am (right_assoc e2)) (mdenote am e2);

        valid_rewrite_trans
          (mdenote am (right_assoc e))
          (mdenote am e1 `parse_pair` mdenote am (right_assoc e2))
          (mdenote am e);

        // Other direction

        valid_rewrite_pair_l (mdenote am e1) (mdenote am e2) (mdenote am (right_assoc e2));
        let _ = valid_rewrite_parse_pair_assoc_2 (mdenote am e1) (mdenote am e1') (mdenote am e2') in

        valid_rewrite_pair (mdenote am e2')
          (mdenote am (Mult e1 e1'))
          (mdenote am (right_assoc (Mult e1 e1')));

        valid_rewrite_trans
          (mdenote am e1 `parse_pair` mdenote am (right_assoc e2))
          (mdenote am (Mult e1 e1') `parse_pair` mdenote am e2')
          (mdenote am (right_assoc e));

        valid_rewrite_trans
          (mdenote am e)
          (mdenote am e1 `parse_pair` mdenote am (right_assoc e2))
          (mdenote am (right_assoc e))


let right_assoc_reflect (am:amap parser) (e1 e2:exp) : Lemma
  (requires mdenote am (right_assoc e1) `valid_rewrite_prop` mdenote am (right_assoc e2))
  (ensures mdenote am e1 `valid_rewrite_prop` mdenote am e2)
  = lemma_right_assoc am e1;
    lemma_right_assoc am e2;
    valid_rewrite_trans4
      (mdenote am e1)
      (mdenote am (right_assoc e1))
      (mdenote am (right_assoc e2))
      (mdenote am e2)

let rec xsdenote_compose (am:amap parser) (l1 l2:list atom)
  : Lemma (
      (mdenote am (xsdenote l1) `parse_pair` mdenote am (xsdenote l2))
        `valid_rewrite_prop`
      mdenote am (xsdenote (l1 @ l2))
        /\
      mdenote am (xsdenote (l1 @ l2))
        `valid_rewrite_prop`
      (mdenote am (xsdenote l1) `parse_pair` mdenote am (xsdenote l2))
    )
  = let p2 = mdenote am (xsdenote l2) in

    match l1 with
    | [] -> valid_rewrite_emp_l' p2; valid_rewrite_emp_r' p2
    | [x] ->
        valid_rewrite_emp_l (mdenote am (Atom x));
        valid_rewrite_emp_r (mdenote am (Atom x))
    | hd::tl ->
      assert (l1 @ l2 == hd::(tl @ l2));
      assert (xsdenote l1 == Mult (Atom hd) (xsdenote tl));
      assert (mdenote am (xsdenote l1) == select hd am `parse_pair` mdenote am (xsdenote tl));
      assert (mdenote am (xsdenote (l1 @ l2)) ==
        select hd am `parse_pair` mdenote am (xsdenote (tl @ l2)));

      let _ = valid_rewrite_parse_pair_assoc_1
        (select hd am)
        (mdenote am (xsdenote tl))
        p2 in

      assert (
        ((select hd am `parse_pair` mdenote am (xsdenote tl)) `parse_pair` p2)
          `valid_rewrite_prop`
        (select hd am `parse_pair` (mdenote am (xsdenote tl) `parse_pair` p2))
      );

      xsdenote_compose am tl l2;

      valid_rewrite_cong
        (select hd am) (select hd am)
        (mdenote am (xsdenote tl) `parse_pair` p2)
        (mdenote am (xsdenote (tl @ l2)));

      valid_rewrite_trans
        (mdenote am (xsdenote l1) `parse_pair` mdenote am (xsdenote l2))
        (select hd am `parse_pair` (mdenote am (xsdenote tl) `parse_pair` p2))
        (mdenote am (xsdenote (l1 @ l2)));

      // Other direction

      valid_rewrite_cong
        (select hd am) (select hd am)
        (mdenote am (xsdenote (tl @ l2)))
        (mdenote am (xsdenote tl) `parse_pair` p2);

      let _ = valid_rewrite_parse_pair_assoc_2
        (select hd am)
        (mdenote am (xsdenote tl))
        p2 in

      valid_rewrite_trans
        (mdenote am (xsdenote (l1 @ l2)))
        (select hd am `parse_pair` (mdenote am (xsdenote tl) `parse_pair` p2))
        (mdenote am (xsdenote l1) `parse_pair` mdenote am (xsdenote l2))

let rec flatten_correct (am:amap parser) (e:exp)
  : Lemma (
      mdenote am e `valid_rewrite_prop` mdenote am (xsdenote (flatten e)) /\
      mdenote am (xsdenote (flatten e)) `valid_rewrite_prop` mdenote am e
    )
  = match e with
    | Unit -> ()
    | Atom _ -> ()
    | Mult e1 e2 ->
      flatten_correct am e1;
      flatten_correct am e2;
      let p1 = mdenote am e1 in
      let p2 = mdenote am e2 in
      let p1' = mdenote am (xsdenote (flatten e1)) in
      let p2' = mdenote am (xsdenote (flatten e2)) in
      assert (mdenote am e == mdenote am e1 `parse_pair` mdenote am e2);
      valid_rewrite_cong p1 p1' p2 p2';
      assert (mdenote am e `valid_rewrite_prop` (p1' `parse_pair` p2'));
      xsdenote_compose am (flatten e1) (flatten e2);
      valid_rewrite_trans
        (mdenote am e)
        (p1' `parse_pair` p2')
        (mdenote am (xsdenote (flatten e)));
      valid_rewrite_cong p1' p1 p2' p2;
      valid_rewrite_trans
        (mdenote am (xsdenote (flatten e)))
        (p1' `parse_pair` p2')
        (mdenote am e)

let monoid_reflect (am:amap parser) (e1 e2:exp) : Lemma
  (requires mdenote am (xsdenote (flatten e1)) `valid_rewrite_prop` mdenote am (xsdenote (flatten e2)))
  (ensures mdenote am e1 `valid_rewrite_prop` mdenote am e2)
  = flatten_correct am e1;
    flatten_correct am e2;
    valid_rewrite_trans4
      (mdenote am e1)
      (mdenote am (xsdenote (flatten e1)))
      (mdenote am (xsdenote (flatten e2)))
      (mdenote am e2)

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
  apply_lemma (`monoid_reflect);
  apply_lemma (`right_assoc_reflect);

  norm normal_tac_steps;

  ignore (repeat (fun _ -> apply_lemma (`valid_rewrite_pair); dismiss_parsers ()));

  or_else (fun _ -> apply_lemma (`valid_rewrite_refl))
          (fun _ ->
          or_else
            (fun _ -> apply_lemma (`valid_rewrite_emp_l'))
            (fun _ -> apply_lemma (`valid_rewrite_emp_r')))

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

let rec solve_last () : Tac unit =
  match goals () with
  | [] -> ()
  | hd::tl -> norm [delta_only [`%last]];
    match term_as_formula' (cur_goal ()) with
    | App _ t ->
      let _, args = collect_app t in
      begin match args with
        | [(t1, _); (t2, _)] ->
          focus (fun _ -> or_else (fun _ -> solve_goal t1 t2) smt)
        | _ -> fail "ill-formed goal"
      end
    | _ -> fail "ill-formed goal"



[@@ resolve_implicits; framing]
let resolve () : Tac unit =
  let gs, lasts = filter_goals (goals ()) in
  set_goals gs;
  solve_maybe_emps (goals ());
  solve ();
  set_goals lasts;
  solve_last ()

(** End tactic **)

inline_for_extraction
let repr (a:Type u#a) (framed:bool) (r_in:parser) (r_out:parser) (l:memory_invariant) : Tot Type
 = unit -> TWrite a r_in r_out l

inline_for_extraction
let returnc
  (t: Type)
  (x: t)
  (r: parser)
  (inv: memory_invariant)
: Tot (repr t true r r inv)
= fun _ -> x

inline_for_extraction
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
let bind a b ff fg r_in_f r_out_f r_in_g r_out_g #frame_f #frame_g l f g =
  fun _ ->
  let x = frame2 a frame_f r_in_f r_out_f l f in
  valid_rewrite #(frame_f `parse_pair` r_out_f) #(frame_g `parse_pair` r_in_g) ();
  frame2 b frame_g r_in_g r_out_g l (g x)

inline_for_extraction
val subcomp (a:Type)
  (r_in r_in':parser) (r_out r_out':parser)
  (ff fg:eqtype_as_type bool)
  (#[@@@ framing] _ : squash (valid_rewrite_prop r_in' r_in))
  (#[@@@ framing] _ : squash (last (valid_rewrite_prop r_out r_out')))
  (l:memory_invariant)
  (l': memory_invariant)
  (f:repr a ff r_in r_out l)
: Pure (repr a fg r_in' r_out' l')
  (requires (
    l `memory_invariant_includes` l'
  ))
  (ensures (fun _ -> True))
let subcomp a r_in r_in' r_out r_out' ff fg l l' f =
  (fun _ ->
    valid_rewrite #r_in' #r_in ();
    f ())

[@@allow_informative_binders]
reifiable reflectable total
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

(* FIXME? The explicit pure lift is still necessary even though PURE can still lift via TWrite. If this lift is not explicitly defined here, then examples below will fail *)

inline_for_extraction
val lift_pure_write (a:Type) (wp:pure_wp a)
  (l: memory_invariant)
  (f: eqtype_as_type unit -> PURE a wp)
: Pure (repr a false parse_empty parse_empty l)
  (requires (wp (fun _ -> True)))
  (ensures (fun _ -> True))
let lift_pure_write a wp l f = fun _ -> f ()

sub_effect PURE ~> FWriteBase = lift_pure_write

inline_for_extraction
val lift_twrite (a:Type) (pin:parser) (pout:parser)
  (l: memory_invariant)
  (f: LowParseWriters.NoHoare.repr a pin pout l)
: Pure (repr a false pin pout l)
  (requires True)
  (ensures (fun _ -> True))
let lift_twrite a pin pout l f _ = TWrite?.reflect f

sub_effect TWrite ~> FWriteBase = lift_twrite

open LowParseWriters.Test

// FIXME: commenting out this definition makes write_example2 FAIL despite lifting TWrite to FWrite
let write_u32 (#inv: _) (x: U32.t) : FWrite unit parse_empty parse_u32 inv
= write_u32 x

// [@@__reduce__]
// let parse_example2 = parse_u32 `parse_pair` parse_u32

let write_example2
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


(* Using LowParseWriters.Test.parse_example *)

let write_example
  inv
  (left right: U32.t)
: FWrite unit parse_empty parse_example inv
=
  write_u32 left;
  write_u32 right;
  valid_rewrite valid_rewrite_example // FIXME: WHY WHY WHY? subcomp SHOULD work automatically

let write_one_int
  inv
  (x y: U32.t)
  (max: U32.t { U32.v max > 0 })
: FWrite unit parse_empty (parse_vllist parse_u32 0ul max) inv
= write_vllist_nil parse_u32 _;
  write_u32 x;
  extend_vllist_snoc parse_u32 _ _

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

let write_two_examples
  inv
  (left1 right1 left2 right2: U32.t)
  (max: U32.t { U32.v max > 0 })
: FWrite unit parse_empty (parse_vllist parse_example 0ul max) inv
= write_vllist_nil parse_example max;
  write_example _ left1 right1;
  extend_vllist_snoc parse_example _ _;
  write_example _ left2 right2;
  extend_vllist_snoc parse_example _ _

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
