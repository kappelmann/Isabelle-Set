(*  Title:      unification.ML
    Author:     Alexander Krauss

Higher-Order Pattern Unification, which can deal with rewrite rules.

This implementation attempts to deal with equations that do not strictly conform to the pattern
fragment but are nevertheless easy to simplify. True non-pattern equations are now rejected.

Non-unifiable Rigid-Rigid pairs are kept until the end, when they are attacked with rewriting
with specially-declared [type_simp] rules.

The algorithm works incrementally, where the type "unification_state" models the state.
New equations can be inserted into the state at any time, and the current substitution is
available via "instantiate".

The type parameter 'o ("origin") can be used to track the origin of each equation (e.g.,
an application in a type inference problem). Origins are merely passed around by this module,
but never inspected.

*)
signature UNIFICATION = sig

  type binder = string * term * typ     (* (name, soft type, rigid type) *)
  type 'o equation = binder list * (term * term) * 'o
  type 'o unification_state

  val init: int -> 'o unification_state

  val add_equation: Proof.context -> 'o equation -> 'o unification_state -> 'o unification_state
  val fresh_idx: 'o unification_state -> int * 'o unification_state

  val is_finished: 'o unification_state -> bool
  val instantiate: 'o unification_state -> term -> term

  val unify: Proof.context -> thm list -> 'o unification_state -> 'o unification_state

  val pr_binders: binder list -> string
  val pr_equation: Proof.context -> 'o equation -> string

end



structure Unification : UNIFICATION =
struct

type binder = string * term * typ
type 'o equation = binder list * (term * term) * 'o

datatype 'o unification_state = UState of {
  eqns: 'o equation list,              (* The worklist of equations, with origin information *)
  postponed : 'o equation list,        (* Postponed equations, to be retried later *)
  subst: term Vartab.table,            (* The current substitution *)
  fresh_idx: int                       (* Index for generating unification variables *)
}


(* Basic operations on unification problems *)

fun origin_of (_, _, or) = or

fun up_map_eqns f (UState { eqns=eqns, postponed=postponed, subst=subst, fresh_idx=fresh_idx })
  = UState { eqns=f eqns, postponed=postponed, subst=subst, fresh_idx=fresh_idx }

fun up_map_postponed f (UState { eqns=eqns, postponed=postponed, subst=subst, fresh_idx=fresh_idx })
  = UState { eqns=eqns, postponed=f postponed, subst=subst, fresh_idx=fresh_idx }

fun up_map_subst f (UState { eqns=eqns, postponed=postponed, subst=subst, fresh_idx=fresh_idx })
  = UState { eqns=eqns, postponed=postponed, subst=f subst, fresh_idx=fresh_idx }

fun up_map_fresh_idx f (UState { eqns=eqns, postponed=postponed, subst=subst, fresh_idx=fresh_idx })
  = UState { eqns=eqns, postponed=postponed, subst=subst, fresh_idx=f fresh_idx }

fun postpone_current_equation (UState { eqns=eqns, postponed, subst, fresh_idx })
  = UState { eqns=tl eqns, postponed=hd eqns::postponed, subst=subst, fresh_idx=fresh_idx }

fun fresh_idx (UState {eqns, postponed, subst, fresh_idx=i}) =
  (i, UState { eqns=eqns, postponed=postponed, subst=subst, fresh_idx=i+1 })

fun up_get_subst (UState { subst, ... })
  = subst

fun up_get_fresh_idx up = fst (fresh_idx up)



fun init fresh_idx =
 UState { eqns=[], postponed=[], subst=Vartab.empty, fresh_idx=fresh_idx }

fun is_finished (UState { eqns=[], postponed=[], ...}) = true
  | is_finished _ = false



(* Tracing *)

fun pr_subst pr_term theta =
  Vartab.dest theta
  |> map (fn ((x, ix), t) => "?" ^ x ^ string_of_int ix ^ " ~-> " ^ pr_term t)

fun pr_binders (bs : binder list) = map (enclose "[" "]" o #1) (rev bs) |> space_implode " "

fun pr_equation ctxt (bs, (s, t), _) =
  let
    val pr_term = Syntax.string_of_term ctxt
    fun pr_termb t = pr_term (Term.subst_bounds (map (fn (x, _, T) => Free (x, T)) bs, t))
  in
    pr_binders bs ^ ": " ^ pr_termb s ^ " = " ^ pr_termb t
  end

fun pr_unification_state ctxt (UState { eqns, postponed, subst, ... }) =
  let
    fun section header content = if (content <> []) then header :: map (prefix "  ") content else []

    val pr_term = Syntax.string_of_term ctxt
  in
     cat_lines ("--- Unification Problem ---" ::
      flat [
        section "Eqns" (map (pr_equation ctxt) eqns),
        section "Postponed" (map (pr_equation ctxt) postponed),
        section "Subst" (pr_subst pr_term subst)
      ])
  end





(* Occurs check. Note that we do not apply substitutions here, since we assume that they
have already been applied *)
fun occurs (Var (F, _)) t =
    let fun occ (Var (G, _))   = (F = G)
          | occ (s $ t)        = occ s orelse occ t
          | occ (Abs(_, _, t)) = occ t
          | occ _              = false
    in occ t end
  | occurs _ _ = raise Match




(* Substitution *)

fun instantiate_term theta t =
  let
    fun inst (t as Var (ixn, _)) = (case Vartab.lookup theta ixn of NONE => t | SOME s => inst s)
      | inst (s $ t) = inst s $ inst t
      | inst (Abs (n, T, t)) = Abs (n, T, inst t)
      | inst t = t
  in
    inst t
  end

fun instantiate_eqn theta (bs, (lhs, rhs), or) =
  (bs, (instantiate_term theta lhs, instantiate_term theta rhs), or)


fun instantiate up =
  instantiate_term (up_get_subst up)
  #> Envir.beta_norm




(* Dealing with bound variables *)

(* Applies f to the index of each loose bound (applying level correction, so that the index is
always the same, even if the bound occurs under further binders. *)
fun map_bound_indices f =
    let fun mpb d (Bound i) = if i < d then Bound i else Bound (f (i - d) + d)
          | mpb d (Abs (s, T, t)) = Abs (s, T, mpb (d + 1) t)
          | mpb d (u1 $ u2) = mpb d u1 $ mpb d u2
          | mpb _ t = t
    in mpb 0 end


fun the_fail msg opt = case opt of SOME x => x | _ => raise Fail msg

(*
  Given
  - term [t] with loose bounds
  - the binder context [binders]
  - a list of indices [is]
  Checks that
  - all loose bounds that actually occur in [t] are present in [is]
  And returns the term
   %x y z. t
  which abstracts over exactly the variables referred to in [is]
*)
fun abstract_over_loose_bounds binders is t =
  let
    (* mapping function for bound indices, which must match the binders we construct *)
    val bound_reorder = Inttab.lookup (Inttab.make (map_index swap (rev is)))
  in
    t
    |> map_bound_indices (bound_reorder #> the_fail "loose bound not covered by abstraction")
    |> fold_rev (fn (x, _, T) => fn b => Abs (x, T, b)) (map (nth binders) is)
  end


(* Rewriting *)

(* Hack: Bijection from Vars to frees, to avoid instantiation during simplification *)
fun encode_indexname (x, i) = x ^ chr 0 ^ string_of_int i
fun decode_indexname s =
  let val [x, is] = String.fields (fn c => Char.ord c = 0) s
  in (x, #1 (read_int (raw_explode is))) end

fun to_free (Var (ixn, T)) = Free (encode_indexname ixn, T)
  | to_free t = t

fun to_var (t as Free (x, T)) =
      if exists_string (curry op = (chr 0)) x
      then Var (decode_indexname x, T)
      else t
  | to_var t = t

fun abstract_over_frees vs t =
  let
    fun abs lev tm =
        case tm of
          Free _ => (case find_index (curry op = tm) vs of
              ~1 => tm
            | i => Bound (lev + i))
        | Abs (a, T, t) => Abs (a, T, abs (lev + 1) t)
        | t $ u => abs lev t $ abs lev u
        | _ => tm;
  in abs 0 t end


fun replace_bounds ctxt binders t =
  let
    val frees = map Free (Variable.variant_names (fold Variable.declare_names [t] ctxt)
      (map (fn (x, _, T) => (x, T)) binders))
    val reverse_op = abstract_over_frees frees
  in
    (Term.subst_bounds (frees, t), reverse_op)
  end


(* Rewrites all rules, returning a list of changed and unchanged rules *)
fun rewrite_eqns ctxt rews eqns =
  let
    val simp_rules = flat (map (Raw_Simplifier.mksimps ctxt) rews)

    fun transform_term bs t =
      let val _ = Soft_Type.tracing ctxt ("Trying to rewrite " ^ Syntax.string_of_term ctxt t)
        val (t', f) = replace_bounds ctxt bs t
        val t'' =
          t'
          |> Term.map_aterms to_free
          |> Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) simp_rules []
          |> Term.map_aterms to_var
          |> f
      in if (t aconv t'') then NONE else SOME t'' end

      fun transform_eqn (bs, (s, t), or) = case (transform_term bs s, transform_term bs t) of
        (NONE, NONE) => NONE
      | (s', t') => SOME (bs, (the_default s s', the_default t t'), or)

      fun transform_eqns [] changed unchanged = (rev changed, rev unchanged)
        | transform_eqns (e::es) changed unchanged = case transform_eqn e of
              NONE => transform_eqns es changed (e :: unchanged)
            | SOME e' => transform_eqns es (e' :: changed) unchanged

  in
    transform_eqns eqns [] []
  end



(*
  Checks if the given equation "?F xs = rhs" is a solvable pattern. This is true iff
  - the left-hand side is a pattern
  - rhs does not contain other variables than the xs in rigid positions.
  - rhs does not contain ?F.
*)
fun can_replace F xs rhs =
  let
    fun check_arg idxs t = case t of
        Bound _ => true (* Other variables can be projected away in this position *)
      | _ => subset (op =) (Term.loose_bnos t, idxs)

    fun check_allowed_bounds d idxs t = case strip_comb t of
        (Var _, rs) => forall (check_arg idxs) rs
      | (Free _, rs) => forall (check_allowed_bounds d idxs) rs
      | (Const _, rs) => forall (check_allowed_bounds d idxs) rs
      | (Bound i, rs) => i < d orelse member (op =) idxs (i - d) andalso forall (check_allowed_bounds d idxs) rs
      | (Abs (_, _, b), rs) => check_allowed_bounds (d + 1) idxs b
                               andalso forall (check_allowed_bounds d idxs) rs
      | _ => raise Fail "Unreachable"

    val bvs =  map (fn s => case s of Bound i => i | _ => ~1) xs
    val is_lhs_linear =
      is_Var F
      andalso not (has_duplicates (op =) bvs)
      andalso forall (fn i => (i >= 0)) bvs
  in
    is_lhs_linear
    andalso check_allowed_bounds 0 bvs rhs
    andalso not (occurs F rhs)
  end



(*
  Creates an instantiation mapping the variable V to a new Variable V' which depends only on
  some given arguments of V.

  [V, T] the variable (name, index, type)
  [fresh_idx] a fresh index that will be used
  [keep args] a list of booleans denoting whether the argument should be
              kept (true) or projected away (false)

*)
fun make_projection (V, T) fresh_idx keep_args =
  let
    val arity = length keep_args
    val (argTs, otherTs) = chop arity (binder_types T)
    val resultT = otherTs ---> body_type T

    val filtered_args =
      (argTs ~~ keep_args)
      |> map_index I
      |> map_filter (fn (i, (T, keep)) => if keep then SOME (arity-i-1, T) else NONE)
  in
    (V,
      Var (apsnd (K fresh_idx) V, map #2 filtered_args ---> resultT)
      |> (fn v => list_comb (v, map (fn (i, _) => Bound i) filtered_args))
      |> fold_rev (fn T => fn b => Abs ("", T, b)) argTs)
  end



fun project_vars ctxt idxs t theta fresh_idx =
  let
    fun proj d t (theta, fresh_idx) = case Envir.beta_norm (instantiate_term theta t) of
        Abs (x, T, b) => proj (d + 1) b (theta, fresh_idx) |> apfst (fn b' => Abs(x, T, b'))
      | t' => case strip_comb t' of
          (Var ((x, i), T), rs) =>
             let
               fun keep_arg (Bound i) = i < d orelse member (op =) idxs (i - d)
                 | keep_arg _ = true
             in if forall keep_arg rs then (t', (theta, fresh_idx)) else let
               val inst = make_projection ((x, i), T) fresh_idx (map keep_arg rs)
               val theta' = Vartab.update inst theta
               val t' = Envir.beta_norm (list_comb (snd inst, rs))
             in
               (t', (theta', fresh_idx + 1))
             end end

        | (t, rs) => fold_map (proj d) rs (theta, fresh_idx) |> apfst (curry list_comb t)  (* Const, Free, Bound *)

in proj 0 t (theta, fresh_idx) end


(* Tries to rewrite a blocked equation. Rewriting must occur at the head, since the head symbol
   is blocked *)
fun try_rewrite ctxt rews u ps =
  case rewrite_eqns ctxt rews ps of
    ([], _) => error "No progress: Cannot simplify blocked equations"
  | (changed, unchanged) =>
      u
      |> up_map_eqns (K changed)
      |> up_map_postponed (K unchanged)


(* Rigid-Rigid case: If possible, decompose the equation. Otherwise, postpone, since we may
   have to rewrite. *)
fun rigidrigid u eqn f ss g ts =
      if f <> g
      then postpone_current_equation u
      else let
        val old_binders = #1 eqn
        val old_origin = origin_of eqn
        fun mk_eqn pair = (old_binders, pair, old_origin)
        val new_eqns = map mk_eqn (ss ~~ ts)
      in
        u
        |> up_map_eqns (fn eqns => (new_eqns @ tl eqns))
      end

(* Flex-Rigid case:

  ?F ss = t    where ss are loose bounds

Instantiate ?F with (%ss. t)
*)
and flexrigid ctxt bs u F ss t =
      if occurs F t then error "Occurs check failed"
      else let
        val bound_by_F =
          map (fn s => case s of Bound i => i | _ => error ("Not a pattern: " ^ \<^make_string> ss)) ss
        val _ = if not (can_replace F ss t)
                then error ("Equation is not a pattern: " ^ \<^make_string> (F, ss, t)) else ()
        val theta = up_get_subst u
        val fresh_idx = up_get_fresh_idx u
        val (t', (theta', fresh_idx')) = project_vars ctxt bound_by_F t theta fresh_idx
        val inst = (fst (dest_Var F), abstract_over_loose_bounds bs bound_by_F t')
        val new_subst = Vartab.update inst theta'
        val instantiate = map (instantiate_eqn new_subst)
      in
        u
        |> up_map_eqns (instantiate o tl)
        |> up_map_postponed instantiate
        |> up_map_subst (K new_subst)
        |> up_map_fresh_idx (K fresh_idx')
      end

fun flexflex_same u F ss ts =
  let
    fun can_unify (s, t) = (s aconv t) orelse case (s, t) of
        (Bound _, Bound _) => false
      | (Bound _, Free _) => false
      | (Free _, Bound _) => false
      | (Free _, Free _) => false
      | (Bound _, Const _) => false
      | (Const _, Bound _) => false
      | _ => true

    val keep_args = map can_unify (ss ~~ ts)
    val is_solved = ss ~~ ts ~~ keep_args
      |> forall (fn ((s, t), keep) => not keep orelse s aconv t)
    val inst = make_projection F (up_get_fresh_idx u) keep_args
    val theta = Vartab.update inst (up_get_subst u)

    val instantiate = map (instantiate_eqn theta)
  in
    u
    |> up_map_eqns (fn es => instantiate (if is_solved then tl es else es))
    |> up_map_postponed instantiate
    |> up_map_subst (K theta)
    |> up_map_fresh_idx (fn i => i + 1)
  end

fun flexflex_different ctxt bs u F ss G ts =
    if can_replace F ss (list_comb (G, ts))
    then flexrigid ctxt bs u F ss (list_comb (G, ts))
    else if can_replace G ts (list_comb (F, ss))
    then flexrigid ctxt bs u G ts (list_comb (F, ss))
    else error ("FlexFlex: non-pattern equality.")


(* cf. clone in soft_type_inference.ML *)
fun incr_bounds (Delta: binder list) =
  map (fn (x, st, T) => (x, Term.incr_boundvars 1 st, T)) Delta

fun abs_decompose u (Abs (x, T, b1)) (Abs (y, _, b2)) (bs, _, or) =
  let
    val name = if (x = "") then y else x
    val bs1 = incr_bounds ((name, Term.dummy, T) :: bs)
    val eqn1 = (bs1, (b1, b2), or)
  in
    up_map_eqns (cons eqn1 o tl) u
  end
  | abs_decompose _ _ _ _ = raise Match



fun cases ctxt u (eqn as (bs, (lhs, rhs), _)) =
      let
        val lhs' = Envir.beta_norm lhs
        val rhs' = Envir.beta_norm rhs
        val ((lhd, ss), (rhd, ts)) =
          (strip_comb lhs', strip_comb rhs')
      in case (lhd, rhd) of
        (Var F, Var G)        => if (F = G)
                                 then flexflex_same u F ss ts
                                 else flexflex_different ctxt bs u lhd ss rhd ts
      | (Var _, _)            => flexrigid ctxt bs u lhd ss rhs'
      | (_, Var _)            => flexrigid ctxt bs u rhd ts lhs'
      | (Const _, Const _)    => rigidrigid u eqn lhd ss rhd ts
      | (Free _, Free _)      => rigidrigid u eqn lhd ss rhd ts
      | (Const _, Free _)     => rigidrigid u eqn lhd ss rhd ts
      | (Free _, Const _)     => rigidrigid u eqn lhd ss rhd ts
      | (Abs _, Abs _)        => abs_decompose u lhs rhs eqn
      | (Const _, Bound _)      => error "Const-Bound clash"
      | (Free _, Bound _)     => error "Free-Bound clash"
      | (Bound _, Const _)    => error "Clash"
      | (Bound _, Free _)      => error "Clash"
      | _                     => error ("Case not implemented: " ^ \<^make_string> (lhs', rhs'))
      end




fun is_eqn_trivial (_, (lhs, rhs), _) = lhs aconv rhs


(*
  Tries to simplify the unification problem, making "progress" towards solving it.
  This includes decomposition of equations and applying pattern substitution and projection
  but no rewriting
*)
fun simplify ctxt (u as UState {eqns, ...}) =
  case eqns of
    [] => u
          |> tap (Soft_Type.tracing ctxt o pr_unification_state ctxt)
  | eqn :: _ =>
    if is_eqn_trivial eqn then simplify ctxt (up_map_eqns tl u)
    else let
      val _ = Soft_Type.tracing ctxt ("Simplifying " ^ pr_equation ctxt eqn)
    in
      simplify ctxt (cases ctxt u eqn)
    end






fun add_equation ctxt eqn up =
  let
    val eqn1 = instantiate_eqn (up_get_subst up) eqn
    val _ = Soft_Type.tracing ctxt ("Adding Constraint: " ^ pr_equation ctxt eqn1)
  in
    up
    |> up_map_eqns (cons eqn1)
    |> simplify ctxt
  end



(* Unification *)

fun unify ctxt rews (u as UState {eqns, postponed, ...}) =
  let
    val _ = Soft_Type.tracing ctxt (pr_unification_state ctxt u)
  in
    if is_finished u then u
    else let
      val next = case (eqns, postponed) of
         ((eqn as (_, (lhs, rhs), _)) :: _, _) =>
           (if lhs aconv rhs (* reflexive case *)
           then up_map_eqns tl u
           else cases ctxt u eqn)
         | ([], ps) => try_rewrite ctxt rews u ps
      in unify ctxt rews next end
  end




end



