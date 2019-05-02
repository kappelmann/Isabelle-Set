(*  Title:      unification.ML
    Author:     Alexander Krauss

Higher-Order Pattern unification, which can deal with rewrite rules.

*)




type substitution = term Vartab.table

fun pr_subst pr_term (theta: substitution) =
  Vartab.dest theta
  |> map (fn ((n, ix), t) => "?" ^ n ^ string_of_int ix ^ " ~-> " ^ pr_term t)



type binder = string * term * typ
type 'o u_equation = binder list * (term * term) * 'o

fun pr_binders (bs : binder list) = map (enclose "[" "]" o #1) (rev bs) |> space_implode " "

datatype 'o unification_problem = UP of {
  eqns: 'o u_equation list,              (* The worklist of equations, with origin information *)
  postponed : 'o u_equation list,        (* Postponed equations, to be retried later *)
  subst: substitution,                   (* The current substitution *)
  fresh_idx: int,                        (* Index for generating unification variables *)
  rews: thm list                         (* The list of rewrite rules *)
}

fun origin_of (_, _, or) = or

fun pr_equation ctxt (bs, (s, t), _) =
  let
    val pr_term = Syntax.string_of_term ctxt
    fun pr_termb t = pr_term (Term.subst_bounds (map (fn (n, _, T) => Free (n, T)) bs, t))
  in
    pr_binders bs ^ ": " ^ pr_termb s ^ " = " ^ pr_termb t
  end

fun pr_unification_problem ctxt (UP { eqns, postponed, subst, ... }) =
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


fun up_map_eqns f (UP { eqns=eqns, postponed=postponed, subst=subst, fresh_idx=fresh_idx, rews=rews })
  = UP { eqns=f eqns, postponed=postponed, subst=subst, fresh_idx=fresh_idx, rews=rews }

fun up_map_postponed f (UP { eqns=eqns, postponed=postponed, subst=subst, fresh_idx=fresh_idx, rews=rews })
  = UP { eqns=eqns, postponed=f postponed, subst=subst, fresh_idx=fresh_idx, rews=rews }

fun up_map_subst f (UP { eqns=eqns, postponed=postponed, subst=subst, fresh_idx=fresh_idx, rews=rews })
  = UP { eqns=eqns, postponed=postponed, subst=f subst, fresh_idx=fresh_idx, rews=rews }

fun postpone_current_equation (UP { eqns=eqn::eqns, postponed, subst, fresh_idx, rews })
  = UP { eqns=eqns, postponed=eqn::postponed, subst=subst, fresh_idx=fresh_idx, rews=rews }

fun up_get_subst (UP { subst, ... })
  = subst

fun up_get_rews (UP { rews, ... })
  = rews

fun init_up eqns fresh_idx rews =
 UP { eqns=eqns, postponed=[], subst=Vartab.empty, fresh_idx=fresh_idx, rews=rews }

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
    fun inst (t as Var (ixn, _)) = (case Vartab.lookup theta ixn of NONE => t | SOME s => s)
      | inst (s $ t) = inst s $ inst t
      | inst (Abs (n, T, t)) = Abs (n, T, inst t)
      | inst t = t
  in
    inst t
  end

fun instantiate_eqn theta (bs, (lhs, rhs), or) =
  (bs, (instantiate_term theta lhs, instantiate_term theta rhs), or)

(* Dealing with bound variables *)

(* Applies f to the index of each loose bound (applying level correction, so that the index is
always the same, even if the bound occurs under further binders. *)
fun map_bound_indices f =
    let fun mpb d (Bound i) = if i < d then Bound i else Bound (f (i - d) + d)
          | mpb d (Abs (s, T, t)) = Abs (s, T, mpb (d + 1) t)
          | mpb d (u1 $ u2) = mpb d u1 $ mpb d u2
          | mpb _ t = t
    in mpb 0 end






(* Rewriting *)

(* Hack: Bijection from Vars to frees, to avoid instantiation during simplification *)
fun encode_indexname (x, i) = x ^ chr 0 ^ string_of_int i
fun decode_indexname s =
  let val [x, is] = String.fields (fn c => Char.ord c = 0) s
  in (x, #1 (read_int (raw_explode is))) end
  
fun to_free (Var (ixn, T)) = Free (encode_indexname ixn, T)
  | to_free t = t 

fun to_var (t as Free (n, T)) = 
      if exists_string (curry op = (chr 0)) n
      then Var (decode_indexname n, T)
      else t
  | to_var t = t 


(* Rewrites all rules, returning a list of changed and unchanged rules *)
fun rewrite_eqns ctxt rews eqns =
  let
    val simp_rules = flat (map (Raw_Simplifier.mksimps ctxt) rews) 

    fun transform_term t =
      let val t' = 
        t
        |> Term.map_aterms to_free
        |> Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) simp_rules []
        |> Term.map_aterms to_var
      in if (t aconv t') then NONE else SOME t' end

      fun transform_eqn (bs, (s, t), or) = case (transform_term s, transform_term t) of
        (NONE, NONE) => NONE
      | (s', t') => SOME (bs, (the_default s s', the_default t t'), or)

      fun transform_eqns [] changed unchanged = (rev changed, rev unchanged)
        | transform_eqns (e::es) changed unchanged = case transform_eqn e of
              NONE => transform_eqns es changed (e :: unchanged)
            | SOME e' => transform_eqns es (e' :: changed) unchanged

  in
    transform_eqns eqns [] []
  end 







(* Unification *)

fun unify ctxt (u as UP {eqns, postponed, subst, ...}) =
  let 
    val _ = Output.tracing (pr_unification_problem ctxt u)
  in
    case (eqns, postponed) of 
       ((eqn as (_, (lhs, rhs), _)) :: _, _) => 
         (if lhs aconv rhs (* reflexive case *)
         then unify ctxt (up_map_eqns tl u)
         else cases ctxt u eqn)
     | ([], []) => subst
     | ([], ps) => try_rewrite ctxt u ps
  end


and cases ctxt u (eqn as (bs, (lhs, rhs), _)) = 
      let
        val ((lhd, ss), (rhd, ts)) = (strip_comb lhs, strip_comb rhs)
      in case (lhd, rhd) of
        (Var _, Var _)        => flexflex ctxt bs u lhd ss rhd ts
      | (Var _, _)            => flexrigid ctxt bs u lhd ss rhs
      | (_, Var _)            => flexrigid ctxt bs u rhd ts lhs
      | (Const _, Const _)    => rigidrigid ctxt u eqn lhd ss rhd ts
      | (Free _, Free _)      => rigidrigid ctxt u eqn lhd ss rhd ts
      | (Const _, Free _)     => rigidrigid ctxt u eqn lhd ss rhd ts
      | (Free _, Const _)     => rigidrigid ctxt u eqn lhd ss rhd ts
      | (Const _, Bound _)      => error "Const-Bound clash"
      | (Free _, Bound _)     => error "Free-Bound clash"
      | (Bound _, Const _)    => error "Clash"
      | (Bound _, Free _)      => error "Clash"
      | _                     => error "Case not implemented"
      end

and flexflex ctxt bs u F ss G ts =
  if ss = [] andalso ts = [] 
  then flexrigid ctxt bs u F ss (list_comb (G, ts))
  else error "FlexFlex: function variable case not supported yet"


(* Flex-Rigid case: 

  ?F ss = t    where ss are loose bounds

Instantiate ?F with (%ss. t)
*)
and flexrigid ctxt bs u F ss t =
      if occurs F t then error "Occurs check failed"
      else let
        val bounds_in_t = Term.loose_bnos t
        val bound_by_F = 
          map (fn s => case s of Bound i => i | _ => error "Not a pattern") ss
        val _ = if subtract (op =) bound_by_F bounds_in_t <> []
                then error "Unsolvalbe bound variable in equation." else ()
        
        (* mapping function for bound indices, which must match the binders we construct *)
        val bound_reorder = the o Inttab.lookup (Inttab.make (map_index swap (rev bound_by_F)))
        val t' = map_bound_indices bound_reorder t
        val lambdas_to_add = map (nth bs) bound_by_F
        val inst = 
          (fst (dest_Var F), fold_rev (fn (n, _, T) => fn b => Abs (n, T, b)) lambdas_to_add t')

        val new_subst = Vartab.update inst (up_get_subst u)
        val instantiate = map (instantiate_eqn new_subst)
      in
        u 
        |> up_map_eqns (instantiate o tl)
        |> up_map_postponed instantiate
        |> up_map_subst (K new_subst)
        |> unify ctxt
      end


(* Rigid-Rigid case: If possible, decompose the equation. Otherwise, postpone, since we may
   have to rewrite. *)
and rigidrigid ctxt u eqn f ss g ts =
      if f <> g
      then postpone_current_equation u |> unify ctxt
      else let
        val old_binders = #1 eqn
        val old_origin = origin_of eqn
        fun mk_eqn pair = (old_binders, pair, old_origin)
        val new_eqns = map mk_eqn (ss ~~ ts)
      in
        u
        |> up_map_eqns (fn eqns => (new_eqns @ tl eqns))
        |> unify ctxt
      end

(* Tries to rewrite a blocked equation. Rewriting must occur at the head, since the head symbol
   is blocked *)
and try_rewrite ctxt u ps =
  case rewrite_eqns ctxt (up_get_rews u) ps of
    ([], _) => error "No progress: Cannot simplify blocked equations"
  | (changed, unchanged) =>
      u
      |> up_map_eqns (K changed)
      |> up_map_postponed (K unchanged)
      |> unify ctxt
  




;



