(*  Title:      elaboration.ML
    Author:     Alexander Krauss

Elaboration. Turns a term into a fully specified term, making use of typing information.
*)

signature ELABORATION =
sig

  (* true iff the elaborator should be invoked automatically in a check phase *)
  val auto_elaborate : bool Config.T

  (* true iff simple function types should be assumed for function variables whose type is unknown *)
  val simple_types : bool Config.T

  val elaborate_terms: Proof.context -> term list -> term list

  val assert_result: Proof.context -> term list -> term list -> term list

end;

structure Elaboration : ELABORATION =
struct

  val auto_elaborate = Attrib.setup_config_bool \<^binding>\<open>auto_elaborate\<close> (K false)
  val simple_types = Attrib.setup_config_bool \<^binding>\<open>simple_types\<close> (K true)

  (* Similar to Term.map_aterms, but also passes the binder level to f *)
  fun map_aterms_lev f =
    let fun mapt l (Abs (n, T, b)) = Abs (n, T, mapt (l + 1) b)
          | mapt l (t $ u) = mapt l t $ mapt l u
          | mapt l t = f l t
    in mapt 0 end


  (* Background context and state. *)
  datatype elaboration_state = Elaboration_State of {

    (* types of constants (fixed) *)
    const_types: term -> term option,

    (* types of free variables (filled on the go) *)
    var_types: term Termtab.table,

    (* the unification state (including generation of fresh variables) *)
    up: unit Unification.unification_state
  }

  fun get_const_type (Elaboration_State {const_types, ...}) (c : term) =
    const_types c;
  
  fun get_var_type (Elaboration_State {const_types, var_types, up}) (v : term) =
    case const_types v of
      SOME sty => SOME sty
    | NONE => Termtab.lookup var_types v |> Option.map (Unification.instantiate up);
  
  fun map_up f (Elaboration_State {const_types, var_types, up}) =
    Elaboration_State {const_types=const_types, var_types=var_types, up = f up}

  fun add_constraint ctxt (c as (_, (lhs, rhs), _)) E =
    if lhs aconv rhs (* Skip trivial constraints *)
    then E
    else map_up (Unification.add_equation ctxt c) E

  
  fun fresh_idx (E as Elaboration_State {up, ...}) =
    let val (i, up') = Unification.fresh_idx up
    in (i, map_up (K up') E) end

  fun context_types (Delta : Unification.binder list) =
    map (#3) Delta

  fun incr_bounds (Delta : Unification.binder list) =
    map (fn (n, st, T) => (n, Term.incr_boundvars 1 st, T)) Delta

  fun fresh_variable T Delta E =
    let
      val var_type = context_types Delta ---> Soft_Type.typeT T
      val (i, E') = fresh_idx E
    in
      (Term.list_comb (Var (("UU", i), var_type), 
        map Bound ((length Delta) -1 downto 0)),
      E')
    end

  fun add_free (v, st) (Elaboration_State {const_types, var_types, up}) =
    Elaboration_State {const_types=const_types, var_types=Termtab.update_new (v, st) var_types, up=up};

  fun fix_var_type Delta v T E =
    let
      val (stv, E1) = fresh_variable T Delta E
    in
      (stv, add_free (v, stv) E1)
    end

  fun instantiate (st, E as Elaboration_State {up, ...}) =
    (Unification.instantiate up st, E)


  fun collect_constraints ctxt
    (Delta : (string * term * typ) list)       (* Names and types of loose bounds *)
    (t : term)
    (E : elaboration_state)                (* Types of frees and vars, constraints *)
    (expected_type : term option)
    : (term * elaboration_state) =
    case t of 
     (* special case: explicit type annotation *)
     Const (\<^const_name>\<open>with_type\<close>, _) $ s $ A =>
       let
         val (st, E1) = collect_constraints' ctxt Delta s E NONE
         val new_constraint = (Delta, (st, A), ())
       in
         (st, add_constraint ctxt new_constraint E1)
       end
    | Const (_, T) => 
        let
          (* If constant type cannot be found, invent a generic type *)
          val st = (case get_const_type E t of SOME st => st | NONE => Soft_Type.mk_any_fun T)
          (* Ensure that unification variables are fresh for each constant occurrence
             and make them depend on the current binders. *)
          val binder_types = rev (map #3 Delta)
          val bounds = (length Delta - 1) downto 0
          val (idx, E1) = fresh_idx E
          fun lift_var d (Var ((n, 0), T)) =
                Term.list_comb (Var ((n, idx), binder_types ---> T), map (fn i => Bound (d + i)) bounds)
            | lift_var _ (Var _) = error "Illegal Var index"
            | lift_var _ t = t
          val const_type = map_aterms_lev lift_var st
        in
          (const_type, E1)
        end
    | s $ u => 
        let
          val (fun_type, E1) = 
            collect_constraints' ctxt Delta s E NONE
            |> ensure_function ctxt Delta s
          val (_, A, B) = Soft_Type.dest_Pi_type fun_type
          val (u_st, E2) = collect_constraints' ctxt Delta u E1 (SOME A)
          val new_constraint = (Delta, (u_st, A), ())
          val application_type = Term.subst_bound (u, B)
        in
          (application_type, add_constraint ctxt new_constraint E2)
        end
    | Bound i => (#2 (nth Delta i), E)
    | Abs (x, T, body) => 
        let 
          (* Invent variable for the domain *)
          val (stvar, E2) = fresh_variable T Delta E

          (* Inner context *)
          val Delta' = incr_bounds ((x, stvar, T) :: Delta)

          val bodyT = Term.fastype_of1 (map #3 Delta', body)

          (* Infer type of the body *)
          val (body_st, E3) =
            collect_constraints' ctxt Delta' body E2 NONE
          (* Build a function type *)
          val st = Soft_Type.Pi_const T bodyT $ stvar $ Abs (x, T, body_st)
        in
          (st, E3)
        end
    | t => (* Variable cases: Var and Free *)
        (case get_var_type E t of
          SOME st => (st, E)
        | NONE => fix_var_type [] t (fastype_of t) E) (* Free variable types have no dependencies: Delta = [] *)

   and ensure_function ctxt Delta f (st, E) =
     case st of
         Const (\<^const_name>\<open>Pi_type\<close>, _) $ _ $ Abs _ => (st, E)
       | _ => 
         let
           val fT = Term.fastype_of1 (map #3 Delta, f)
           val domainT = domain_type fT
           val rangeT = range_type fT
           val (A_var, E1) = fresh_variable domainT Delta E
           val Delta' = if Config.get ctxt simple_types then Delta else (("", A_var, domainT) :: Delta)
           val (B_var, E2) = fresh_variable (range_type fT) Delta' E1
           val fun_st = Soft_Type.Pi_const domainT rangeT $ A_var $ Abs ("", domainT, B_var)
           val E3 = add_constraint ctxt (Delta, (st, fun_st), ()) E2
         in
           (fun_st, E3)
         end  

   and collect_constraints' ctxt Delta t E expected_type =
     let 
       fun inst t = Term.subst_bounds (map (fn (n, _, T) => Free (n, T)) Delta, t)
       fun pr_term t = Syntax.string_of_term ctxt (inst t)
     in
      collect_constraints ctxt Delta t E expected_type
      |> instantiate
      |> tap (fn (sT, _) => Soft_Type.tracing ctxt (
            Unification.pr_binders Delta ^ " |- " ^ pr_term t ^ " : " ^ pr_term sT))
     end


fun collect_constraints_prop ctxt
    (Delta : (string * term * typ) list)
    (t : term)
    (E : elaboration_state) =
  case t of
    Const ("HOL.Trueprop", _) $ arg =>
      collect_constraints ctxt Delta arg E NONE |> snd
  | Const ("Pure.implies", _) $ u $ s =>
      E
      |> collect_constraints_prop ctxt Delta u
      |> collect_constraints_prop ctxt Delta s
  | Const ("Pure.eq", _) $ u $ s =>
      E
      |> collect_constraints_prop ctxt Delta u
      |> collect_constraints_prop ctxt Delta s
  | Const ("Pure.all", _) $ Abs (x, T, b) =>
      let
        (* Invent variable for the domain *)
        val (stvar, E2) = fresh_variable T Delta E
      in
        collect_constraints_prop ctxt (incr_bounds ((x, stvar, T) :: Delta)) b E2
      end
  | Const ("Pure.type", _) => E
  | _ => collect_constraints ctxt Delta t E NONE |> snd


datatype elaboration_result =
  Elaboration_Result of {
    elaborated_terms: term list,
    variable_types: (term * term) list
  }


fun infer_type ctxt ts = 
  let
    val const_types = 
      Option.map (#2 o Soft_Type.dest_typing o Thm.prop_of) o Soft_Type_Context.get_current_type ctxt

    val maxidx = fold Term.maxidx_term ts ~1

    val ictxt = Elaboration_State {
        const_types = const_types,
        var_types = Termtab.empty,
        up = Unification.init (maxidx + 1)
      }
    val Elaboration_State {up, var_types, ...} =
       fold (collect_constraints_prop ctxt []) ts ictxt

    val type_simps = Named_Theorems.get ctxt \<^named_theorems>\<open>type_simp\<close>
    val up' = Unification.unify ctxt type_simps up
    fun instantiate t = Unification.instantiate up' t
    val elaborated_terms = map instantiate ts

    val types_for_vars =
      (map Free (fold Term.add_frees elaborated_terms [])) @ (map Var (fold Term.add_vars elaborated_terms []))
      |> map_filter (fn v => case Termtab.lookup var_types v of SOME t => SOME (v, instantiate t) | _ => NONE)
  in
    Elaboration_Result {
      elaborated_terms = elaborated_terms,
      variable_types = types_for_vars
    }
  end 


fun trace_infer_result ctxt (Elaboration_Result {elaborated_terms, variable_types }) =
  let
    fun section header content = header :: map (prefix "  ") content

    val pr_term = Syntax.string_of_term ctxt
  in
    Soft_Type.tracing ctxt (cat_lines ("--- Elaboration result ---" ::
      flat [
        section "Instantiated terms" (map pr_term elaborated_terms),
        section "Variable types" (map (fn (v, st) => pr_term v ^ ": " ^ pr_term st) variable_types)
      ]))
  end

fun annotate_terms env ts =
  let
    fun annot_var t env =
      case AList.lookup (op aconv) env t of
          SOME st => (Soft_Type.annotate st t, AList.delete (op aconv) t env)
        | NONE => (t, env)
    fun annot t env = case t of
        Var _ => annot_var t env
      | Free _ => annot_var t env
      | Const (\<^const_name>\<open>with_type\<close>, T) $ u $ A =>
         if is_Free u orelse is_Var u
         then (t, AList.delete (op aconv) u env)
         else let val (u', env') = annot u env in
           (Const (\<^const_name>\<open>with_type\<close>, T) $ u' $ A, env')
         end
      | Const _ => (t, env)
      | s $ u => 
          let
            val (s', env') = annot s env
            val (u', env'') = annot u env'
          in (s' $ u', env'') end
      | Abs (x, T, b) => let val (b', env') = annot b env in (Abs (x, T, b'), env') end
      | Bound i => (Bound i, env)
  in
    fst (fold_map annot ts env)
  end

fun elaborate_terms ctxt ts =
  let
    val (ts', _) = fold_map Implicit_Arguments.replace_iargs ts 0
    val Elaboration_Result {elaborated_terms, variable_types } =
      infer_type ctxt ts'
      |> tap (trace_infer_result ctxt)

    val (ets', variable_types') = Type_Classes.refine_classes ctxt elaborated_terms variable_types

    (* Insert information about the variables into the elaborated terms *)
    val ets'' = annotate_terms variable_types' ets'

    (* We discard the resulting context, since the terms will be re-declared using auto-fixes
       later *)
    val (ets''', _) = Variable.import_terms true ets'' ctxt

    val _ = Soft_Type.tracing ctxt (cat_lines ("Elaborated terms:"
      :: map (Syntax.string_of_term ctxt) ets'''))
  in
    ets'''
  end


(* Install check phase (when activated in the configuration) *)
val _ = Context.>> (Syntax_Phases.term_check 5 "elaboration" (fn ctxt =>
  if Config.get ctxt auto_elaborate then elaborate_terms ctxt else I))


(* Testing *)


fun assert_result ctxt expected ts =
  let
    val result = elaborate_terms ctxt ts
    fun section header content = header :: map (prefix "  ") content

    val pr_term = Syntax.string_of_term ctxt
  in
    if result <> expected
    then error (cat_lines (flat [
        section "Expected result:" (map pr_term expected),
        section "Actual result:" (map pr_term result)]))
    else result
end



(* Useful antiquotation for testing *)

fun read_term_dummies ctxt s =
  #1 (Term.replace_dummy_patterns (Syntax.read_term (Proof_Context.allow_dummies ctxt) s) 1);

val _ = Theory.setup (
  ML_Antiquotation.inline_embedded \<^binding>\<open>term_dummies\<close>
    (Scan.peek (Args.named_term o read_term_dummies o Context.proof_of)
      >> (ML_Syntax.atomic o ML_Syntax.print_term)))


end
