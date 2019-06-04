(*  Title:      soft_type_inference.ML
    Author:     Alexander Krauss

Soft type inference.
*)

signature SOFT_TYPE_INFERENCE =
sig

  val print_inferred_types: Proof.context -> term list -> unit;
  val elaborate: Proof.context -> term list -> term list

  val soft_type_inference : bool Config.T

end;

structure Soft_Type_Inference : SOFT_TYPE_INFERENCE =
struct

  val soft_type_inference = Attrib.setup_config_bool \<^binding>\<open>soft_type_inference\<close> (K false)

  (* Similar to Term.map_aterms, but also passes the binder level to f *)
  fun map_aterms_lev f =
    let fun mapt l (Abs (n, T, b)) = Abs (n, T, mapt (l + 1) b)
          | mapt l (t $ u) = mapt l t $ mapt l u
          | mapt l t = f l t
    in mapt 0 end


  (* Context \<Gamma>, which maps variables and constants to their types. Also used to collect constraints
     during inference.
   *)
  datatype inference_context = Inference_Context of {
    const_types: term -> term option,
    var_types: term Termtab.table,
    constraints: unit u_equation list,
    fresh_idx: int
  }

  fun get_const_type (Inference_Context {const_types, ...}) (c : term) =
    const_types c;
  
  fun get_var_type (Inference_Context {const_types, var_types, ...}) (v : term) =
    case const_types v of
      SOME sty => SOME sty
    | NONE => Termtab.lookup var_types v;
  
  fun add_constraint 
         (c as (_, (lhs, rhs), _)) 
         (Gamma as Inference_Context {const_types, var_types, constraints, fresh_idx}) =
    if lhs aconv rhs (* Skip trivial constraints *)
    then Gamma
    else Inference_Context {const_types=const_types, var_types=var_types,
           constraints = insert (op =) c constraints,
           fresh_idx=fresh_idx};
  

  type preproc_context = 
    (string * term * typ) list

  fun context_types (Delta : preproc_context) =
    map (#3) Delta

  fun incr_bounds (Delta : preproc_context) =
    map (fn (n, st, T) => (n, Term.incr_boundvars 1 st, T)) Delta

  fun incr (Inference_Context {const_types, var_types, constraints, fresh_idx}) =
    Inference_Context {const_types=const_types, var_types=var_types, constraints=constraints, fresh_idx=fresh_idx + 1}

  fun fresh_idx (Inference_Context {fresh_idx, ...}) =
    fresh_idx

  fun fresh_variable T Delta Gamma =
    let
      val var_type = context_types Delta ---> Soft_Type.typeT T
    in
      (Term.list_comb (Var (("UU", fresh_idx Gamma), var_type), 
        map Bound ((length Delta) -1 downto 0)),
      incr Gamma)
    end

  fun add_free (v, st) (Inference_Context {const_types, var_types, constraints, fresh_idx}) =
    Inference_Context {const_types=const_types, var_types=Termtab.update_new (v, st) var_types, constraints=constraints, fresh_idx=fresh_idx};

  fun fix_var_type Delta v T Gamma =
    let
      val (stv, Gamma1) = fresh_variable T Delta Gamma
    in
      (stv, add_free (v, stv) Gamma1)
    end

  fun trace_constraint ctxt t (eqn as (_, (lhs, rhs), _)) =
    let
      val context_msg = 
        (case t of SOME t' => " (collected from " ^ Syntax.string_of_term ctxt t' ^ ")" | _ => "")
    in                        
      if (fastype_of lhs <> fastype_of rhs)
      then error (cat_lines ["Bad types in constraint:", 
          "  Constraint: " ^ pr_equation ctxt eqn,
          "  Term: "^ (Option.map (Syntax.string_of_term ctxt) t |> the_default "-")])
      else Soft_Type.tracing ctxt ("Constraint: " ^ pr_equation ctxt eqn ^ context_msg)
    end

  fun collect_constraints ctxt
    (Delta : (string * term * typ) list)       (* Names and types of loose bounds *)
    (t : term)
    (Gamma : inference_context)                (* Types of frees and vars, constraints *)
    (expected_type : term option)
    : (term * inference_context) =
    case t of 
      Const (_, T) => 
        let
          (* If constant type cannot be found, invent a generic type *)
          val st = (case get_const_type Gamma t of SOME st => st | NONE => Soft_Type.mk_any_fun T)
          (* Ensure that unification variables are fresh for each constant occurrence
             and make them depend on the current binders. *)
          val binder_types = rev (map #3 Delta)
          val bounds = (length Delta - 1) downto 0
          val idx = fresh_idx Gamma
          fun lift_var d (Var ((n, 0), T)) =
                Term.list_comb (Var ((n, idx), binder_types ---> T), map (fn i => Bound (d + i)) bounds)
            | lift_var _ (Var _) = error "Illegal Var index"
            | lift_var _ t = t
          val const_type = map_aterms_lev lift_var st
          val _ = Soft_Type.tracing ctxt ("Using Const of type " ^ Syntax.string_of_term ctxt const_type)
        in
          (const_type, incr Gamma)
        end
    | s $ u => 
        let
          val (fun_type, Gamma1) = 
            collect_constraints' ctxt Delta s Gamma NONE
            |> ensure_function Delta s
          val Const (@{const_name "Pi_type"}, _) $ A $ Abs (_, _, B) = fun_type
          val (u_st, Gamma2) = collect_constraints' ctxt Delta u Gamma1 (SOME A)
          val new_constraint = (Delta, (u_st, A), ())
            |> tap (trace_constraint ctxt (SOME t))
          val application_type = Term.subst_bound (u, B)
        in
          (application_type, add_constraint new_constraint Gamma2)
        end
    | Bound i => (#2 (nth Delta i), Gamma)
    | Abs (x, T, body) => 
        let 
          (* Invent variable for the domain *)
          val (stvar, Gamma2) = fresh_variable T Delta Gamma

          (* Inner context *)
          val Delta' = incr_bounds ((x, stvar, T) :: Delta)

          val bodyT = Term.fastype_of1 (map #3 Delta', body)

          (* Infer type of the body *)
          val (body_st, Gamma3) =
            collect_constraints' ctxt Delta' body Gamma2 NONE
          (* Build a function type *)
          val st = Soft_Type.Pi_const T bodyT $ stvar $ Abs (x, T, body_st)
        in
          (st, Gamma3)
        end
    | t => (* Variable cases: Var and Free *)
        (case get_var_type Gamma t of
          SOME st => (st, Gamma)
        | NONE => fix_var_type [] t (fastype_of t) Gamma) (* Free variable types have no dependencies: Delta = [] *)

   and ensure_function Delta f (st, Gamma) =
     case st of
         Const (@{const_name "Pi_type"}, _) $ _ $ Abs _ => (st, Gamma)
       | _ => 
         let
           val fT = Term.fastype_of1 (map #3 Delta, f)
           val domainT = domain_type fT
           val rangeT = range_type fT
           val (A_var, Gamma1) = fresh_variable domainT Delta Gamma
           val (B_var, Gamma2) = fresh_variable (range_type fT) (("", A_var, domainT) :: Delta) Gamma1
           val fun_st = Soft_Type.Pi_const domainT rangeT $ A_var $ Abs ("", domainT, B_var)
         in
           (fun_st, Gamma2)
         end  

   and collect_constraints' ctxt Delta t Gamma expected_type =
     let 
       val _ = Soft_Type.tracing ctxt (cat_lines [
         "collect_constraints:",
         "  \<Delta> = " ^ @{make_string} Delta,
         "  t = " ^ Syntax.string_of_term ctxt t])
     in
      collect_constraints ctxt Delta t Gamma expected_type
      |> tap (fn (sT, _) => Soft_Type.tracing ctxt (cat_lines [
            "### " ^ Syntax.string_of_term ctxt t,
            "--> " ^ Syntax.string_of_term ctxt sT]))
     end


fun collect_constraints_prop ctxt
    (Delta : (string * term * typ) list)
    (t : term)
    (Gamma : inference_context) =
  case t of
    Const ("HOL.Trueprop", _) $ arg =>
      collect_constraints ctxt Delta arg Gamma NONE |> snd
  | Const ("Pure.implies", _) $ u $ s =>
      Gamma
      |> collect_constraints_prop ctxt Delta u
      |> collect_constraints_prop ctxt Delta s
  | Const ("Pure.eq", _) $ u $ s =>
      Gamma
      |> collect_constraints_prop ctxt Delta u
      |> collect_constraints_prop ctxt Delta s
  | Const ("Pure.all", _) $ Abs (x, T, b) =>
      let
        (* Invent variable for the domain *)
        val (stvar, Gamma2) = fresh_variable T Delta Gamma
      in
        collect_constraints_prop ctxt (incr_bounds ((x, stvar, T) :: Delta)) b Gamma2
      end
  | Const ("Pure.type", _) => Gamma
  | _ => collect_constraints ctxt Delta t Gamma NONE |> snd


datatype infer_result =
  Infer_Result of {
    elaborated_terms: term list,
    variable_types: (term * term) list
  }



fun unify_constraints ctxt constraints fresh_idx =
  let
    val type_simps = Named_Theorems.get ctxt @{named_theorems "type_simp"}
    val up = init_up constraints fresh_idx type_simps
  in 
    unify ctxt up
  end

fun infer_type ctxt ts = 
  let
    val const_types = 
      Option.map (#2 o Soft_Type_Context.dest_typing o Thm.prop_of) o Soft_Type_Context.get_current_type (Context.Proof ctxt)

    val maxidx = fold Term.maxidx_term ts ~1

    val ictxt = Inference_Context {
        const_types = const_types,
        var_types = Termtab.empty,
        constraints = [],
        fresh_idx = maxidx + 1
      }
    val Inference_Context {constraints, var_types, fresh_idx, ...} =
       fold (collect_constraints_prop ctxt []) ts ictxt
    
    val _ = Soft_Type.tracing ctxt "Original constraints: "   
    val _ = map (trace_constraint ctxt NONE) constraints

    val env = unify_constraints ctxt constraints fresh_idx
    fun instantiate t = instantiate_term env t
    val elaborated_terms = map instantiate ts

    val types_for_vars =
      (map Free (fold Term.add_frees elaborated_terms [])) @ (map Var (fold Term.add_vars elaborated_terms []))
      |> map_filter (fn v => case Termtab.lookup var_types v of SOME t => SOME (v, instantiate t) | _ => NONE)
  in
    Infer_Result {
      elaborated_terms = elaborated_terms,
      variable_types = types_for_vars
    }
  end 


fun trace_infer_result ctxt (Infer_Result {elaborated_terms, variable_types }) =
  let
    fun section header content = header :: map (prefix "  ") content

    val pr_term = Syntax.string_of_term ctxt
  in
    Soft_Type.tracing ctxt (cat_lines ("--- Inference result ---" ::
      flat [
        section "Instantiated terms" (map pr_term elaborated_terms),
        section "Variable types" (map (fn (v, st) => pr_term v ^ ": " ^ pr_term st) variable_types)
      ]))
  end

fun print_inferred_types ctxt ts = trace_infer_result ctxt (infer_type ctxt ts)


fun elaborate ctxt ts =
  if Config.get ctxt soft_type_inference then
    let
      val (ts', _) = fold_map Implicit_Arguments.replace_iargs ts 0
      val Infer_Result {elaborated_terms, ... } =
        infer_type ctxt ts'
        |> tap (trace_infer_result ctxt)

      (* We discard the resulting context, since the terms will be re-declared using auto-fixes
         later *)
      val (ets', _) = Variable.import_terms true elaborated_terms ctxt
    in
      ets'
    end
  else ts;

(* No effect until activated in the configuration *)
val _ = Context.>> (Syntax_Phases.term_check 5 "elaboration" elaborate)


(* Useful antiquotation for testing *)

fun read_term_dummies ctxt s =
  #1 (Term.replace_dummy_patterns (Syntax.read_term (Proof_Context.allow_dummies ctxt) s) 1);

val _ = Theory.setup (
  ML_Antiquotation.inline \<^binding>\<open>term_dummies\<close> (* TODO: Isabelle 2019 -> inline_embedded *)
    (Scan.peek (Args.named_term o read_term_dummies o Context.proof_of)
      >> (ML_Syntax.atomic o ML_Syntax.print_term)))


end
