(*  Title:      soft_type_inference.ML
    Author:     Alexander Krauss

Soft type inference.
*)

signature SOFT_TYPE_INFERENCE =
sig


  val print_inferred_types: Proof.context -> term list -> unit;

end;

structure Soft_Type_Inference : SOFT_TYPE_INFERENCE =
struct

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

  fun fresh_variable T Gamma Delta =
    let
      val var_type = context_types Delta ---> Soft_Type.typeT T
    in
      (Term.list_comb (Var (("UU", fresh_idx Gamma), var_type), 
        map Bound ((length Delta) -1 downto 0)),
      incr Gamma)
    end

  fun add_free (v, st) (Inference_Context {const_types, var_types, constraints, fresh_idx}) =
    Inference_Context {const_types=const_types, var_types=Termtab.update_new (v, st) var_types, constraints=constraints, fresh_idx=fresh_idx};

  fun fix_var_type v T Gamma Delta =
    let
      val (stv, Gamma1) = fresh_variable T Gamma Delta
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
      else Output.tracing ("Constraint: " ^ pr_equation ctxt eqn ^ context_msg)
    end

  fun collect_constraints ctxt
    (Gamma : inference_context)                (* Types of frees and vars, constraints *)
    (Delta : (string * term * typ) list)       (* Names and types of loose bounds *)
    (t : term)
    (expected_type : term option)
    : (term * inference_context) =
    case t of 
      Const (n, _) => 
        (case get_const_type Gamma t of
          SOME st => 
            let   
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
              val _ = Output.tracing ("Using Const of type " ^ Syntax.string_of_term ctxt const_type)
            in
              (const_type, incr Gamma)
            end
        | NONE => error ("Cannot resolve type of constant " ^ quote n))
    | s $ u => 
        (case collect_constraints' ctxt Gamma Delta s NONE of
          (Const (@{const_name "Pi_type"}, _) $ A $ Abs (_, _, B), Gamma1) =>
            let
              val (u_st, Gamma2) = collect_constraints' ctxt Gamma1 Delta u (SOME A)
              val new_constraint = (Delta, (u_st, A), ())
                |> tap (trace_constraint ctxt (SOME t))
              val application_type = Term.subst_bound (u, B)
            in
              (application_type, add_constraint new_constraint Gamma2)
            end
        | (s_st, _) => error ("Bad soft type for application head: " ^ Syntax.string_of_term ctxt s 
                      ^ " ::: " ^ Syntax.string_of_term ctxt s_st))
    | Bound i => (#2 (nth Delta i), Gamma)
    | Abs (x, T, body) => 
        let 
          (* Invent variable for the domain *)
          val (stvar, Gamma2) = fresh_variable T Gamma Delta

          (* Inner context *)
          val Delta' = incr_bounds ((x, stvar, T) :: Delta)

          val bodyT = Term.fastype_of1 (map #3 Delta', body)

          (* Infer type of the body *)
          val (body_st, Gamma3) =
            collect_constraints' ctxt Gamma2 Delta' body NONE
          (* Build a function type *)
          val st = Soft_Type.Pi_const T bodyT $ stvar $ Abs (x, T, body_st)
        in
          (st, Gamma3)
        end
    | t => (* Variable cases: Var and Free *)
        (case get_var_type Gamma t of
          SOME st => (st, Gamma)
        | NONE => fix_var_type t (fastype_of t) Gamma []) (* Free variable types have no dependencies: Delta = [] *)

   and collect_constraints' ctxt Gamma Delta t expected_type =
     let 
       val _ = Output.tracing (cat_lines [
         "collect_constraints:",
         "  \<Delta> = " ^ @{make_string} Delta,
         "  t = " ^ Syntax.string_of_term ctxt t])
     in
      collect_constraints ctxt Gamma Delta t expected_type
      |> tap (fn (sT, _) => Output.tracing (cat_lines [
            "### " ^ Syntax.string_of_term ctxt t,
            "--> " ^ Syntax.string_of_term ctxt sT]))
     end

datatype infer_result =
  Infer_Result of {
    elaborated_terms: term list,
    term_types: term list,
    variable_types: (term * term) list,
    constraints: (term * term) list
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
      Option.map (#2 o Soft_Type_Context.dest_typing o Thm.prop_of) o Soft_Type_Context.get (Context.Proof ctxt)

    val ictxt = Inference_Context {
        const_types = const_types,
        var_types = Termtab.empty,
        constraints = [],
        fresh_idx = 0
      }
    val (sTs, Inference_Context {constraints, var_types, fresh_idx, ...}) =
       fold_map (fn t => fn c => collect_constraints' ctxt c [] t NONE) ts ictxt
    
    val _ = Output.tracing "Original constraints: "   
    val _ = map (trace_constraint ctxt NONE) constraints

    val env = unify_constraints ctxt constraints fresh_idx
    fun instantiate t = instantiate_term env t
    val term_types = map instantiate sTs
    val elaborated_terms = map instantiate ts

    val types_for_vars =
      (map Free (fold Term.add_frees elaborated_terms [])) @ (map Var (fold Term.add_vars elaborated_terms []))
      |> map_filter (fn v => case Termtab.lookup var_types v of SOME t => SOME (v, instantiate t) | _ => NONE)
  in
    Infer_Result {
      elaborated_terms = elaborated_terms,
      term_types = term_types,
      variable_types = types_for_vars,
      constraints = []
    }
  end 

fun print_inferred_types ctxt ts = 
  let
    val Infer_Result {elaborated_terms, term_types, variable_types, constraints } = infer_type ctxt ts

    fun section header content = header :: map (prefix "  ") content

    val pr_term = Syntax.string_of_term ctxt

    val _ = Output.writeln (cat_lines ("--- Inference result ---" ::
      flat [
        section "Instantiated terms" (map pr_term elaborated_terms),
        section "Types of terms" (map pr_term term_types),
        section "Variable types" (map (fn (v, st) => pr_term v ^ ": " ^ pr_term st) variable_types),
        section "Constraints" (map (fn (s, t) => pr_term s ^ " = " ^ pr_term t) constraints)
      ]))

  in () end 


(* Useful antiquotation for testing *)
val _ = Theory.setup (
   ML_Antiquotation.inline \<^binding>\<open>term_pattern\<close> (Args.term_pattern >> (ML_Syntax.atomic o ML_Syntax.print_term)))


end
