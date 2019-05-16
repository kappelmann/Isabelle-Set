(*  Title:      soft_type_inference.ML
    Author:     Alexander Krauss

Soft type inference.
*)

signature SOFT_TYPE_INFERENCE =
sig

datatype constraint =
  Eq of term * term  (* equality *)

(* Context \<Gamma>, which maps variables and constants to their types. Also used to collect constraints
   during inference.
 *)
datatype inference_context =
  Inference_Context of {
    var_types: term Termtab.table,
    constraints: constraint list,
    fresh_idx: int
  }

val init_context: (term * term) list -> inference_context

val print_inferred_types: Proof.context -> term list -> unit

end

structure Soft_Type_Inference : SOFT_TYPE_INFERENCE =
struct

datatype constraint =
  Eq of term * term

datatype inference_context =
  Inference_Context of {
    var_types: term Termtab.table,
    constraints: constraint list,
    fresh_idx: int
  }

fun init_context (vts : (term * term) list) =
  Inference_Context {
    var_types = Termtab.make vts,
    constraints = [],
    fresh_idx = 0
}

fun get_var_type (Inference_Context {var_types, ...}) (v : term) =
  Termtab.lookup var_types v

fun add_constraint
  (c as Eq (lhs, rhs))
  (Gamma as Inference_Context {var_types, constraints, fresh_idx}) =
  if lhs aconv rhs (* Skip trivial constraints *)
  then Gamma
  else Inference_Context {
    var_types=var_types,
    constraints = insert (op =) c constraints,
    fresh_idx=fresh_idx
  }

type preproc_context = 
  (string * term * typ) list

fun context_types (Delta : preproc_context) =
  map (#3) Delta

fun incr_bounds (Delta : preproc_context) =
  map (fn (n, st, T) => (n, Term.incr_boundvars 1 st, T)) Delta

fun incr (Inference_Context {var_types, constraints, fresh_idx}) =
  Inference_Context {var_types=var_types, constraints=constraints, fresh_idx=fresh_idx + 1}

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

fun add_free (v, st) (Inference_Context {var_types, constraints, fresh_idx}) =
  Inference_Context {
    var_types = Termtab.update_new (v, st) var_types,
    constraints = constraints,
    fresh_idx = fresh_idx
  }

fun fix_var_type v T Gamma Delta =
  let
    val (stv, Gamma1) = fresh_variable T Gamma Delta
  in
    (stv, add_free (v, stv) Gamma1)
  end

fun abstract_constraint Delta (Eq (s, t)) =
  let
    val abstract = fold (fn (x, _, T) => Term.abs (x, T)) Delta
  in
    Eq (abstract s, abstract t)
  end    

fun trace_constraint ctxt (Eq (s, t)) =
  let
    val pr = Syntax.string_of_term ctxt
  in 
    if (fastype_of s <> fastype_of t)
    then error ("Bad types in constraint:" ^ pr s ^ " === " ^ pr t)
    else Output.tracing ("Constraint " ^ pr s ^ " === " ^ pr t)
  end

fun collect_constraints ctxt
  (Gamma : inference_context)
  (Delta : (string * term * typ) list)
  (t : term)
  (expected_type : term option) 
  : (term * inference_context) =
  case t of
    Free (_, T) => 
      (case get_var_type Gamma t of
        SOME st => (st, Gamma)
      | NONE => 
          (case expected_type of 
             SOME exp => (exp, add_free (t, exp) Gamma)
           | NONE => fix_var_type t T Gamma []) (* Free variable types have no dependencies: Delta = [] *)
      )
  | Const (n, _) => 
      (case get_var_type Gamma t of
        SOME st => (st, Gamma)
      | NONE => error ("Cannot resolve type of constant " ^ quote n))
  | s $ u => 
      (case collect_constraints' ctxt Gamma Delta s NONE of
        (Const (@{const_name "Pi_type"}, _) $ A $ Abs (_, _, B), Gamma1) =>
          let
            val (u_st, Gamma2) = collect_constraints' ctxt Gamma1 Delta u (SOME A)
            val new_constraint = Eq (u_st, A)
              |> abstract_constraint Delta
              |> tap (trace_constraint ctxt)
            val application_type = Term.subst_bound (u, B)
          in
            (application_type, add_constraint new_constraint Gamma2)
          end
      | (s_st, _) => error ("Bad soft type for application head: " ^ Syntax.string_of_term ctxt s 
                    ^ " ::: " ^ Syntax.string_of_term ctxt s_st))
  | Bound i => (#2 (nth Delta i), Gamma)
  | Var _ => error "illegal Var"
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
    term_types: term list,
    variable_types: (term * term) list,
    constraints: (term * term) list
  }




fun preprocess_constraints ctxt constraints =
  let

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

    val type_simp_rules = 
      Named_Theorems.get ctxt @{named_theorems "type_simp"}
      |> map (Raw_Simplifier.mksimps ctxt)
      |> flat

    val transform_term =
      Term.map_aterms to_free
      #> Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) type_simp_rules []
      #> Term.map_aterms to_var
  in
    map (fn Eq(s, t) => Eq (transform_term s, transform_term t)) constraints
  end 




fun unify_constraints ctxt constraints maxidx =
  Seq.hd (Unify.smash_unifiers (Context.Proof ctxt) (map (fn Eq e => e) constraints) (Envir.empty maxidx))

fun infer_type ctxt ts = 
  let
    val var_types = Soft_Type_Context.Ctxt.get (Context.Proof ctxt)
      |> Termtab.map (K (#2 o Soft_Type_Context.dest_typing o Thm.prop_of))

    val ictxt = Inference_Context {
        var_types = var_types,
        constraints = [],
        fresh_idx = 0
      }
    val (sTs, Inference_Context {constraints, var_types, fresh_idx}) =
       fold_map (fn t => fn c => collect_constraints' ctxt c [] t NONE) ts ictxt
    
    val _ = Output.tracing "Original constraints: "   
    val _ = map (trace_constraint ctxt) constraints

    val simplified_constraints = preprocess_constraints ctxt constraints

    val _ = Output.tracing "Simplified constraints: "   
    val _ = map (trace_constraint ctxt) simplified_constraints

    val env = unify_constraints ctxt simplified_constraints fresh_idx
    val instantiated = map (Envir.norm_term env) sTs

    val types_for_frees =
      fold Term.add_frees ts []
      |> map (fn f => 
          (Free f, 
          Termtab.lookup var_types (Free f) |> the |> Envir.norm_term env))
  in
    Infer_Result {
      term_types = instantiated,
      variable_types = types_for_frees,
      constraints = []
    }
  end 

fun print_inferred_types ctxt ts = 
  let
    val Infer_Result {term_types, variable_types, constraints} = infer_type ctxt ts

    fun section header content = header :: map (prefix "  ") content

    val pr_term = Syntax.string_of_term ctxt

    val _ = Output.writeln (cat_lines ("--- Inference result ---" ::
      flat [
        section "Types of terms" (map pr_term term_types),
        section "Variable types" (map (fn (v, st) => pr_term v ^ ": " ^ pr_term st) variable_types),
        section "Constraints" (map (fn (s, t) => pr_term s ^ " = " ^ pr_term t) constraints)
      ]))
  in () end

end
