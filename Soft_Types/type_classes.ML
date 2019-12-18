(*  Title:      type_classes.ML
    Author:     Alexander Krauss

Type classes based on soft types.
*)

signature TYPE_CLASSES =
sig

val get_type_classes: Proof.context -> term Item_Net.T
val put_type_class: term -> Context.generic -> Context.generic
val refine_classes: Proof.context -> term list -> (term * term) list
  -> (term list * (term * term) list)

end;

structure Type_Classes: TYPE_CLASSES =
struct

(* Type class declarations *)

structure Type_Class_Data = Generic_Data (
  type T = term Item_Net.T
  val empty = Item_Net.init Term.aconv single
  val extend = I
  val merge = Item_Net.merge
)

val get_type_classes = Type_Class_Data.get o Context.Proof
val put_type_class = Type_Class_Data.map o Item_Net.update

fun is_class_type ctxt tm = Item_Net.member (get_type_classes ctxt) (head_of tm)

val typeclass_parser =
  Scan.lift (Scan.succeed (Thm.declaration_attribute (fn thm =>
    put_type_class (head_of (#1 (Soft_Type.dest_eq (Thm.prop_of thm))))
    #> Named_Theorems.add_thm \<^named_theorems>\<open>typedef\<close> thm
  )))

val _ =
  Theory.setup (Attrib.setup \<^binding>\<open>typeclass\<close> typeclass_parser "define typeclass")


(* Tracing *)

fun pr_subst ctxt (Envir.Envir {tenv, ...}) = 
  let val pr_term = Syntax.string_of_term ctxt in
    Vartab.dest tenv
    |> map (fn (ixn, t) => pr_term (Var (ixn, dummyT)) ^ " ~> " ^ pr_term (snd t))
    |> cat_lines
  end

fun maxidx_of_state (goals, env, subst) =
  Int.max (fold Term.maxidx_term goals (fold Term.maxidx_term env 0), Envir.maxidx_of subst)

fun apply_instance_rule ctxt (rule: thm) (state as (goals: term list, env, subst)) =
  let
    val rule' = Thm.incr_indexes (maxidx_of_state state + 1) rule
    val head_goal = hd goals
    val _ = Output.tracing ("Attempt Rule " ^ Syntax.string_of_term ctxt 
      (Thm.prop_of rule') ^ " on: " ^ Syntax.string_of_term ctxt head_goal)
    val concl = HOLogic.dest_Trueprop (Thm.concl_of rule')
    val subst' = Pattern.unify (Context.Proof ctxt) (concl, head_goal) subst
    val _ = Soft_Type.tracing ctxt ("Substitution:\n" ^ pr_subst ctxt subst')
    fun inst t = Envir.norm_term subst' t
    val subgoals = Thm.prems_of rule' |> map HOLogic.dest_Trueprop
    val new_goals = map inst (subgoals @ tl goals)
  in
    SOME (new_goals, map inst env, subst')
  end
  handle Pattern.Unif => (Output.tracing "No unifier found"; NONE)

fun assume_class ctxt goal env subst =
  let val (var, cls_type) = Soft_Type.dest_typing goal 
  val _ = Output.tracing ("Looking for entry for " ^ Syntax.string_of_term ctxt goal)
  val is_side_condition = not (is_Var var)
  in 
    if is_side_condition
    then
      (*Side conditions must be part of the environment already. Then they are discharged.*)
      if exists (fn assm => assm aconv goal) env
      then (env, subst)
      else raise TERM ("Cannot discharge side condition", [goal])
    else
      (*If we already have an assumption for the same class, it will be reused (via variable
        renaming).*)
      case find_first (fn assm => snd (Soft_Type.dest_typing assm) aconv cls_type) env of
          SOME assm => 
            let
              val _ = Soft_Type.tracing ctxt ("Found assumption: " ^ Syntax.string_of_term ctxt assm)
              val assm_var = fst (Soft_Type.dest_typing assm)
              val subst' = Envir.vupdate (dest_Var var, assm_var) subst
              val _ = Soft_Type.tracing ctxt ("Substitution:\n" ^ pr_subst ctxt subst')
            in
              (env, subst')
            end
      (*If no assumption was found, just add it to the environment*)
    | NONE => (goal :: env, subst)
  end        


(* Checks if the goal is about a type variable and resolves it from
  the (local) environment, possibly extending it. *)
fun resolve_type_variable ctxt (goals, env, subst) =
  let
    val head_goal = hd goals
    val _ = Soft_Type.tracing ctxt ("Attempt TypeVar: " ^ Syntax.string_of_term ctxt head_goal)
    val (_, cls_type) = Soft_Type.dest_typing head_goal
 
    val (head, args) = strip_comb cls_type
    val is_composite = is_class_type ctxt head andalso exists (not o is_Free) args
  in
    if is_composite then NONE else let
    val (env', subst') = assume_class ctxt head_goal env subst
  in
    SOME (tl goals, env', subst')
  end end

fun resolve_instance ctxt rules state =
    map_filter (fn rule => apply_instance_rule ctxt rule state) rules

fun step ctxt rules state =
  let
    fun section header content = header :: map (prefix "  ") content
    val pr_term = Syntax.string_of_term ctxt

    val _ = Soft_Type.tracing ctxt (cat_lines ("Class constraint problem:" :: flat [
        section "Goals" (map pr_term (#1 state)),
        section "Env" (map pr_term (#2 state))
      ]))
  in case resolve_type_variable ctxt state of
    SOME result => [result]
  | _ => resolve_instance ctxt rules state
  end

fun is_solved ([], _, _) = true
  | is_solved _ = false

fun search _ [] = error "No solution"
  | search f (x::xs) =
      if is_solved x then x else search f (f x @ xs)


(* Partial import operation: Replaces all Vars by fresh fixed variables, except for the ones given by
   keep_vars.

   Returns the new context and the export operation.
*)
fun partial_import ctxt keep_vars goals =
  let
    val other_vars = subtract (op =) keep_vars (fold Term.add_vars goals [])

    val (fixes, ctxt') = Variable.variant_fixes (map (fst o fst) other_vars) ctxt
    val vpairs = map2 (fn f => fn (ixn, T) => (Free (f, T), Var (ixn, T))) fixes other_vars

    fun replace alist = Term.map_aterms (perhaps (AList.lookup (op =) alist))

    val import = replace (map swap vpairs)
    val export = replace vpairs
  in
    (map import goals, ctxt', export)
  end


fun refine_classes ctxt terms variable_types =
  let
    (* Fix all variables except for the dictionary variables, to ensure that they are not
       accidentally instantiated. *)
    val dict_vars =
      variable_types
      |> map_filter (fn (v, t) =>
let val _ = (@{print} "hi";@{print} t) in
           if Term.is_Var v andalso is_class_type ctxt t then SOME (dest_Var v) else NONE end)
    val (env, ctxt', export) = partial_import ctxt dict_vars (map Soft_Type.mk_typing variable_types)

    fun is_goal t = Term.is_Var (fst (Soft_Type.dest_typing t))
    val goals = filter is_goal env
    val side_conditions = filter_out is_goal env
    val init_state = [(goals, side_conditions, Envir.init)]

    val rules = Named_Theorems.get ctxt \<^named_theorems>\<open>type_instance\<close>
    val (leftover_goals, env, subst) = search (step ctxt' rules) init_state
    val _ = if not (leftover_goals = [])
      then error (cat_lines ("Cannot resolve instances:" ::
        map (Syntax.string_of_term ctxt) leftover_goals))
      else ()


    val ets = map (Envir.norm_term subst) terms
    val _ = Output.tracing ("Env: " ^ cat_lines (map (Syntax.string_of_term ctxt') env))     
    val _ = Output.tracing ("Terms: " ^ cat_lines (map (Syntax.string_of_term ctxt') ets))

    val env = map export env
    val ets' = map export ets

    val _ = Output.tracing ("Exported Env: " ^ cat_lines (map (Syntax.string_of_term ctxt) env))
    val _ = Output.tracing ("Exported Terms: " ^ cat_lines (map (Syntax.string_of_term ctxt) ets'))

    val variable_types' = map Soft_Type.dest_typing env
  in
    (ets', variable_types')
  end




end
