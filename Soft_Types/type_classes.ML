(*  Title:      type_classes.ML
    Author:     Alexander Krauss

Type classes based on soft types.
*)

signature TYPE_CLASSES =
sig

(* TODO *)


end;

structure Type_Classes(*: TYPE_CLASSES*) =
struct


(* For now, hardcode this information, which must be configurable *)
fun is_class_type t =
  case t of
    Const ("Monoid_Class.Monoid", _) $ _ => true
  | _ => false


(* Tracing *)

fun pr_subst ctxt (Envir.Envir {tenv, ...}) = 
  let val pr_term = Syntax.string_of_term ctxt in
    Vartab.dest tenv
    |> map (fn (ixn, t) => pr_term (Var (ixn, dummyT)) ^ " ~> " ^ pr_term (snd t))
    |> cat_lines
  end


fun apply_instance_rule ctxt (rule: thm) (goals: term list, env, subst) =
  let
    val head_goal = hd goals
    val _ = Output.tracing ("Attempt Rule " ^ Syntax.string_of_term ctxt 
      (Thm.prop_of rule) ^ " on: " ^ Syntax.string_of_term ctxt head_goal)
    val concl = HOLogic.dest_Trueprop (Thm.concl_of rule)
    val subst' = Pattern.unify (Context.Proof ctxt) (concl, head_goal) subst
    val _ = Soft_Type.tracing ctxt ("Substitution:\n" ^ pr_subst ctxt subst')
    fun inst t = Envir.norm_term subst' t
    val subgoals = Thm.prems_of rule
    val new_goals = map inst (subgoals @ tl goals)
    val _ = Output.tracing (cat_lines ("New goals:" :: map (Syntax.string_of_term ctxt) new_goals))
  in
    SOME (new_goals, env, subst')
  end
  handle Pattern.Unif => (Output.tracing "No unifier found"; NONE)



fun assume_class ctxt goal env subst =
  let val (var, cls_type) = Soft_Type.dest_typing goal 
  val _ = Output.tracing ("Looking for entry for " ^ Syntax.string_of_term ctxt cls_type) in
  case find_first (fn assm =>
      snd (Soft_Type.dest_typing assm) aconv cls_type) env of
      SOME assm => 
        let
          val assm_var = fst (Soft_Type.dest_typing assm)
          val subst' = Envir.vupdate (dest_Var var, assm_var) subst
          val _ = Soft_Type.tracing ctxt ("Substitution:\n" ^ pr_subst ctxt subst')
        in
          (env, subst')
        end
    | NONE => (goal :: env, subst)
  end        


(* Checks if the goal is about a type variable and resolves it from
  the (local) environment, possibly extending it. *)
fun resolve_type_variable ctxt (goals, env, subst) =
  let
    val head_goal = hd goals
    val _ = Output.tracing ("Attempt TypeVar: " ^ Syntax.string_of_term ctxt head_goal)
    val (_, cls_type) = Soft_Type.dest_typing head_goal
 
    fun is_var_class t = 
      forall (fn s => is_Var s orelse is_Free s) (snd (strip_comb t))
  in
    if not (is_var_class cls_type) then NONE else let
    val (env', subst') = assume_class ctxt head_goal env subst
  in
    SOME (tl goals, env', subst')
  end end

fun resolve_instance ctxt rules state =
    map_filter (fn rule => apply_instance_rule ctxt rule state) rules

fun step ctxt rules state =
  case resolve_type_variable ctxt state of
    SOME result => [result]
  | _ => resolve_instance ctxt rules state

fun is_solved ([], _, _) = true
  | is_solved _ = false

fun search _ [] = error "No solution"
  | search f (x::xs) =
      if is_solved x then x else search f (f x @ xs)

fun import_class_goals ctxt goals =
  let
    fun protect_var goal =
      let 
        val var = Soft_Type.dest_typing goal |> fst |> dest_Var
        val goal' = Term.map_aterms (fn t => case t of 
           Var (v, T) => if v = fst var then Free ("_protect_", T) else t 
           | _ => t) goal
      in
        (var, goal')
      end
    
    fun unprotect var = Term.map_aterms (fn t => case t of
         Free ("_protect_", T) => Var (fst var, T) | _ => t)
      
    val (vars, goals') = split_list (map protect_var goals)
    val (igoals', ctxt') = Variable.import_terms true goals' ctxt
    val igoals = map2 unprotect vars igoals'
  in
    (igoals, ctxt')
  end

(*
  Exports an environment.
  Only operates on term substitutions, since type substitutions are not relevant in our context
*)
fun export_envir inner_ctxt outer_ctxt (Envir.Envir {maxidx, tenv, tyenv}) =
  let
    val export_term = singleton (Variable.export_terms inner_ctxt outer_ctxt)
    fun export_tenv tenv = 
      tenv
      |> Vartab.dest
      |> map (apsnd (apsnd export_term))
      |> filter (fn (key, (_, v)) => not (is_Var v) orelse not (fst (dest_Var v) = key))
      |> Vartab.make
  in 
    Envir.Envir {maxidx=maxidx, tenv=export_tenv tenv, tyenv=tyenv}
  end


fun compute_instances ctxt (goals: term list) = 
  let
    val rules = Named_Theorems.get ctxt \<^named_theorems>\<open>type_instance\<close>
    val (imported_goals, ctxt') = import_class_goals ctxt goals
    val init_state = [(imported_goals, [], Envir.init)]
    val (leftover_goals, env, subst) = search (step ctxt' rules) init_state
    val _ = if not (leftover_goals = [])
      then error (cat_lines ("Cannot resolve instances:" ::
        map (Syntax.string_of_term ctxt) leftover_goals))
      else ()
  in
    (Variable.export_terms ctxt' ctxt env, export_envir ctxt' ctxt subst)
  end



fun refine_classes ctxt variable_types =
  let
    val open_class_constraints =
      variable_types
      |> filter (fn (v, t) => Term.is_Var v andalso is_class_type t)
      |> map (Soft_Type.mk_typing)
  
    val (env, subst) = compute_instances ctxt open_class_constraints
  in
    (env, subst)
  end




end
