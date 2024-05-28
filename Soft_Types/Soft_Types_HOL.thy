\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Technical Setup For Soft Types\<close>
theory Soft_Types_HOL
  imports
    TBounded_Quantifiers
    TFunctions_Monotone
    Implicit_Arguments
    "HOL-Eisbach.Eisbach"
  keywords
    "opaque" :: thy_decl and
    "soft_type_translation" :: thy_goal_stmt and
    "print_opaque_terms" "print_types" :: diag
begin

unbundle no_HOL_ascii_syntax

paragraph \<open>Summary\<close>
text \<open>This theory contains the automation setup for soft-types for HOL.\<close>

subsection \<open>Low-Level Methods\<close>

(*FUTURE: Dedicated keyword setup for soft type declarations should go here*)

text \<open>Unfold all type information to work only in the underlying theory:\<close>

named_theorems typedef \<comment>\<open>soft type definitions\<close>
named_theorems type_intro \<comment>\<open>soft type introduction rules\<close>
  (*TODO: This should be kept for typechecking, so only introduction rules
    whose premises and conclusion are type judgments should be declared*)

method unfold_types =
  (rule type_intro
  |simp_all only: typedef meaning_of_type meaning_of_adj of_type_type_eq_self
    ball_type_def bex_type_def ball_pred_def bex_pred_def)+

subsection \<open>Dependent Function/Pi-Types (\<Pi>-Types)\<close>

definition [typedef]: "Dep_fun (A :: 'a type) B \<equiv> type ((x : A) \<Rightarrow> B x)"
adhoc_overloading dep_mono_wrt Dep_fun

lemma of_type_Dep_fun_eq_dep_mono_wrt_type [type_to_HOL_simp]:
  "of_type ((x : A) \<Rightarrow> B x) = ((x : A) \<Rightarrow> B x)"
  unfolding Dep_fun_def type_to_HOL_simp by simp

(*TODO: make it a definition*)
abbreviation "Fun A B \<equiv> Dep_fun A (\<lambda>_. B)"
adhoc_overloading mono_wrt Fun

lemma of_type_Fun_eq_mono_wrt_type [type_to_HOL_simp]: "of_type (A \<Rightarrow> B) = (A \<Rightarrow> B)"
  by (simp add: mono_wrt_pred_eq_dep_mono_wrt_pred type_to_HOL_simp)

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
begin

lemma Dep_funI [type_intro]:
  assumes "\<And>x. x \<Ztypecolon> A \<Longrightarrow> f x \<Ztypecolon> B x"
  shows "f \<Ztypecolon> (x : A) \<Rightarrow> B x"
  by (urule dep_mono_wrt_predI) (use assms in simp)

lemma Dep_funE:
  assumes "f \<Ztypecolon> (x : A) \<Rightarrow> B x"
  obtains "\<And>x. x \<Ztypecolon> A \<Longrightarrow> f x \<Ztypecolon> B x"
  using assms by (urule (e) dep_mono_wrt_predE)

lemma Dep_funD:
  assumes "f \<Ztypecolon> (x : A) \<Rightarrow> B x"
  and "x \<Ztypecolon> A"
  shows "f x \<Ztypecolon> B x"
  using assms by (urule dep_mono_wrt_predD)

lemma Dep_fun_cong [cong]:
  assumes "\<And>x. x \<Ztypecolon> A \<longleftrightarrow> x \<Ztypecolon> A'"
  and "\<And>x y. x \<Ztypecolon> A' \<Longrightarrow> y \<Ztypecolon> B x \<longleftrightarrow> y \<Ztypecolon> B' x"
  shows "f \<Ztypecolon> (x : A) \<Rightarrow> B x \<longleftrightarrow> f \<Ztypecolon> (x : A') \<Rightarrow> B' x"
  by (urule dep_mono_wrt_pred_cong[THEN fun_cong]) (use assms in auto)

lemma Dep_fun_contravariant_dom:
  assumes "f \<Ztypecolon> (x : A) \<Rightarrow> B x"
  and "\<And>x. x \<Ztypecolon> A' \<Longrightarrow> x \<Ztypecolon> A"
  shows "f \<Ztypecolon> (x : A') \<Rightarrow> B x"
  by (urule dep_mono_wrt_pred_if_le_left_if_dep_mono_wrt_pred) (use assms in auto)

lemma Dep_fun_covariant_codom:
  assumes "f \<Ztypecolon> (x : A) \<Rightarrow> B x"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> f x \<Ztypecolon> B x \<Longrightarrow> f x \<Ztypecolon> B' x"
  shows "f \<Ztypecolon> (x : A) \<Rightarrow> B' x"
  by (urule dep_mono_wrt_pred_if_le_right_if_dep_mono_wrt_pred) (use assms in auto)

lemma Fun_eq_Dep_fun: "(A \<Rightarrow> B) = Dep_fun A (\<lambda>_. B)"
  by (urule refl)

lemma Fun_eq_Dep_fun_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A \<Rightarrow> B \<equiv> Dep_fun A' B'"
  by (rule eq_reflection) (use assms in simp)

lemma Fun_iff_Dep_fun: "(f \<Ztypecolon> A \<Rightarrow> B) \<longleftrightarrow> f \<Ztypecolon> (_ : A) \<Rightarrow> B"
  by simp

lemma FunI [type_intro]:
  assumes "\<And>x. x \<Ztypecolon> A \<Longrightarrow> f x \<Ztypecolon> B"
  shows "f \<Ztypecolon> A \<Rightarrow> B"
  using assms by (urule Dep_funI)

lemma FunE:
  assumes "f \<Ztypecolon> A \<Rightarrow> B"
  obtains "\<And>x. x \<Ztypecolon> A \<Longrightarrow> f x \<Ztypecolon> B"
  using assms by (urule (e) Dep_funE)

lemma FunD:
  assumes "f \<Ztypecolon> A \<Rightarrow> B"
  and "x \<Ztypecolon> A"
  shows "f x \<Ztypecolon> B"
  using assms by (urule Dep_funD)

lemma Fun_contravariant_dom:
  assumes "f \<Ztypecolon> A \<Rightarrow> B"
  and "\<And>x. x \<Ztypecolon> A' \<Longrightarrow> x \<Ztypecolon> A"
  shows "f \<Ztypecolon> A' \<Rightarrow> B"
  using assms by (urule Dep_fun_contravariant_dom)

lemma Fun_covariant_codom:
  assumes "f \<Ztypecolon> (x : A) \<Rightarrow> B x"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> f x \<Ztypecolon> B x \<Longrightarrow> f x \<Ztypecolon> B' x"
  shows "f \<Ztypecolon> (x : A) \<Rightarrow> B' x"
  using assms by (urule Dep_fun_covariant_codom)

end


subsection \<open>Intersection and Union Types\<close>

definition [typedef]: "Inter A B \<equiv> type (of_type A \<sqinter> of_type B)"

bundle soft_type_Inter_syntax
begin notation Inter (infixl "&" 55) end
bundle no_soft_type_Inter_syntax
begin no_notation Inter (infixl "&" 55) end

unbundle soft_type_Inter_syntax

lemma of_type_Inter_eq_of_type_inf_of_type [type_to_HOL_simp]:
  "of_type (A & B) = of_type A \<sqinter> of_type B"
  unfolding Inter_def type_to_HOL_simp by simp

lemma
  InterI [type_intro]: "x \<Ztypecolon> A \<Longrightarrow> x \<Ztypecolon> B \<Longrightarrow> x \<Ztypecolon> A & B" and
  InterD1: "x \<Ztypecolon> A & B \<Longrightarrow> x \<Ztypecolon> A" and
  InterD2: "x \<Ztypecolon> A & B \<Longrightarrow> x \<Ztypecolon> B" and
  Inter_covariant_left: "x \<Ztypecolon> A & B \<Longrightarrow> (x \<Ztypecolon> A \<Longrightarrow> x \<Ztypecolon> A') \<Longrightarrow> x \<Ztypecolon> A' & B" and
  Inter_covariant_right: "x \<Ztypecolon> A & B \<Longrightarrow> (x \<Ztypecolon> B \<Longrightarrow> x \<Ztypecolon> B') \<Longrightarrow> x \<Ztypecolon> A & B'"
  by unfold_types auto

lemma InterE:
  assumes "x \<Ztypecolon> A & B"
  obtains "x \<Ztypecolon> A" "x \<Ztypecolon> B"
  using assms unfolding Inter_def meaning_of_type by simp

definition [typedef]: "Union A B \<equiv> type (of_type A \<squnion> of_type B)"

bundle soft_type_Union_syntax
begin notation Union (infixl "\<bar>" 55) end
bundle no_soft_type_Union_syntax
begin no_notation Union (infixl "\<bar>" 55) end

unbundle soft_type_Union_syntax

lemma of_type_Union_eq_of_type_sup_of_type [type_to_HOL_simp]:
  "of_type (A \<bar> B) = of_type A \<squnion> of_type B"
  unfolding Union_def type_to_HOL_simp by simp

lemma
  Union_leftI: "x \<Ztypecolon> A \<Longrightarrow> x \<Ztypecolon> A \<bar> B" and
  Union_rightI: "x \<Ztypecolon> B \<Longrightarrow> x \<Ztypecolon> A \<bar> B" and
  UnionD: "x \<Ztypecolon> A \<bar> B \<Longrightarrow> x \<Ztypecolon> A \<or> x \<Ztypecolon> B" and
  Union_covariant_left: "x \<Ztypecolon> A \<bar> B \<Longrightarrow> (x \<Ztypecolon> A \<Longrightarrow> x \<Ztypecolon> A') \<Longrightarrow> x \<Ztypecolon> A' \<bar> B" and
  Union_covariant_right: "x \<Ztypecolon> A \<bar> B \<Longrightarrow> (x \<Ztypecolon> B \<Longrightarrow> x \<Ztypecolon> B') \<Longrightarrow> x \<Ztypecolon> A \<bar> B'"
  by unfold_types auto

lemma UnionE:
  assumes "x \<Ztypecolon> A \<bar> B"
  obtains (left) "x \<Ztypecolon> A" | (right) "x \<Ztypecolon> B"
  using assms by (auto dest: UnionD)

subsection \<open>The Any type\<close>

text \<open>Used, for example, to reflect rigid types back into the soft type system.\<close>

definition Any :: "'a type" ("Any")
  where [typedef]: "Any \<equiv> type \<top>"

lemma of_type_Any_eq_top [simp, type_to_HOL_simp]: "of_type Any = \<top>"
  unfolding Any_def type_to_HOL_simp by simp

lemma AnyI [type_intro]: "x \<Ztypecolon> Any"
  by unfold_types auto

lemma ball_Any_eq_all [simp]: "\<forall>\<^bsub>Any\<^esub> = All"
  by simp

lemma ball_Any_eq_all_uhint [uhint]:
  assumes "T \<equiv> Any"
  shows "\<forall>\<^bsub>T\<^esub> \<equiv> All"
  using assms by simp

lemma bex_Any_eq_ex [simp]: "\<exists>\<^bsub>Any\<^esub> = Ex"
  by simp

lemma bex_Any_eq_ex_uhint [uhint]:
  assumes "T \<equiv> Any"
  shows "\<exists>\<^bsub>T\<^esub> \<equiv> Ex"
  using assms by simp

abbreviation Bool_type :: "bool type" ("Bool")
  where "Bool \<equiv> Any"

subsection \<open>Type annotations\<close>

definition with_type :: "'a \<Rightarrow> 'a type \<Rightarrow> 'a"
  where "with_type x T \<equiv> x"

bundle soft_type_with_type_syntax
begin notation with_type (infixl ":>" 50) end
bundle no_soft_type_with_type_syntax
begin no_notation with_type (infixl ":>" 50) end

unbundle soft_type_with_type_syntax

text \<open>
\<^term>\<open>x :> T\<close> annotates \<^term>\<open>x\<close> with type \<^term>\<open>T\<close>, and is used by automated
tools to represent additional typing information in a term.
\<close>


subsection \<open>Tooling and automation\<close>

declare atomize_conjL [symmetric, rulify]
  \<comment>\<open>Used in normalization of type judgments.\<close>

named_theorems type_simp \<comment>\<open>For type elaboration\<close>
named_theorems type_instance \<comment>\<open>For type class reasoning\<close>

named_theorems derivation_rules
named_theorems backderivation_rules
(* named_theorems subtype_rules *) \<comment>\<open>Unused, for now\<close>

text \<open>
@{thm derivation_rules}, @{thm backderivation_rules} \<open>(*and @{thm subtype_rules}*)\<close>
should only be inspected and not assigned to directly; use the \<open>derive\<close>,
\<open>backward_derive\<close> \<open>(*and \<open>subtype\<close>*)\<close> attributes instead.
\<close>

(* Enable this when debugging exceptions:
declare [[ML_debugger, ML_exception_debugger]]
*)

ML_file \<open>soft_type.ML\<close>
ML_file \<open>soft_type_context.ML\<close>
ML_file \<open>derivation.ML\<close>

soft_type_translation
  "((x : (A :: 'a type)) \<Rightarrow> (B x :: 'b type)) f" \<rightleftharpoons> "f \<Ztypecolon> (x : A) \<Rightarrow> B x"
  unfolding of_type_Dep_fun_eq_dep_mono_wrt_type[symmetric] by auto

subsubsection \<open>Type derivation\<close>

method_setup raw_discharge_type =
  \<open>Scan.optional (Scan.lift (Args.add -- Args.colon) |-- Scan.repeat Args.term) []
    >> (fn add_tms => fn ctxt => SIMPLE_METHOD (
      HEADGOAL (Derivation.raw_discharge_type_tac [] add_tms ctxt)))\<close>

method_setup discharge_types =
  \<open>Scan.optional (Scan.lift (Args.add -- Args.colon) |-- Scan.repeat Args.term) []
    >> (fn add_tms => fn ctxt => SIMPLE_METHOD (
      REPEAT1 (CHANGED (ALLGOALS (TRY o (
        Derivation.full_discharge_types_tac [] add_tms ctxt))))))\<close>

ML \<open>
val soft_type_simp_solver =
  let
    fun solver ctxt i =
      (if Config.get ctxt Derivation.debug
      then print_tac ctxt ("type derivation called on subgoal " ^ string_of_int i)
      else all_tac)
      THEN
      (SUBGOAL (fn (_, j) =>
        Derivation.full_discharge_types_tac (Simplifier.prems_of ctxt) [] ctxt j)) i
  in
    map_theory_simpset (fn ctxt => ctxt
      addSolver (mk_solver "discharge_types" solver))
  end
\<close>

setup \<open>soft_type_simp_solver\<close>

ML_file \<open>unification.ML\<close>
ML_file \<open>type_classes.ML\<close>
ML_file \<open>elaboration.ML\<close>
ML_file \<open>isar_integration.ML\<close>

setup \<open>Isar_Integration.setup\<close>

declare with_type_def[type_simp]


subsection \<open>Basic declarations\<close>

declare AnyI[type]
declare Dep_funI[backward_derive]
declare FunI[backward_derive]
declare Dep_funD[derive]
declare FunD[derive]

lemma eq_type [type]: "(=) \<Ztypecolon> A \<Rightarrow> A \<Rightarrow> Bool"
  by discharge_types

lemma imp_type [type]: "(\<longrightarrow>) \<Ztypecolon> Bool \<Rightarrow> Bool \<Rightarrow> Bool"
  by discharge_types

lemma const_fun [derive]: "c \<Ztypecolon> C \<Longrightarrow> (\<lambda>a. c) \<Ztypecolon> A \<Rightarrow> C"
  by discharge_types

lemma lambda_self_type [type]: "(\<lambda>x. x) \<Ztypecolon> A \<Rightarrow> A"
  by discharge_types

lemma if_type [type]: "If \<Ztypecolon> Bool \<Rightarrow> A \<Rightarrow> A \<Rightarrow> A"
  by unfold_types auto


end
