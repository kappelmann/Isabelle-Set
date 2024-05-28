\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Monotonicity\<close>
theory TFunctions_Monotone
  imports
    Soft_Types_HOL_Base
    Transport.Functions_Monotone
begin

definition "dep_mono_wrt_type A B \<equiv> (x : of_type A) \<Rightarrow> of_type (B x)"
adhoc_overloading dep_mono_wrt dep_mono_wrt_type
definition "mono_wrt_type A B \<equiv> of_type A \<Rightarrow> of_type B"
adhoc_overloading mono_wrt mono_wrt_type

lemma dep_mono_wrt_type_eq_dep_mono_wrt_pred [simp]:
  "((x : A) \<Rightarrow> B x) = ((x : of_type A) \<Rightarrow> of_type (B x))"
  unfolding dep_mono_wrt_type_def by simp

lemma dep_mono_wrt_type_eq_dep_mono_wrt_pred_uhint [uhint]:
  assumes "A' \<equiv> of_type A"
  and "\<And>x. B' x \<equiv> of_type (B x)"
  shows "(x : A) \<Rightarrow> B x \<equiv> (x : A') \<Rightarrow> B' x"
  using assms by simp

lemma dep_mono_wrt_type_iff_dep_mono_wrt_pred [iff]:
  "((x : A) \<Rightarrow> B x) f \<longleftrightarrow> ((x : of_type A) \<Rightarrow> of_type (B x)) f"
  by simp

(*TODO: abstract and then also use for set monotonicity theorems*)
lemma dep_mono_wrt_type_eq_pred_map_dep_mono_wrt_pred_comp_type_if_iff:
  assumes "\<And>(T :: 'a type). A T \<longleftrightarrow> A' (of_type T)"
  shows "((T : A) \<Rightarrow> B T) = pred_map (\<lambda>f. f \<circ> type) ((P : A') \<Rightarrow> B (type P))"
  (is "?lhs = ?rhs")
proof (urule (rr) ext iffI dep_mono_wrt_predI)
  fix f T assume "?rhs f" "A T"
  with assms have "B (type (of_type T)) (f (type (of_type T)))" by auto
  moreover have "type (of_type T) = T" by (intro type_ext) (simp add: of_type_type_eq_self)
  ultimately show "B T (f T)" by simp
next
  fix f P presume "?lhs f" "A' P"
  with assms show "B (type P) ((f \<circ> type) P)" by (fastforce simp add: of_type_type_eq_self)
qed simp_all

declare dep_mono_comp_iff_dep_mono_if_all_app_eq[where ?m=type, type_to_HOL_simp]
declare dep_mono_pred_map_comp_iff_dep_mono_if_all_app_eq[where ?m=type, type_to_HOL_simp]

lemma mono_wrt_type_eq_mono_wrt_pred [simp]:
  "(A \<Rightarrow> B) = (of_type A \<Rightarrow> of_type B)"
  unfolding mono_wrt_type_def by simp

lemma mono_wrt_type_eq_mono_wrt_pred_uhint [uhint]:
  assumes "A' \<equiv> of_type A"
  and "B' \<equiv> of_type B"
  shows "(A \<Rightarrow> B) \<equiv> (A' \<Rightarrow> B')"
  using assms by simp

lemma mono_wrt_type_iff_mono_wrt_pred [iff]: "(A \<Rightarrow> B) f \<longleftrightarrow> (of_type A \<Rightarrow> of_type B) f"
  by simp

lemma mono_wrt_type_eq_pred_map_mono_wrt_pred_comp_type_if_iff:
  assumes "\<And>(T :: 'a type). A T \<longleftrightarrow> A' (of_type T)"
  shows "(A \<Rightarrow> B) = pred_map (\<lambda>f. f \<circ> type) (A' \<Rightarrow> B)"
  using assms by (urule dep_mono_wrt_type_eq_pred_map_dep_mono_wrt_pred_comp_type_if_iff)

end