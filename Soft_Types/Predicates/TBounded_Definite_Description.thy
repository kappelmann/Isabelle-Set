\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Type-Bounded Definite Description\<close>
theory TBounded_Definite_Description
  imports
    Soft_Types_HOL_Base
    Transport.Bounded_Definite_Description
begin

definition "bthe_type T \<equiv> bthe (of_type T)"
adhoc_overloading bthe \<rightleftharpoons> bthe_type

lemma bthe_type_eq_bthe_pred [simp]: "bthe T = bthe (of_type T)"
  unfolding bthe_type_def by simp

lemma bthe_type_eq_bthe_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "bthe T = bthe P"
  using assms by simp

lemma bthe_type_eq_iff_bthe_pred_eq [iff]: "(THE x : T. P x) = y \<longleftrightarrow> (THE x : of_type T. P x) = y"
  by simp

end