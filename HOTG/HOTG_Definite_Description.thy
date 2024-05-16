\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Definite Descriptiosn\<close>
theory HOTG_Definite_Description
  imports
    HOTG_Basics
    Transport.Bounded_Definite_Description
begin

definition "bthe_set A \<equiv> bthe (mem_of A)"
adhoc_overloading bthe bthe_set

lemma bthe_set_eq_bthe_pred [simp]: "bthe A = bthe (mem_of A)"
  unfolding bthe_set_def by simp

lemma bthe_set_eq_bthe_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "bthe A = bthe P"
  using assms by simp

lemma bthe_set_eq_iff_bthe_pred_eq [iff]: "(THE x : A. P x) = y \<longleftrightarrow> (THE x : mem_of A. P x) = y"
  by simp

end
