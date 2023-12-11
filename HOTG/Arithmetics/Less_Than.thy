theory Less_Than
  imports
    Transport.HOL_Syntax_Bundles_Orders
    Foundation
    Mem_Transitive_Closure
begin

unbundle no_HOL_ascii_syntax

paragraph \<open>Less-Than Order\<close>

definition "lt X Y \<equiv> X \<in> mem_trans_closure Y"

bundle hotg_lt_syntax begin notation lt (infix "<" 50) end
bundle no_hotg_lt_syntax begin no_notation lt (infix "<" 50) end
unbundle hotg_lt_syntax
unbundle no_HOL_order_syntax

lemma lt_iff_mem_trans_closure: "X < Y \<longleftrightarrow> X \<in> mem_trans_closure Y"
  unfolding lt_def by simp

lemma lt_if_lt_if_mem [trans]:
  assumes "y \<in> Y"
  and "Y < X"
  shows "y < X"
  using assms mem_trans_closed_mem_trans_closure unfolding lt_iff_mem_trans_closure by auto

lemma lt_trans [trans]:
  assumes "X < Y"
  and "Y < Z"
  shows "X < Y"
  using assms mem_mem_trans_closure_trans by auto

lemma not_lt_self [iff]: "\<not>(X < X)"
  using lt_iff_mem_trans_closure by auto


paragraph \<open>Less-Than or Equal Order\<close>

definition "le X Y \<equiv> X < Y \<or> X = Y"

bundle hotg_le_syntax begin notation le (infix "\<le>" 60) end
bundle no_hotg_le_syntax begin no_notation le (infix "\<le>" 60) end
unbundle hotg_le_syntax

lemma le_iff_mem_trans_closure_or_eq: "X \<le> Y \<longleftrightarrow> X \<in> mem_trans_closure Y \<or> X = Y"
  by (simp add: le_def lt_iff_mem_trans_closure)

lemma le_trans [trans]:
  assumes "X \<le> Y"
  and "Y \<le> Z"
  shows "X \<le> Z"
  using assms mem_mem_trans_closure_trans unfolding le_iff_mem_trans_closure_or_eq by auto


end
