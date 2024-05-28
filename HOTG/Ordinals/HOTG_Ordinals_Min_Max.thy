theory HOTG_Ordinals_Min_Max
  imports HOTG_Ordinals_Base HOTG_Less_Than
begin

unbundle no_HOL_order_syntax

definition max_ordinal :: "set \<Rightarrow> set \<Rightarrow> set" where
"max_ordinal A B = (if A \<in> B then B else A)"

lemma ordinal_max_ordinal: "ordinal A \<Longrightarrow> ordinal B \<Longrightarrow> ordinal (max_ordinal A B)"
  using max_ordinal_def by auto

lemma le_max_ordinal_left: "ordinal A \<Longrightarrow> ordinal B \<Longrightarrow> A \<le> max_ordinal A B"
  using ordinal_memE max_ordinal_def le_if_lt lt_if_mem by auto

lemma max_ordinal_comm:
  assumes "ordinal A" and "ordinal B"
  shows "max_ordinal A B = max_ordinal B A" 
  by (cases rule: ordinal_memE[OF assms]) (auto simp: max_ordinal_def not_mem_if_mem)

lemma le_max_ordinal_right: "ordinal A \<Longrightarrow> ordinal B \<Longrightarrow> B \<le> max_ordinal A B"
  using le_max_ordinal_left max_ordinal_comm by force

lemma max_ordinal_lt: "A < C \<Longrightarrow> B < C \<Longrightarrow> max_ordinal A B < C"
  using max_ordinal_def by auto

end