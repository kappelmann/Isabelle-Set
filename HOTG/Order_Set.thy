\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Order on Sets\<close>
theory Order_Set
  imports
    Transport.Functions_Monotone
    HOL.Orderings
    Subset
begin

unbundle no_HOL_ascii_syntax

instantiation set :: order
begin

definition le_set_def: "less_eq_set \<equiv> (\<subseteq>)"
definition lt_set_def: "less_set \<equiv> (\<subset>)"

lemma le_set_eq_subset [simp]: "(\<le>) = (\<subseteq>)" unfolding le_set_def by simp
lemma lt_set_eq_ssubset [simp]: "(<) = (\<subset>)" unfolding lt_set_def by simp

instance by (standard) auto

end

lemma mono_mem_of: "mono mem_of"
  by (intro monoI) auto

lemma le_boolD': "P \<le> Q \<Longrightarrow> P \<Longrightarrow> Q" by (rule le_boolE)

lemma le_boolD'': "P \<Longrightarrow> P \<le> Q \<Longrightarrow> Q" by (rule le_boolE)


end