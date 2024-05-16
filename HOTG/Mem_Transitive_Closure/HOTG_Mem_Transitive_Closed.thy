\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOTG_Mem_Transitive_Closed
  imports
    HOTG_Mem_Transitive_Closed_Base
    HOTG_Union_Intersection
begin

lemma mem_trans_closed_unionI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> mem_trans_closed x"
  shows "mem_trans_closed (\<Union>X)"
  using assms by (intro mem_trans_closedI) fast

lemma mem_trans_closed_interI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> mem_trans_closed x"
  shows "mem_trans_closed (\<Inter>X)"
  using assms by (intro mem_trans_closedI) fast

lemma mem_trans_closed_bin_unionI:
  assumes "mem_trans_closed X"
  and "mem_trans_closed Y"
  shows "mem_trans_closed (X \<union> Y)"
  using assms by blast

lemma mem_trans_closed_bin_interI:
  assumes "mem_trans_closed X"
  and "mem_trans_closed Y"
  shows "mem_trans_closed (X \<inter> Y)"
  using assms by blast

lemma mem_trans_closed_powersetI: "mem_trans_closed X \<Longrightarrow> mem_trans_closed (powerset X)"
  by fast


end
