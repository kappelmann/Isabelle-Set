\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Mem_Transitive_Closed
  imports
    Mem_Transitive_Closed_Base
    SAddition
begin

lemma mem_trans_closed_succI [intro]:
  assumes "mem_trans_closed X"
  shows "mem_trans_closed (succ X)"
  unfolding succ_def using assms
  by (auto simp flip: insert_self_eq_add_one)

lemma mem_trans_closed_unionI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> mem_trans_closed x"
  shows "mem_trans_closed (\<Union>X)"
  using assms by (intro mem_trans_closedI) auto

lemma mem_trans_closed_interI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> mem_trans_closed x"
  shows "mem_trans_closed (\<Inter>X)"
  using assms by (intro mem_trans_closedI) auto

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
  by auto

lemma union_succ_eq_self_if_mem_trans_closed [simp]: "mem_trans_closed X \<Longrightarrow> \<Union>(succ X) = X"
  by (auto simp flip: insert_self_eq_add_one simp: succ_eq_add_one)


end
