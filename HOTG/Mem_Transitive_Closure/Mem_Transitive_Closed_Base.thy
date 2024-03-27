\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transitive Sets\<close>
theory Mem_Transitive_Closed_Base
  imports Subset
begin

lemma mem_trans_closedI [intro]: "(\<And>x. x \<in> X \<Longrightarrow> x \<subseteq> X) \<Longrightarrow> mem_trans_closed X"
  unfolding mem_trans_closed_def by auto

lemma mem_trans_closedI': "(\<And>x y. x \<in> X \<Longrightarrow> y \<in> x \<Longrightarrow> y \<in> X) \<Longrightarrow> mem_trans_closed X"
  by auto

lemma mem_trans_closedD [dest]:
  assumes "mem_trans_closed x"
  shows "\<And>y. y \<in> x \<Longrightarrow> y \<subseteq> x"
  using assms unfolding mem_trans_closed_def by auto

lemma mem_trans_closed_empty [iff]: "mem_trans_closed {}" by auto


end
