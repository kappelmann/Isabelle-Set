section \<open>Transitive Sets\<close>
theory Mem_Trans
  imports Subset
begin

lemma mem_transI [intro]: "(\<And>x. x \<in> X \<Longrightarrow> x \<subseteq> X) \<Longrightarrow> mem_trans X"
  unfolding mem_trans_def by auto

lemma mem_transI': "(\<And>x y. x \<in> X \<Longrightarrow> y \<in> x \<Longrightarrow> y \<in> X) \<Longrightarrow> mem_trans X"
  by auto

lemma mem_transE [elim]:
  "mem_trans x \<Longrightarrow> y \<in> x \<Longrightarrow> y \<subseteq> x"
  unfolding mem_trans_def by auto


end
