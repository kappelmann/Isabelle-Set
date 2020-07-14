section \<open>Transitive Sets\<close>

theory Mem_Transitive
imports Subset
begin

lemma mem_transitiveI [intro]:
  "(\<And>x y. x \<in> X \<Longrightarrow> y \<in> x \<Longrightarrow> y \<in> X) \<Longrightarrow> mem_transitive X"
  unfolding mem_transitive_def by auto

lemma mem_transitiveE [elim]:
  "mem_transitive x \<Longrightarrow> y \<in> x \<Longrightarrow> y \<subseteq> x"
  unfolding mem_transitive_def by auto


end
