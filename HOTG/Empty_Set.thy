section \<open>Empty Set\<close>

theory Empty_Set
imports Subset
begin

lemma emptyE [elim]: "x \<in> {} \<Longrightarrow> P"
  by auto

lemma empty_subsetI [simp]: "{} \<subseteq> A"
  by auto

lemma equals_emptyI [intro]: "\<lbrakk>\<And>y. y \<in> A \<Longrightarrow> False\<rbrakk> \<Longrightarrow> A = {}"
  by (rule extensionality) auto

lemma equals_emptyD [dest]: "A = {} \<Longrightarrow> a \<notin> A"
  by auto

lemma not_emptyI: "a \<in> A \<Longrightarrow> A \<noteq> {}"
  by auto

lemma not_empty_Ex: "A \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A"
  by auto

lemma not_emptyE:
  assumes "A \<noteq> {}"
  obtains x where "x \<in> A"
  using not_empty_Ex[OF assms]
  by auto

lemma subset_empty_iff_eq_empty [simp]: "A \<subseteq> {} \<longleftrightarrow> A = {}"
  by auto

lemma mem_transitive_empty [intro]: "mem_transitive {}"
  unfolding mem_transitive_def by auto


end
