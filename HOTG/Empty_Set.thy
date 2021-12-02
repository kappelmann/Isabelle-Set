section \<open>Empty Set\<close>

theory Empty_Set
imports Subset
begin

lemma emptyE [elim]: "x \<in> {} \<Longrightarrow> P" by auto

lemma empty_subset [simp, intro!]: "{} \<subseteq> A" by auto

lemma eq_emptyI [intro]: "\<lbrakk>\<And>y. y \<in> A \<Longrightarrow> False\<rbrakk> \<Longrightarrow> A = {}"
  by auto

lemma not_mem_if_empty [dest]: "A = {} \<Longrightarrow> a \<notin> A"
  by auto

lemma not_empty_if_mem: "a \<in> A \<Longrightarrow> A \<noteq> {}"
  by auto

lemma ex_mem_if_not_empty: "A \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A"
  by auto

lemma mem_if_not_emptyE:
  assumes "A \<noteq> {}"
  obtains x where "x \<in> A"
  using ex_mem_if_not_empty[OF assms]
  by blast

lemma subset_empty_iff_eq_empty [iff]: "A \<subseteq> {} \<longleftrightarrow> A = {}"
  by blast

lemma mem_trans_empty [simp, intro!]: "mem_trans {}"
  unfolding mem_trans_def by blast


end
