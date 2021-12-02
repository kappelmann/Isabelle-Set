section \<open>Subset\<close>

theory Subset
imports Basic
begin

lemma subsetI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  unfolding subset_def by simp

lemma subset_refl [simp, intro!]: "A \<subseteq> A" by blast

lemma mem_if_mem_if_subset [elim, trans]: "\<lbrakk>A \<subseteq> B; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> B"
  unfolding subset_def by blast

lemma not_mem_if_not_mem_subset [trans]: "\<lbrakk>a \<notin> B; A \<subseteq> B\<rbrakk> \<Longrightarrow> a \<notin> A"
  unfolding subset_def by blast

lemma subset_trans [trans]: "\<lbrakk>A \<subseteq> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> A \<subseteq> C"
  unfolding subset_def by blast

lemma subsetCE [elim]:
  assumes "A \<subseteq> B"
  obtains "a \<notin> A" | "a \<in> B"
  using assms unfolding subset_def by auto


end
