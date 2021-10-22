section \<open>Subset\<close>

theory Subset
imports Basic
begin

lemma subsetI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  by (unfold subset_def) simp

lemma subset_refl [simp, intro!]: "A \<subseteq> A" by blast

lemma mem_if_subset_if_mem [trans]: "\<lbrakk>A \<subseteq> B; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> B"
  by (unfold subset_def) blast

lemma not_mem_if_not_mem_subset [trans]: "\<lbrakk>a \<notin> B; A \<subseteq> B\<rbrakk> \<Longrightarrow> a \<notin> A"
  by (unfold subset_def) blast

lemma subset_trans [trans]: "\<lbrakk>A \<subseteq> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> A \<subseteq> C"
  by (unfold subset_def) blast

end
