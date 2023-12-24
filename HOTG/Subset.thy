\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Subset\<close>
theory Subset
  imports Basic
begin

lemma subsetI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  unfolding subset_def by simp

lemma subsetD [dest]: "\<lbrakk>A \<subseteq> B; a \<in> A\<rbrakk> \<Longrightarrow> a \<in> B"
  unfolding subset_def by blast

lemma mem_if_subset_if_mem [trans]: "\<lbrakk>a \<in> A; A \<subseteq> B\<rbrakk> \<Longrightarrow> a \<in> B" by blast

lemma subset_self [iff]: "A \<subseteq> A" by blast

lemma empty_subset [iff]: "{} \<subseteq> A" by blast

lemma subset_empty_iff [iff]: "A \<subseteq> {} \<longleftrightarrow> A = {}" by blast

lemma not_mem_if_subset_if_not_mem [trans]: "\<lbrakk>a \<notin> B; A \<subseteq> B\<rbrakk> \<Longrightarrow> a \<notin> A"
  by blast

lemma subset_if_subset_if_subset [trans]: "\<lbrakk>A \<subseteq> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> A \<subseteq> C"
  by blast

lemma subsetCE [elim]:
  assumes "A \<subseteq> B"
  obtains "a \<notin> A" | "a \<in> B"
  using assms by auto

subsection \<open>Strict Subsets\<close>

definition "ssubset A B \<equiv> A \<subseteq> B \<and> A \<noteq> B"

bundle hotg_ssubset_syntax begin notation ssubset (infixl "\<subset>" 50) end
bundle no_hotg_xsubset_syntax begin no_notation ssubset (infixl "\<subset>" 50) end
unbundle hotg_ssubset_syntax

lemma ssubsetI [intro]:
  assumes "A \<subseteq> B"
  and "A \<noteq> B"
  shows "A \<subset> B"
  unfolding ssubset_def using assms by blast

lemma ssubsetE [elim]:
  assumes "A \<subset> B"
  obtains "A \<subseteq> B" "A \<noteq> B"
  using assms unfolding ssubset_def by blast



end
