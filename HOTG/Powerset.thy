\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Powerset\<close>
theory Powerset
  imports Subset
begin

lemma mem_powerset_if_subset: "A \<subseteq> B \<Longrightarrow> A \<in> powerset B"
  by auto

lemma subset_if_mem_powerset: "A \<in> powerset B  \<Longrightarrow> A \<subseteq> B"
  by auto

lemma empty_mem_powerset [iff]: "{} \<in> powerset A"
  by auto

lemma mem_powerset_self [iff]: "A \<in> powerset A"
  by auto

lemma mem_powerset_empty_iff_eq_empty [iff]: "x \<in> powerset {} \<longleftrightarrow> x = {}"
  by auto

lemma mono_subset_powerset: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>)) powerset" by auto

end
