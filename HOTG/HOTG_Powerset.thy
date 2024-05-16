\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Powerset\<close>
theory HOTG_Powerset
  imports HOTG_Subset
begin

lemma mem_powerset_if_subset: "A \<subseteq> B \<Longrightarrow> A \<in> powerset B"
  by auto

lemma mem_of_powerset_eq_supset [simp]: "mem_of (powerset B) = supset B"
  by (intro ext) auto

lemma subset_if_mem_powerset: "A \<in> powerset B  \<Longrightarrow> A \<subseteq> B"
  by auto

lemma empty_mem_powerset [iff]: "{} \<in> powerset A"
  by auto

lemma mem_powerset_self [iff]: "A \<in> powerset A"
  by auto

lemma mem_powerset_empty_iff_eq_empty [iff]: "x \<in> powerset {} \<longleftrightarrow> x = {}"
  by auto

lemma mono_subset_powerset: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) powerset" by fast

end

