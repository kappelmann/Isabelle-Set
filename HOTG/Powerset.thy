section \<open>Powerset\<close>

theory Powerset
imports Empty_Set
begin

lemma powersetI: "A \<subseteq> B \<Longrightarrow> A \<in> powerset B"
  by auto

lemma powersetD: "A \<in> powerset B  \<Longrightarrow> A \<subseteq> B"
  by auto

lemma empty_mem_powerset [simp, intro]: "{} \<in> powerset A"
  by auto

lemma powerset_top [simp, intro]: "A \<in> powerset A"
  by auto

lemma mem_powerset_empty_iff_eq_empty [iff]: "x \<in> powerset {} \<longleftrightarrow> x = {}"
  by auto


end
