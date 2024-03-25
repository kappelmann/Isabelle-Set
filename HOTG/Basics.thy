\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Basic Lemmas\<close>
theory Basics
  imports Axioms
begin

paragraph \<open>Summary\<close>
text \<open>Here we derive a few preliminary lemmas following from the axioms that are
needed to formalise more complicated concepts.\<close>

text \<open>The following are easier to work with variants of the axioms.\<close>

lemma not_mem_emptyset [iff]: "x \<notin> {}" using emptyset by blast

lemma eq_if_subset_if_subset [intro]: "\<lbrakk>X \<subseteq> Y; Y \<subseteq> X\<rbrakk> \<Longrightarrow> X = Y"
  by (fact Axioms.extensionality[rule_format])

lemma mem_induction [case_names mem, induct type: set]:
  "(\<And>X. (\<And>x. x \<in> X \<Longrightarrow> P x) \<Longrightarrow> P X) \<Longrightarrow> P X"
  by (fact Axioms.mem_induction[rule_format])

lemma mem_union_iff_mem_mem [iff]: "(x \<in> \<Union>X) \<longleftrightarrow> (\<exists>Y. Y \<in> X \<and> x \<in> Y)"
  by (fact Axioms.union[rule_format])

corollary mem_unionI:
  assumes "Y \<in> X"
  and "x \<in> Y"
  shows "x \<in> \<Union>X"
  using assms mem_union_iff_mem_mem by auto

corollary mem_unionE:
  assumes "x \<in> \<Union>X"
  obtains Y where "Y \<in> X" "x \<in> Y"
  using assms mem_union_iff_mem_mem by auto

lemma mem_powerset_iff_subset [iff]: "(x \<in> powerset A) \<longleftrightarrow> (x \<subseteq> A)"
  by (fact Axioms.powerset[rule_format])

corollary mem_powerset_if_subset:
  assumes "x \<subseteq> A"
  shows "x \<in> powerset A"
  using assms by blast

corollary subset_if_mem_powerset:
  assumes "x \<in> powerset A"
  shows "x \<subseteq> A"
  using assms by blast

lemma mem_repl_iff_mem_eq [iff]: "(y \<in> repl X f) \<longleftrightarrow> (\<exists>x. x \<in> X \<and> y = f x)"
  by (fact Axioms.replacement[rule_format])

corollary mem_replI:
  assumes "y = f x"
  and "x \<in> X"
  shows "y \<in> repl X f"
  using assms mem_repl_iff_mem_eq by blast

corollary mem_replE:
  assumes "y \<in> repl X f"
  obtains x where "y = f x" "x \<in> X"
  using assms mem_repl_iff_mem_eq by blast


end
