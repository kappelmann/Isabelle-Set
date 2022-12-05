\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Basic Lemmas\<close>
theory Basic
  imports Axioms
begin
paragraph \<open>Summary\<close>
text \<open>Here we derive a few preliminary lemmas following from the axioms that are
needed to formalise more complicated concepts.\<close>

text \<open>The following are easier to work with variants of the axioms.\<close>

lemma not_mem_emptyset [iff]: "x \<notin> {}" using emptyset by blast

lemma eq_if_subset_if_subset [intro]: "\<lbrakk>X \<subseteq> Y; Y \<subseteq> X\<rbrakk> \<Longrightarrow> X = Y"
  by (fact Axioms.extensionality[rule_format])

lemma mem_induction: "(\<And>X. (\<And>x. x \<in> X \<Longrightarrow> P x) \<Longrightarrow> P X) \<Longrightarrow> P X"
  by (fact Axioms.mem_induction[rule_format])

lemma mem_union_iff_mem_mem [iff]: "(x \<in> \<Union>X) \<longleftrightarrow> (\<exists>Y. Y \<in> X \<and> x \<in> Y)"
  by (fact Axioms.union[rule_format])

lemma mem_powerset_iff_subset [iff]: "(x \<in> powerset A) \<longleftrightarrow> (x \<subseteq> A)"
  by (fact Axioms.powerset[rule_format])

lemma mem_repl_iff_mem_eq [iff]: "(y \<in> repl X F) \<longleftrightarrow> (\<exists>x. x \<in> X \<and> y = F x)"
  by (fact Axioms.replacement[rule_format])


end
