section \<open>Basic Lemmas\<close>

theory Basic
imports Axioms
begin
paragraph \<open>Summary\<close>
text \<open>Here we derive a few preliminary lemmas following from the axioms that are needed to formalise
more complicated concepts.\<close>

abbreviation "not_mem x y \<equiv> \<not> x \<in> y"

bundle hotg_not_mem_syntax begin notation not_mem (infixl "\<notin>" 50) end
bundle no_hotg_not_mem_syntax begin no_notation not_mem (infixl "\<notin>" 50) end

unbundle hotg_not_mem_syntax

text \<open>The following are easier to work with variants of the axioms.\<close>

lemma emptyset [simp]: "x \<notin> {}" using emptyset by blast

lemma extensionality: "\<lbrakk>X \<subseteq> Y; Y \<subseteq> X\<rbrakk> \<Longrightarrow> X = Y"
  by (fact Axioms.extensionality[rule_format])

lemma mem_induction: "(\<And>X. (\<And>x. x \<in> X \<Longrightarrow> P x) \<Longrightarrow> P X) \<Longrightarrow> P X"
  by (fact Axioms.mem_induction[rule_format])

lemma union [iff]: "(x \<in> \<Union>X) = (\<exists>Y. Y \<in> X \<and> x \<in> Y)"
  by (fact Axioms.union[rule_format])

lemma powerset [iff]: "(x \<in> powerset A) \<longleftrightarrow> (x \<subseteq> A)"
  by (fact Axioms.powerset[rule_format])

lemma replacement [iff]: "(y \<in> repl X F) \<longleftrightarrow> (\<exists>x. x \<in> X \<and> y = F x)"
  by (fact Axioms.replacement[rule_format])


end