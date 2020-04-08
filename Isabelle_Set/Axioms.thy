section \<open>Axioms of HOTG\<close>

theory Axioms
imports Setup

begin

text \<open>
Axiomatic basis of higher-order Tarski-Grothendieck set theory embedded in HOL.
\<close>

typedecl set

axiomatization
  mem      :: \<open>set \<Rightarrow> set \<Rightarrow> bool\<close> (infixl "\<in>" 50) and
  emptyset :: \<open>set\<close> ("{}") and
  powerset :: \<open>set \<Rightarrow> set\<close> and
  union       :: \<open>set \<Rightarrow> set\<close> ("\<Union>_" [90] 90) and
  repl     :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set\<close>
where
  mem_induction: "(\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> P x) \<longrightarrow> P X) \<longrightarrow> (\<forall>X. P X)" and
  emptyset: "\<not>(\<exists>x. x \<in> {})" and
  union: "\<forall>X x. x \<in> \<Union>X \<longleftrightarrow> (\<exists>Y. Y \<in> X \<and> x \<in> Y)" and
  replacement: "\<forall>X y. y \<in> repl X F \<longleftrightarrow> (\<exists>x. x \<in> X \<and> y = F x)"

text \<open>
Axioms @{thm mem_induction} and @{thm replacement} are axiom schemas in first-
order logic.
\<close>

definition subset :: \<open>set \<Rightarrow> set \<Rightarrow> bool\<close> (infixl "\<subseteq>" 50)
  where "A \<subseteq> B \<equiv> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B)"

hide_const (open) subset \<comment> \<open>Will usually be referred to via infix\<close>

axiomatization where
  extensionality: "\<forall>X Y. X \<subseteq> Y \<longrightarrow> Y \<subseteq> X \<longrightarrow> X = Y" and
  powerset: "\<forall>A x. x \<in> powerset A \<longleftrightarrow> x \<subseteq> A"

definition mem_transitive :: \<open>set \<Rightarrow> bool\<close>
  where "mem_transitive X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> x \<subseteq> X)"

definition ZF_closed :: \<open>set \<Rightarrow> bool\<close>
  where "ZF_closed U \<equiv> (
      (\<forall>X. X \<in> U \<longrightarrow> \<Union>X \<in> U) \<and>
      (\<forall>X. X \<in> U \<longrightarrow> powerset X \<in> U) \<and>
      (\<forall>X F. X \<in> U \<longrightarrow> (\<forall>x. x \<in> X \<longrightarrow> F x \<in> U) \<longrightarrow> repl X F \<in> U))"

text \<open>Remark: @{const ZF_closed} is a second-order statement.\<close>

text \<open>\<open>univ X\<close> is the smallest Grothendieck universe containing X.\<close>

axiomatization
  univ :: \<open>set \<Rightarrow> set\<close>
where
  univ_elem: "X \<in> univ X" and
  univ_trans: "mem_transitive (univ X)" and
  univ_ZF_closed: "ZF_closed (univ X)" and
  univ_min: "\<lbrakk>X \<in> U; mem_transitive U; ZF_closed U\<rbrakk> \<Longrightarrow> univ X \<subseteq> U"


end
