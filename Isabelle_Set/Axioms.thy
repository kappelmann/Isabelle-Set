section \<open>Axioms of HOTG\<close>

theory Axioms
imports Setup

begin

text \<open>Axiomatic basis of higher-order Tarski-Grothendieck set theory embedded in HOL.\<close>

typedecl set

axiomatization
  mem      :: \<open>set \<Rightarrow> set \<Rightarrow> bool\<close> (infixl "\<in>" 50) and
  emptyset :: \<open>set\<close> ("{}") and
  Pow      :: \<open>set \<Rightarrow> set\<close> and
  Un       :: \<open>set \<Rightarrow> set\<close> ("\<Union>_" [90] 90) and
  Repl     :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set\<close>
where
  mem_induction: "(\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> P x) \<longrightarrow> P X) \<longrightarrow> (\<forall>X. P X)"
and
  emptyset: "\<not>(\<exists>x. x \<in> {})"
and
  union: "\<forall>X x. x \<in> \<Union>X \<longleftrightarrow> (\<exists>Y. Y \<in> X \<and> x \<in> Y)"
and
  replacement: "\<forall>X y. y \<in> Repl X F \<longleftrightarrow> (\<exists>x. x \<in> X \<and> y = F x)"

text \<open>
  Axioms @{thm mem_induction} and @{thm replacement} are axiom schemas in first-order
  logic.
\<close>


definition subset :: \<open>set \<Rightarrow> set \<Rightarrow> bool\<close> (infixl "\<subseteq>" 50)
  where "A \<subseteq> B \<equiv> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B)"

hide_const (open) subset (* Will usually be referred to via infix *)

axiomatization where
  extensionality: "\<forall>X Y. X \<subseteq> Y \<longrightarrow> Y \<subseteq> X \<longrightarrow> X = Y"
and
  powerset: "\<forall>A x. x \<in> Pow A \<longleftrightarrow> x \<subseteq> A"


text \<open>\<open>Univ X\<close> is the smallest Grothendieck universe containing X.\<close>

definition mem_transitive :: \<open>set \<Rightarrow> bool\<close>
  where "mem_transitive X \<equiv> (\<forall>x. x \<in> X \<longrightarrow> x \<subseteq> X)"

definition ZF_closed :: \<open>set \<Rightarrow> bool\<close>
  where "ZF_closed U \<equiv> (
      (\<forall>X. X \<in> U \<longrightarrow> \<Union>X \<in> U) \<and>
      (\<forall>X. X \<in> U \<longrightarrow> Pow X \<in> U) \<and>
      (\<forall>X F. X \<in> U \<longrightarrow> (\<forall>x. x \<in> X \<longrightarrow> F x \<in> U) \<longrightarrow> Repl X F \<in> U))"

text \<open>Remark: @{const ZF_closed} is a second-order statement.\<close>


axiomatization
  Univ :: \<open>set \<Rightarrow> set\<close>
where
  Univ_base: "X \<in> Univ X"
and
  Univ_transitive: "mem_transitive (Univ X)"
and
  Univ_ZF_closed: "ZF_closed (Univ X)"
and
  Univ_min: "\<lbrakk>X \<in> U; mem_transitive U; ZF_closed U\<rbrakk> \<Longrightarrow> Univ X \<subseteq> U"


end
