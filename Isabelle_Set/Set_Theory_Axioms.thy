theory Set_Theory_Axioms
  imports Notation_Cleanup
begin

subsection \<open> Axiomatic basis of set theory embedded in HOL. \<close>


text \<open> 
  We axiomatize a type \<open>set\<close>, with the standard set-theoretic operations and axioms.
\<close>

typedecl set 

axiomatization
  member :: "set \<Rightarrow> set \<Rightarrow> bool" (infixl "\<in>" 50) and
  empty_set :: set ("{}") and
  Pow :: "set \<Rightarrow> set" and
  Union :: "set \<Rightarrow> set" ("\<Union>_" [90] 90) and
  Repl :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
where
  elem_induct_axiom: "(\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> P x) \<longrightarrow> P X) \<longrightarrow> P A"
  and not_mem_empty[simp]: "\<not> x \<in> {}"
  and Union_axiom[iff]: "x \<in> \<Union>X \<longleftrightarrow> (\<exists>Y. Y \<in> X \<and> x \<in> Y)"
  and Replacement_axiom[iff]: "y \<in> Repl X F \<longleftrightarrow> (\<exists>x. x \<in> X \<and> y = F x)"

text \<open> The following axioms need a definition first: \<close>

definition subset :: "set \<Rightarrow> set \<Rightarrow> bool"  (infixl "\<subseteq>" 50)  \<comment> \<open>subset relation\<close>
  where subset_def: "A \<subseteq> B \<equiv> (\<forall>x. x \<in> A \<longrightarrow> x \<in> B)"

axiomatization
  where extensionality: "X \<subseteq> Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> X = Y"
  and Pow_iff: "x \<in> Pow A \<longleftrightarrow> x \<subseteq> A"

text \<open> Finally, we axiomatize the constant \<open>Univ\<close>, which, given a set,
  returns a Grothendieck universe containing the set.

  This is the Tarski axiom.
\<close>

definition transitive :: "set \<Rightarrow> bool"
  where "transitive U \<equiv> (\<forall>x. x \<in> U \<longrightarrow> x \<subseteq> U)"

definition ZF_closed :: "set \<Rightarrow> bool"
  where "ZF_closed U \<equiv> (
      (\<forall>X. X \<in> U \<longrightarrow> \<Union>X \<in> U) \<and>
      (\<forall>X. X \<in> U \<longrightarrow> Pow X \<in> U) \<and>
      (\<forall>X F. X \<in> U \<longrightarrow> (\<forall>x. x \<in> X \<longrightarrow> F x \<in> U) \<longrightarrow> Repl X F \<in> U)
    )"

axiomatization
  Univ :: "set \<Rightarrow> set"
  where Univ_member: "N \<in> Univ N"
  and Univ_transtive: "transitive (Univ N)"
  and Univ_ZF_closed: "ZF_closed (Univ N)"


end
