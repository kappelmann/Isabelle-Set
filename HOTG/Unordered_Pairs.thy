section \<open>Unordered Pairs\<close>

theory Unordered_Pairs
imports
  Replacement
  Powerset
begin

text \<open>We define an unordered pair \<open>upair\<close> using replacement. We then use it to define finite sets
in \<open>Finite_Sets\<close>.\<close>

definition upair :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "upair a b = {if i = {} then a else b | i \<in> powerset (powerset {})}"

definition cons :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "cons x A = \<Union>(upair A (upair x x))"

lemma cons_elems [iff]: "y \<in> cons x A \<longleftrightarrow> y = x \<or> y \<in> A"
  by (auto 5 0 simp: cons_def upair_def)

lemma consI1 [simp]: "a \<in> cons a A"
  by simp

lemma consI2: "a \<in> A \<Longrightarrow> a \<in> cons b A"
  by simp

lemma consE [elim!]: "\<lbrakk>a \<in> cons b A; a = b \<Longrightarrow> P; a \<in> A \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(*LP: Stronger version of the rule above*)
lemma consE':
  "\<lbrakk>a \<in> cons b A; a = b \<Longrightarrow> P; \<lbrakk>a \<in> A; a \<noteq> b\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(*LP: Classical introduction rule*)
lemma consCI [intro!]: "(a \<notin> B \<Longrightarrow> a = b) \<Longrightarrow> a \<in> cons b B"
  by auto

lemma cons_ne_empty [simp]: "cons a B \<noteq> {}"
  by auto

lemma empty_ne_cons [simp]: "{} \<noteq> cons a B"
  by (fact cons_ne_empty[symmetric])

lemma cons_eq_emptyE: assumes "cons a B = {}" shows "P"
  using assms by simp

lemma cons_commute: "cons x (cons y A) = cons y (cons x A)"
  by (rule extensionality) auto

lemma cons_repeat: "cons x (cons x A) = cons x A"
  by (rule extensionality) auto


end
