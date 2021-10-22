section \<open>Unordered Pairs\<close>

theory Unordered_Pairs
imports
  Replacement
  Powerset
begin

text \<open>We define an unordered pair \<open>upair\<close> using replacement.
We then use it to define finite sets in @{file "Finite_Sets.thy"}.\<close>

definition "upair a b \<equiv> {if i = {} then a else b | i \<in> powerset (powerset {})}"

definition "cons x A \<equiv> \<Union>(upair A (upair x x))"

lemma mem_cons_iff [iff]: "y \<in> cons x A \<longleftrightarrow> y = x \<or> y \<in> A"
  unfolding cons_def upair_def by auto

lemma mem_cons [simp, intro!]: "a \<in> cons a A" by simp

lemma mem_cons_if_mem: "a \<in> A \<Longrightarrow> a \<in> cons b A" by simp

lemma mem_consE [elim!]: "\<lbrakk>a \<in> cons b A; a = b \<Longrightarrow> P; a \<in> A \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by auto

(*LP: Stronger version of the rule above*)
lemma mem_consE': "\<lbrakk>a \<in> cons b A; a = b \<Longrightarrow> P; \<lbrakk>a \<in> A; a \<noteq> b\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(*LP: Classical introduction rule*)
lemma mem_cons_if_not_mem_imp_eq [intro!]: "(a \<notin> B \<Longrightarrow> a = b) \<Longrightarrow> a \<in> cons b B"
  by auto

lemma cons_ne_empty [simp, intro!]: "cons a B \<noteq> {}"
  by auto

lemma empty_ne_cons [simp, intro!]: "{} \<noteq> cons a B"
  by (fact cons_ne_empty[symmetric])

lemma cons_eq_emptyE: assumes "cons a B = {}" shows "P"
  using assms by simp

lemma cons_commute: "cons x (cons y A) = cons y (cons x A)"
  by (rule eqI) auto

lemma cons_cons_eq_cons [simp]: "cons x (cons x A) = cons x A"
  by (rule eqI) auto

subsubsection \<open>Subsets\<close>

lemma cons_subset_iff_mem_subset: "cons x A \<subseteq> B \<longleftrightarrow> x \<in> B \<and> A \<subseteq> B"
  using mem_if_subset_if_mem by blast

end
