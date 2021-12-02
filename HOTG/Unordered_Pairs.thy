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

lemma not_mem_cons_if_not_mem_if_ne: "\<lbrakk>x \<noteq> a; x \<notin> A\<rbrakk> \<Longrightarrow> x \<notin> cons a A" by auto

lemma mem_cons [simp, intro!]: "a \<in> cons a A" by simp

lemma mem_cons_if_mem: "a \<in> A \<Longrightarrow> a \<in> cons b A" by simp

lemma mem_consE [elim!]:
  assumes "a \<in> cons b A"
  obtains "a = b" | "a \<in> A"
  using assms by auto

lemma mem_consE':
  assumes "a \<in> cons b A"
  obtains "a = b" | "a \<in> A" and "a \<noteq> b"
  using assms by auto

(*LP: Classical introduction rule*)
lemma mem_cons_if_not_mem_imp_eq [intro!]: "(a \<notin> B \<Longrightarrow> a = b) \<Longrightarrow> a \<in> cons b B"
  by auto

lemma cons_ne_empty [simp, intro!]: "cons a B \<noteq> {}"
  by auto

lemma empty_ne_cons [simp, intro!]: "{} \<noteq> cons a B"
  by (fact cons_ne_empty[symmetric])

lemma cons_comm: "cons x (cons y A) = cons y (cons x A)"
  by (rule eqI) auto

lemma cons_cons_eq_cons [simp, intro!]: "cons x (cons x A) = cons x A"
  by (rule eqI) auto

lemma bex_cons_iff_or_bex [simp]: "(\<exists>x \<in> cons a A. P x) \<longleftrightarrow> (P a \<or> (\<exists>x \<in> A. P x))"
  by auto

lemma ball_cons_iff_and_ball [simp]:
  "(\<forall>x \<in> cons a A. P x) \<longleftrightarrow> (P a \<and> (\<forall>x \<in> A. P x))"
  by auto

subsubsection \<open>Subsets\<close>

lemma cons_subset_iff_mem_subset: "cons x A \<subseteq> B \<longleftrightarrow> x \<in> B \<and> A \<subseteq> B"
  using mem_if_mem_if_subset by blast

end
