section \<open>Unordered Pairs\<close>

theory Unordered_Pairs
imports
  Replacement
  Powerset
begin

text \<open>We define an unordered pair \<open>upair\<close> using replacement.
We then use it to define finite sets in @{file "Finite_Sets.thy"}.\<close>

definition "upair a b \<equiv> {if i = {} then a else b | i \<in> powerset (powerset {})}"

definition "insert x A \<equiv> \<Union>(upair A (upair x x))"

lemma mem_insert_iff [iff]: "y \<in> insert x A \<longleftrightarrow> y = x \<or> y \<in> A"
  unfolding insert_def upair_def by auto

lemma not_mem_insert_if_not_mem_if_ne: "\<lbrakk>x \<noteq> a; x \<notin> A\<rbrakk> \<Longrightarrow> x \<notin> insert a A" by auto

lemma mem_insert[simp, intro!]: "a \<in> insert a A" by simp

lemma mem_insert_if_mem: "a \<in> A \<Longrightarrow> a \<in> insert b A" by simp

lemma mem_insertE [elim!]:
  assumes "a \<in> insert b A"
  obtains "a = b" | "a \<in> A"
  using assms by auto

lemma mem_insertE':
  assumes "a \<in> insert b A"
  obtains "a = b" | "a \<in> A" and "a \<noteq> b"
  using assms by auto

lemma insert_eq_if_mem [simp]: "a \<in> A \<Longrightarrow> insert a A = A" by auto

(*LP: Classical introduction rule*)
lemma mem_insert_if_not_mem_imp_eq [intro!]: "(a \<notin> B \<Longrightarrow> a = b) \<Longrightarrow> a \<in> insert b B"
  by auto

lemma insert_ne_empty [simp, intro!]: "insert a B \<noteq> {}"
  by auto

lemma empty_ne_insert[simp, intro!]: "{} \<noteq> insert a B"
  by (fact insert_ne_empty[symmetric])

lemma insert_comm: "insert x (insert y A) = insert y (insert x A)"
  by (rule eqI) auto

lemma insert_insert_eq_insert[simp, intro!]: "insert x (insert x A) = insert x A"
  by (rule eqI) auto

lemma bex_insert_iff_or_bex [simp]: "(\<exists>x \<in> insert a A. P x) \<longleftrightarrow> (P a \<or> (\<exists>x \<in> A. P x))"
  by auto

lemma ball_insert_iff_and_ball [simp]:
  "(\<forall>x \<in> insert a A. P x) \<longleftrightarrow> (P a \<and> (\<forall>x \<in> A. P x))"
  by auto


subsubsection \<open>Subsets\<close>

lemma insert_subset_iff_mem_subset: "insert x A \<subseteq> B \<longleftrightarrow> x \<in> B \<and> A \<subseteq> B"
  using mem_if_mem_if_subset by blast


end
