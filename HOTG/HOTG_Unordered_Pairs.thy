\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Unordered Pairs\<close>
theory HOTG_Unordered_Pairs
  imports
    HOTG_Powerset
    HOTG_Replacement
begin

text \<open>We define an unordered pair \<open>upair\<close> using replacement.
We then use it to define finite sets in @{file "HOTG_Finite_Sets.thy"}.\<close>

definition "upair a b \<equiv> {if i = {} then a else b | i \<in> powerset (powerset {})}"

lemma mem_upair_leftI [intro]: "a \<in> upair a b" unfolding upair_def by auto
lemma mem_upair_rightI [intro]: "b \<in> upair a b" unfolding upair_def by auto

lemma mem_upairE [elim!]:
  assumes "x \<in> upair a b"
  obtains "x = a" | "x = b"
  using assms unfolding upair_def by (auto split: if_splits)

lemma mem_upair_iff: "x \<in> upair a b \<longleftrightarrow> x = a \<or> x = b" by auto

definition "insert x A \<equiv> \<Union>(upair A (upair x x))"

lemma mem_insert_leftI [intro]: "x \<in> insert x A"
  unfolding insert_def by auto

lemma mem_insert_rightI [intro]: "y \<in> A \<Longrightarrow> y \<in> insert x A"
  unfolding insert_def by auto

lemma mem_insertE [elim]:
  assumes "y \<in> insert x A"
  obtains "y = x" | "y \<noteq> x" "y \<in> A"
  using assms unfolding insert_def by auto

lemma mem_of_insert_eq_eq_sup_mem_of [set_to_HOL_simp]: "mem_of (insert x A) = ((=) x \<squnion> mem_of A)"
  by (intro ext) auto

lemma mem_insert_iff: "y \<in> insert x A \<longleftrightarrow> y = x \<or> y \<in> A" by auto

lemma not_mem_insert_if_not_mem_if_ne: "\<lbrakk>x \<noteq> a; x \<notin> A\<rbrakk> \<Longrightarrow> x \<notin> insert a A" by auto

lemma insert_eq_if_mem [simp]: "a \<in> A \<Longrightarrow> insert a A = A" by auto

(*LP: Classical introduction rule*)
lemma mem_insert_if_not_mem_imp_eq [intro!]:
  "(a \<notin> B \<Longrightarrow> a = b) \<Longrightarrow> a \<in> insert b B"
  by auto

lemma insert_ne_empty [iff]: "insert a B \<noteq> {}"
  by auto

lemma insert_comm: "insert x (insert y A) = insert y (insert x A)"
  by auto

lemma insert_insert_eq_insert [simp]: "insert x (insert x A) = insert x A"
  by auto

lemma bex_insert_iff_or_bex [iff]: "(\<exists>x : insert a A. P x) \<longleftrightarrow> (P a \<or> (\<exists>x : A. P x))"
  by auto

lemma ball_insert_iff_and_ball [iff]: "(\<forall>x : insert a A. P x) \<longleftrightarrow> (P a \<and> (\<forall>x : A. P x))"
  by auto

lemma mono_subset_subset_insert: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) (insert x)"
  by auto

lemma insert_subset_iff_mem_subset [iff]: "insert x A \<subseteq> B \<longleftrightarrow> x \<in> B \<and> A \<subseteq> B"
  by blast

lemma repl_insert_eq: "{f x | x \<in> insert x A} = insert (f x) {f x | x \<in> A}"
  by auto


end

