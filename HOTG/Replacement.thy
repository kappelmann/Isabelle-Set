section \<open>Replacement\<close>

theory Replacement
imports
  Bounded_Quantifiers
  Equality
begin

section \<open>Replacement\<close>

(*TODO: localise*)
syntax
  "_repl" :: \<open>[set, pttrn, set] => set\<close> ("(1{_ |/ _ \<in> _})")
translations
  "{y | x \<in> A}" \<rightleftharpoons> "CONST repl A (\<lambda>x. y)"

lemma app_mem_repl_if_mem [intro]: "a \<in> A \<Longrightarrow> f a \<in> {f x | x \<in> A}"
  by (unfold mem_repl_iff_mem_eq) auto

(*LP: Useful for coinduction proofs*)
lemma mem_repl_if_mem_if_eq_app [elim]: "\<lbrakk>b = f a; a \<in> A\<rbrakk> \<Longrightarrow> b \<in> {f x | x \<in> A}"
  using app_mem_repl_if_mem by auto

(*The converse of the above*)
lemma bex_eq_app_if_mem_repl: "b \<in> {f x | x \<in> A} \<Longrightarrow> \<exists>a \<in> A. b = f a"
  using mem_repl_iff_mem_eq by auto

lemma replE [elim!]:
  assumes "b \<in> {f x | x \<in> A}"
  obtains x where "x \<in> A" and "b = f x"
  using assms by (auto dest: bex_eq_app_if_mem_repl)

lemma repl_cong [cong]:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> {f x | x \<in> A} = {g x | x \<in> B}"
  by (rule subset_antisym) auto

lemma repl_repl_eq_repl [simp]: "{g b | b \<in> {f a | a \<in> A}} = {g (f a) | a \<in> A}"
  by (rule subset_antisym) auto

lemma repl_eq_dom [simp]: "{x | x \<in> A} = A"
  by (rule subset_antisym) auto

lemma repl_eq_empty [simp]: "{f x | x \<in> {}} = {}"
  by (rule subset_antisym) auto

lemma repl_eq_empty_iff [iff]: "{f x | x \<in> A} = {} \<longleftrightarrow> A = {}"
  by (auto dest: eqD intro!: eqI')

lemma repl_subset_repl_if_subset_dom [intro!]:
  "A \<subseteq> B \<Longrightarrow> {g y | y \<in> A} \<subseteq> {g y | y \<in> B}"
  by auto

lemma ball_repl_iff_ball [iff]: "(\<forall>x \<in> {f x | x \<in> A}. P x) \<longleftrightarrow> (\<forall>x \<in> A. P (f x))"
  by auto

lemma bex_repl_iff_bex [iff]: "(\<exists>x \<in> {f x | x \<in> A}. P x) \<longleftrightarrow> (\<exists>x \<in> A. P (f x))"
  by auto

end
