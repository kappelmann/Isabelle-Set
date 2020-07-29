section \<open>Finite Sets\<close>

theory Finite_Sets
imports Unordered_Pairs
begin

syntax
  "_finset" :: \<open>args \<Rightarrow> set\<close> ("{(_)}")
translations
  "{x, xs}" \<rightleftharpoons> "CONST cons x {xs}"
  "{x}" \<rightleftharpoons> "CONST cons x {}"

(*TODO: proper rewrite rules for finite sets!*)

lemma singleton_eq_iff [iff]: "{a} = {b} \<longleftrightarrow> a = b"
  by (auto dest: equalityD)

lemma singleton_mem_iff: "x \<in> {a} \<longleftrightarrow> x = a" by auto

lemma mem_singletonD: "x \<in> {a} \<Longrightarrow> x = a" by auto
lemma mem_singleton: "a \<in> {a}" by auto

lemma singleton_eq_pair: "{a} = {a, a}" by (rule extensionality) auto

lemma powerset_empty_eq: "powerset {} = {{}}"
  by (rule extensionality) auto

lemma powerset_singleton: "powerset {a} = {{}, {a}}"
  by (rule extensionality) (auto intro: equalityI')

corollary powerset_singleton_elems [iff]: "x \<in> powerset {a} \<longleftrightarrow> x = {} \<or> x = {a}"
  using powerset_singleton by auto

corollary subset_singleton_iff [iff]: "x \<subseteq> {a} \<longleftrightarrow> x = {} \<or> x = {a}"
  using powerset_singleton_elems by auto
  
lemma singleton_subset_iff_mem [simp]: "{a} \<subseteq> B \<longleftrightarrow> a \<in> B" by auto

lemma mem_pair_iff: "x \<in> {a, b} \<longleftrightarrow> x = a \<or> x = b"
  by auto

lemma pair_eq_iff: "{a, b} = {c, d} \<longleftrightarrow> (a = c \<and> b = d) \<or> (a = d \<and> b = c)"
  by (auto intro: equalityI' dest: equalityD)

text \<open>\<^term>\<open>upair x y\<close> and \<^term>\<open>{x, y}\<close> are equal, and thus interchangeable in developments.\<close>
lemma upair_eq_pair: "upair x y = {x, y}"
  unfolding upair_def by (rule extensionality) (auto, auto)

lemma pair_eq_upair: "{x, y} = upair x y"
  by (fact upair_eq_pair[symmetric])

subsection \<open>Replacement\<close>

lemma repl_singleton [simp]: "{f x | x \<in> {a}} = {f a}"
  by (rule equalityI) auto

lemma repl_cons: "{f x | x \<in> cons x A} = cons (f x) {f x | x \<in> A}"
  by (rule extensionality) auto

end
