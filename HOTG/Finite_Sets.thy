section \<open>Finite Sets\<close>

theory Finite_Sets
imports Unordered_Pairs
begin

(*TODO: localise*)
syntax
  "_finset" :: \<open>args \<Rightarrow> set\<close> ("{(_)}")
translations
  "{x, xs}" \<rightleftharpoons> "CONST cons x {xs}"
  "{x}" \<rightleftharpoons> "CONST cons x {}"

lemma singleton_eq_iff_eq [iff]: "{a} = {b} \<longleftrightarrow> a = b"
  by (auto dest: eqD)

lemma singleton_mem_iff_eq [iff]: "x \<in> {a} \<longleftrightarrow> x = a" by auto

lemma eq_if_mem_singleton [dest]: "x \<in> {a} \<Longrightarrow> x = a" by auto

lemma mem_singleton_self [simp, intro!]: "a \<in> {a}" by auto

lemma upair_self_eq_singleton [simp, intro!]: "{a, a} = {a}"
  by (rule eqI) auto

lemma powerset_empty_eq [simp, intro!]: "powerset {} = {{}}"
  by (rule eqI) auto

lemma powerset_singleton_eq [simp, intro!]: "powerset {a} = {{}, {a}}"
  by (rule eqI) (auto simp: subset_def intro: eqI)

lemma powerset_powerset_empty_eq [simp, intro!]:
  "powerset (powerset {}) = {{}, {{}}}"
  by simp

corollary powerset_singleton_elems [iff]: "x \<in> powerset {a} \<longleftrightarrow> x = {} \<or> x = {a}"
  using powerset_singleton_eq by auto

corollary subset_singleton_iff [iff]: "x \<subseteq> {a} \<longleftrightarrow> x = {} \<or> x = {a}"
  using powerset_singleton_elems by (blast dest: mem_powerset_if_subset)

lemma singleton_subset_iff_mem [iff]: "{a} \<subseteq> B \<longleftrightarrow> a \<in> B"
  by (unfold subset_def) simp

lemma mem_pair_iff [iff]: "x \<in> {a, b} \<longleftrightarrow> x = a \<or> x = b" by auto

lemma upair_eq_iff: "{a, b} = {c, d} \<longleftrightarrow> (a = c \<and> b = d) \<or> (a = d \<and> b = c)"
  by (auto intro: eqI dest: eqD)

lemma upair_eq_singleton_iff [iff]: "{a, b} = {c} \<longleftrightarrow> a = c \<and> b = c"
  by (subst upair_self_eq_singleton[of c, symmetric]) (auto simp only: upair_eq_iff)

lemma singleton_eq_upair_iff [iff]: "{a} = {b, c} \<longleftrightarrow> b = a \<and> c = a"
  using upair_eq_singleton_iff by (auto dest: sym[of "{a}"])

text \<open>\<^term>\<open>upair x y\<close> and \<^term>\<open>{x, y}\<close> are equal, and thus interchangeable in developments.\<close>
lemma upair_eq_cons_singleton: "upair x y = {x, y}"
  unfolding upair_def by (rule eqI) auto

lemma cons_singleton_eq_upair: "{x, y} = upair x y"
  by (fact upair_eq_cons_singleton[symmetric])

subsection \<open>Replacement\<close>

lemma repl_singleton_eq [simp]: "{f x | x \<in> {a}} = {f a}"
  by (rule eqI) auto

lemma repl_cons_eq: "{f x | x \<in> cons x A} = cons (f x) {f x | x \<in> A}"
  by (rule eqI) auto

end
