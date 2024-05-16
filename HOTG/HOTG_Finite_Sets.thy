\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Finite Sets\<close>
theory HOTG_Finite_Sets
  imports HOTG_Unordered_Pairs
begin

bundle hotg_finite_sets_syntax
begin
syntax "_finset" :: \<open>args \<Rightarrow> set\<close> ("{(_)}")
end
bundle no_hotg_finite_sets_syntax
begin
no_syntax "_finset" :: \<open>args \<Rightarrow> set\<close> ("{(_)}")
end
unbundle hotg_finite_sets_syntax
unbundle no_HOL_ascii_syntax

translations
  "{x, xs}" \<rightleftharpoons> "CONST insert x {xs}"
  "{x}" \<rightleftharpoons> "CONST insert x {}"

lemma singleton_eq_iff_eq [iff]: "{a} = {b} \<longleftrightarrow> a = b"
  by auto

lemma subset_singleton_iff_eq_or_eq [iff]: "A \<subseteq> {a} \<longleftrightarrow> A = {} \<or> A = {a}"
  by auto

lemma singleton_mem_iff_eq [iff]: "x \<in> {a} \<longleftrightarrow> x = a" by auto

lemma powerset_empty_eq [simp]: "powerset {} = {{}}"
  by auto

lemma powerset_singleton_eq [simp]: "powerset {a} = {{}, {a}}"
  by auto

lemma powerset_powerset_empty_eq [simp]: "powerset (powerset {}) = {{}, {{}}}"
  by simp

corollary powerset_singleton_elems [iff]: "x \<in> powerset {a} \<longleftrightarrow> x = {} \<or> x = {a}"
  by auto

corollary subset_singleton_iff [iff]: "x \<subseteq> {a} \<longleftrightarrow> x = {} \<or> x = {a}" by auto

lemma singleton_subset_iff_mem [iff]: "{a} \<subseteq> B \<longleftrightarrow> a \<in> B"
  by blast

lemma insert_singleton_eq_singleton_iff [iff]: "{a, b} = {c} \<longleftrightarrow> a = c \<and> b = c"
  by (subst insert_insert_eq_insert[of c, symmetric]) auto

lemma singleton_eq_insert_singleton_iff [iff]: "{a} = {b, c} \<longleftrightarrow> b = a \<and> c = a"
  using insert_singleton_eq_singleton_iff by (auto dest: sym[of "{a}"])

text \<open>@{term "upair x y"} and @{term "{x, y}"} are equal and thus interchangeable in developments.\<close>
lemma upair_eq_insert_singleton [simp]: "upair x y = {x, y}"
  unfolding upair_def by (rule eqI) auto


subsection \<open>Replacement\<close>

lemma repl_singleton_eq [simp]: "{f x | x \<in> {a}} = {f a}" by auto


end