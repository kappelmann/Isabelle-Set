\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Pairs (\<open>\<Sigma>\<close>-types)\<close>
theory Pairs
  imports
    Foundation
begin

definition pair :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "pair a b \<equiv> {{a}, {a, b}}"

definition fst :: \<open>set \<Rightarrow> set\<close>
  where "fst p \<equiv> THE a. \<exists>b. p = pair a b"

definition snd :: \<open>set \<Rightarrow> set\<close>
  where "snd p \<equiv> THE b. \<exists>a. p = pair a b"

bundle hotg_pair_syntax
begin
syntax "_pair" :: \<open>args \<Rightarrow> set\<close> ("\<langle>_\<rangle>")
end
bundle no_hotg_pair_syntax
begin
no_syntax "_pair" :: \<open>args \<Rightarrow> set\<close> ("\<langle>_\<rangle>")
end
unbundle hotg_pair_syntax

translations
  "\<langle>x, y, z\<rangle>" \<rightleftharpoons> "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>" \<rightleftharpoons> "CONST pair x y"

definition "is_pair p \<equiv> \<exists>x y. p = \<langle>x, y\<rangle>"

lemma is_pairI [intro]: "p = \<langle>x, y\<rangle> \<Longrightarrow> is_pair p"
  unfolding is_pair_def by blast

lemma is_pairE [elim!]:
  assumes "is_pair p"
  obtains x y where "p = \<langle>x, y\<rangle>"
  using assms unfolding is_pair_def by blast

lemma pair_eq_iff [iff]: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<longleftrightarrow> a = c \<and> b = d"
  unfolding pair_def by (auto dest: iffD1[OF upair_eq_iff])

lemma eq_if_pair_eq_left: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<Longrightarrow> a = c" by simp

lemma eq_if_pair_eq_right: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<Longrightarrow> b = d" by simp

lemma fst_pair_eq [simp]: "fst \<langle>a, b\<rangle> = a"
  by (simp add: fst_def)

lemma snd_pair_eq [simp]: "snd \<langle>a, b\<rangle> = b"
  by (simp add: snd_def)

lemma pair_ne_empty [iff]: "\<langle>a, b\<rangle> \<noteq> {}"
  unfolding pair_def by blast

lemma fst_snd_eq_if_is_pair [simp]: "is_pair p \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by auto

lemma pair_ne_fst [iff]: "\<langle>a, b\<rangle> \<noteq> a"
  unfolding pair_def using not_mem_if_mem
  by (intro ne_if_ex_mem_not_mem, intro exI[where x="{a}"]) auto

lemma pair_ne_snd [iff]: "\<langle>a, b\<rangle> \<noteq> b"
  unfolding pair_def using not_mem_if_mem
  by (intro ne_if_ex_mem_not_mem, intro exI[where x="{a, b}"]) auto

lemma pair_not_mem_fst [iff]: "\<langle>a, b\<rangle> \<notin> a"
  unfolding pair_def using not_mem_if_mem_if_mem by auto

lemma pair_not_mem_snd [iff]: "\<langle>a, b\<rangle> \<notin> b"
  unfolding pair_def by (auto dest: not_mem_if_mem_if_mem)


subsection \<open>Set-Theoretic Dependent Pair Type\<close>

definition dep_pairs :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set\<close>
  where "dep_pairs A B \<equiv> \<Union>a \<in> A. \<Union>y \<in> B a. {\<langle>a, y\<rangle>}"

bundle hotg_dependent_pairs_syntax
begin
syntax
  "_dep_pairs" :: \<open>[pttrn, set, set \<Rightarrow> set] \<Rightarrow> set\<close> ("\<Sum>_ \<in> _./ _" [0, 0, 100] 51)
end
bundle no_hotg_dependent_pairs_syntax
begin
no_syntax
  "_dep_pairs" :: \<open>[pttrn, set, set \<Rightarrow> set] \<Rightarrow> set\<close> ("\<Sum>_ \<in> _./ _" [0, 0, 100] 51)
end
unbundle hotg_dependent_pairs_syntax

translations
  "\<Sum>x \<in> A. B" \<rightleftharpoons> "CONST dep_pairs A (\<lambda>x. B)"

abbreviation pairs :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "pairs A B \<equiv> \<Sum>_ \<in> A. B"

bundle hotg_pairs_syntax begin notation pairs (infixl "\<times>" 80) end
bundle no_hotg_pairs_syntax begin no_notation pairs (infixl "\<times>" 80) end

unbundle hotg_pairs_syntax

lemma mem_dep_pairsI:
  assumes "is_pair p"
  and "fst p \<in> A"
  and "snd p \<in> B (fst p)"
  shows "p \<in> (\<Sum>x \<in> A. B x)"
  using assms unfolding dep_pairs_def by force

lemma pair_mem_dep_pairsI [intro!]:
  assumes "a \<in> A"
  and "b \<in> B a"
  shows "\<langle>a, b\<rangle> \<in> (\<Sum>x \<in> A. B x)"
  using assms by (auto intro: mem_dep_pairsI)

lemma mem_dep_pairsE [elim!]:
  assumes "p \<in> (\<Sum>x \<in> A. B x)"
  obtains x y where "x \<in> A" "y \<in> B x" "p = \<langle>x, y\<rangle>"
  using assms unfolding dep_pairs_def by blast

lemma pair_mem_dep_pairs_iff: "\<langle>a, b\<rangle> \<in> (\<Sum>x \<in> A. B x) \<longleftrightarrow> a \<in> A \<and> b \<in> B a" by blast

lemma mem_if_mem_dep_pairs_fst: "\<langle>a, b\<rangle> \<in> (\<Sum>x \<in> A. B x) \<Longrightarrow> a \<in> A" by auto
lemma mem_if_mem_dep_pairs_snd: "\<langle>a, b\<rangle> \<in> (\<Sum>x \<in> A. B x) \<Longrightarrow> b \<in> B a" by auto

lemma dep_pairs_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> (\<Sum>x \<in> A. B x) = (\<Sum>x \<in> A'. B' x)"
  unfolding dep_pairs_def by auto

lemma fst_mem_if_mem_dep_pairs: "p \<in> \<Sum>x \<in> A. B x \<Longrightarrow> fst p \<in> A"
  by auto

lemma snd_mem_if_mem_dep_pairs: "p \<in> \<Sum>x \<in> A. B x \<Longrightarrow> snd p \<in> B (fst p)"
  by auto

lemma is_pair_if_mem_dep_pairs: "p \<in> \<Sum>x \<in> P. B x \<Longrightarrow> is_pair p"
  by auto

lemma dep_pairs_empty_dom_eq_empty [simp]: "\<Sum>x \<in> {}. B x = {}"
  by auto

lemma dep_pairs_empty_eq_empty [simp]: "\<Sum>x \<in> A. {} = {}"
  by auto

lemma pairs_empty_iff [iff]: "A \<times> B = {} \<longleftrightarrow> A = {} \<or> B = {}"
  by (auto intro!: eqI)

lemma pairs_singleton_eq [simp]: "{a} \<times> {b} = {\<langle>a, b\<rangle>}"
  by (rule eqI) auto

lemma dep_pairs_subset_pairs: "\<Sum>x \<in> A. B x \<subseteq> A \<times> (\<Union>x \<in> A. B x)"
  by auto


text \<open>Splitting quantifiers:\<close>

lemma bex_dep_pairs_iff_bex_bex [iff]:
  "(\<exists>z \<in> \<Sum>x \<in> A. B x. P z) \<longleftrightarrow> (\<exists>x \<in> A. \<exists>y \<in> B x. P \<langle>x, y\<rangle>)"
  by blast

lemma ball_dep_pairs_iff_ball_ball [iff]:
  "(\<forall>z \<in> \<Sum>x \<in> A. B x. P z) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B x. P \<langle>x,y\<rangle>)"
  by blast


subsection \<open>Monotonicity\<close>

lemma mono_dep_pairs:
  assumes "A \<subseteq> A'"
  and "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> B' x"
  shows "(\<Sum>x \<in> A. B x) \<subseteq> (\<Sum>x \<in> A'. B' x)"
  using assms by force

lemma mono_dep_pairs_dom:
  assumes "A \<subseteq> A'"
  shows "(\<Sum>x \<in> A. B x) \<subseteq> (\<Sum>x \<in> A'. B x)"
  using assms by (intro mono_dep_pairs) auto

lemma mono_dep_pairs_codom:
  assumes "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> B' x"
  shows "(\<Sum>x \<in> A. B x) \<subseteq> (\<Sum>x \<in> A. (B' x))"
  using assms by (intro mono_dep_pairs) auto

lemma mono_subset_pairs_dom: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>)) (\<lambda>A. A \<times> B)"
  by auto

lemma mono_subset_pairs_codom: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>)) (\<lambda>B. A \<times> B)"
  by auto


subsection \<open>Functions on Dependent Pairs\<close>

definition "uncurry f p \<equiv> f (fst p) (snd p)"

bundle hotg_uncurry_syntax
begin
syntax "_uncurry_args"  :: "args => pttrn" ("\<langle>_\<rangle>")
end
bundle no_hotg_uncurry_syntax
begin
no_syntax "_uncurry_args"  :: "args => pttrn" ("\<langle>_\<rangle>")
end
unbundle hotg_uncurry_syntax

translations
  "\<lambda>\<langle>x, y, zs\<rangle>. b" \<rightleftharpoons> "CONST uncurry (\<lambda>x \<langle>y, zs\<rangle>. b)"
  "\<lambda>\<langle>x, y\<rangle>. b" \<rightleftharpoons> "CONST uncurry (\<lambda>x y. b)"

lemma uncurry [simp]: "uncurry f \<langle>a, b\<rangle> = f a b"
  unfolding uncurry_def by simp

definition "swap p = \<langle>snd p, fst p\<rangle>"

lemma swap_pair_eq [simp]: "swap \<langle>x, y\<rangle> = \<langle>y, x\<rangle>" unfolding swap_def by simp

lemma swap_pair_eq' [simp]: "is_pair p \<Longrightarrow> swap p = \<langle>snd p, fst p\<rangle>"
  unfolding swap_def by simp

end