section \<open>Pairs (\<Sigma>-types)\<close>
theory Pairs
  imports Foundation
begin

definition pair :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "pair a b \<equiv> {{a}, {a, b}}"

definition fst :: \<open>set \<Rightarrow> set\<close>
  where "fst p \<equiv> THE a. \<exists>b. p = pair a b"

definition snd :: \<open>set \<Rightarrow> set\<close>
  where "snd p \<equiv> THE b. \<exists>a. p = pair a b"

(*TODO: localise*)
syntax
  "_tuple" :: \<open>args \<Rightarrow> set\<close> ("\<langle>_\<rangle>")
translations
  "\<langle>x, y, z\<rangle>" \<rightleftharpoons> "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>" \<rightleftharpoons> "CONST pair x y"

lemma pair_eq_iff [iff]: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<longleftrightarrow> a = c \<and> b = d"
  unfolding pair_def by (auto dest: iffD1[OF upair_eq_iff])

lemma eq_if_pair_eq_left: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<Longrightarrow> a = c" by simp

lemma eq_if_pair_eq_right: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<Longrightarrow> b = d" by simp

lemma fst_pair_eq [simp, intro!]: "fst \<langle>a, b\<rangle> = a"
  by (simp add: fst_def)

lemma snd_pair_eq [simp, intro!]: "snd \<langle>a, b\<rangle> = b"
  by (simp add: snd_def)

lemma pair_ne_empty [simp, intro!]: "\<langle>a, b\<rangle> \<noteq> {}"
  unfolding pair_def by blast

lemma fst_snd_eq_if_eq_pair [simp]: "p = \<langle>a, b\<rangle> \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by simp

lemma pair_ne_fst [simp, intro!]: "\<langle>a, b\<rangle> \<noteq> a"
  unfolding pair_def using mem_asym
  by (intro ne_if_ex_mem_not_mem, intro exI[where x="{a}"]) auto

lemma pair_ne_snd [simp, intro!]: "\<langle>a, b\<rangle> \<noteq> b"
  unfolding pair_def using mem_asym
  by (intro ne_if_ex_mem_not_mem, intro exI[where x="{a, b}"]) auto

lemma pair_not_mem_fst [simp, intro!]: "\<langle>a, b\<rangle> \<notin> a"
  unfolding pair_def using not_mem_if_mem_if_mem by auto

lemma pair_not_mem_snd [simp, intro!]: "\<langle>a, b\<rangle> \<notin> b"
  unfolding pair_def by (auto intro: eqI dest: not_mem_if_mem_if_mem)


subsection \<open>Set-Theoretic Dependent Pair Type\<close>

definition dep_pairs :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set\<close>
  where "dep_pairs A B \<equiv> \<Union>x \<in> A. \<Union>y \<in> B x. {\<langle>x, y\<rangle>}"

(*TODO: localise*)
syntax
  "_dep_pairs" :: \<open>[pttrn, set, set \<Rightarrow> set] \<Rightarrow> set\<close> ("\<Sum>_ \<in> _./ _" [0, 0, 100])
translations
  "\<Sum>x \<in> A. B" \<rightleftharpoons> "CONST dep_pairs A (\<lambda>x. B)"

abbreviation pairs :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close>
  where "pairs A B \<equiv> \<Sum>_ \<in> A. B"

bundle hotg_pairs_syntax begin notation pairs (infixl "\<times>" 80) end
bundle no_hotg_pairs_syntax begin no_notation pairs (infixl "\<times>" 80) end

unbundle hotg_pairs_syntax

lemma mem_dep_pairs_iff [iff]: "\<langle>a, b\<rangle> \<in> \<Sum>x \<in> A. (B x) \<longleftrightarrow> a \<in> A \<and> b \<in> B a"
  unfolding dep_pairs_def by blast

lemma mem_if_mem_dep_pairs_fst: "\<langle>a, b\<rangle> \<in> \<Sum>x \<in> A. (B x) \<Longrightarrow> a \<in> A" by simp
lemma mem_if_mem_dep_pairs_snd: "\<langle>a, b\<rangle> \<in> \<Sum>x \<in> A. (B x) \<Longrightarrow> b \<in> B a" by simp

lemma mem_dep_pairsE [elim!]:
  assumes "p \<in> \<Sum>x \<in> A. (B x)"
  obtains x y where "x \<in> A" "y \<in> B x" "p = \<langle>x, y\<rangle>"
  using assms unfolding dep_pairs_def by blast

lemma dep_pairs_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A' \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> \<Sum>x \<in> A. (B x) = \<Sum>x \<in> A'. (B' x)"
  unfolding dep_pairs_def by auto

lemma fst_mem_if_mem_dep_pairs: "p \<in> \<Sum>x \<in> A. (B x) \<Longrightarrow> fst p \<in> A"
  by auto

lemma snd_mem_if_mem_dep_pairs: "p \<in> \<Sum>x \<in> A. (B x) \<Longrightarrow> snd p \<in> B (fst p)"
  by auto

lemma fst_snd_eq_pair_if_mem_dep_pairs [simp]:
  "p \<in> \<Sum>x \<in> P. (B x) \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by auto

lemma dep_pairs_empty_dom_eq_empty [simp, intro!]: "\<Sum>x \<in> {}. (B x) = {}"
  by auto

lemma dep_pairs_empty_eq_empty [simp, intro!]: "\<Sum>x \<in> A. {} = {}"
  by auto

lemma pairs_empty_iff [iff]: "A \<times> B = {} \<longleftrightarrow> A = {} \<or> B = {}"
  by (auto intro!: eqI)

lemma pairs_singleton_eq [simp, intro!]: "{a} \<times> {b} = {\<langle>a, b\<rangle>}"
  by (rule eqI) auto

lemma dep_pairs_subset_pairs: "\<Sum>x \<in> A. (B x) \<subseteq> A \<times> (\<Union>x \<in> A. (B x))"
  by auto


text \<open>Splitting quantifiers:\<close>

lemma bex_dep_pairs_iff_bex_bex [iff]:
  "(\<exists>z \<in> \<Sum>x \<in> A. (B x). P z) \<longleftrightarrow> (\<exists>x \<in> A. \<exists>y \<in> B x. P \<langle>x, y\<rangle>)"
  by blast

lemma ball_dep_pairs_iff_ball_ball [iff]:
  "(\<forall>z \<in> \<Sum>x \<in> A. (B x). P z) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> B x. P \<langle>x,y\<rangle>)"
  by blast


subsection \<open>Monotonicity\<close>

lemma dep_pairs_covariant:
  assumes "A \<subseteq> A'"
  and "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> B' x"
  shows "(\<Sum>x \<in> A. B x) \<subseteq> (\<Sum>x \<in> A'. B' x)"
  using assms by auto

lemma dep_pairs_covariant_dom:
  assumes "A \<subseteq> A'"
  shows "(\<Sum>x \<in> A. B x) \<subseteq> (\<Sum>x \<in> A. B x)"
  using assms by (intro dep_pairs_covariant) auto

lemma dep_pairs_covariant_rng:
  assumes "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> B' x"
  shows "(\<Sum>x \<in> A. (B x)) \<subseteq> (\<Sum>x \<in> A. (B' x))"
  using assms by (intro dep_pairs_covariant) auto

lemma subset_pairs_subsetI: "A \<subseteq> A' \<Longrightarrow> B \<subseteq> B' \<Longrightarrow> A \<times> B \<subseteq> A' \<times> B'"
  by (rule dep_pairs_covariant) auto

lemma subset_pairs_subset_if_subset_left: "A \<subseteq> A' \<Longrightarrow> A \<times> B \<subseteq> A' \<times> B"
  by (rule subset_pairs_subsetI) auto

lemma subset_pairs_subset_if_subset_right: "B \<subseteq> B' \<Longrightarrow> A \<times> B \<subseteq> A \<times> B'"
  by (rule subset_pairs_subsetI) auto


subsection \<open>Functions on Dependent Pairs\<close>

definition "uncurry f p \<equiv> f (fst p) (snd p)"

(*TODO: localise*)
syntax
  "_uncurry_args"  :: "args => pttrn" ("\<langle>_\<rangle>")
translations
  "\<lambda>\<langle>x, y, zs\<rangle>. b" \<rightleftharpoons> "CONST uncurry (\<lambda>x \<langle>y, zs\<rangle>. b)"
  "\<lambda>\<langle>x, y\<rangle>. b" \<rightleftharpoons> "CONST uncurry (\<lambda>x y. b)"

lemma uncurry [simp, intro!]: "uncurry f \<langle>a, b\<rangle> = f a b"
  unfolding uncurry_def by simp

definition "swap p = \<langle>snd p, fst p\<rangle>"

lemma swap_pair_eq [simp]: "swap \<langle>x, y\<rangle> = \<langle>y, x\<rangle>" unfolding swap_def by simp


end