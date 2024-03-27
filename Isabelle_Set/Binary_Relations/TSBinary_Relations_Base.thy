\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Typed Set-Theoretic Binary Relations\<close>
theory TSBinary_Relations_Base
  imports
    TSPairs
begin

subsection \<open>Dependent Binary Relations\<close>

definition [typedef]: "Dep_Bin_Rel A B \<equiv> Collection (\<Sum>x : A. (B x))"

abbreviation "Bin_Rel A B \<equiv> Dep_Bin_Rel A (\<lambda>_. B)"

lemma subset_dep_pairs_iff_Dep_Bin_Rel:
  "R \<subseteq> (\<Sum>x \<in> A. (B x)) \<longleftrightarrow> R : Dep_Bin_Rel (Element A) (\<lambda>x. Element (B x))"
  by unfold_types auto

soft_type_translation
  "R \<subseteq> (\<Sum>x \<in> A. (B x))" \<rightleftharpoons> "R : Dep_Bin_Rel (Element A) (\<lambda>x. Element (B x))"
  using subset_dep_pairs_iff_Dep_Bin_Rel by auto

lemma Dep_Bin_RelI:
  "(\<And>p. p \<in> R \<Longrightarrow> p : \<Sum>x : A. (B x)) \<Longrightarrow> R : Dep_Bin_Rel A B"
  unfolding Dep_Bin_Rel_def by (rule CollectionI)

lemma Dep_Bin_Rel_memE [elim]:
  assumes "R : Dep_Bin_Rel A B"
  and "p \<in> R"
  obtains x y where "x : A" "y : B x" "p = \<langle>x, y\<rangle>"
  using assms unfolding Dep_Bin_Rel_def
  by (auto dest: Collection_memD)

lemma Dep_Bin_Rel_covariant_dom:
  "R : Dep_Bin_Rel A B \<Longrightarrow> (\<And>x. x : A \<Longrightarrow> x : A') \<Longrightarrow> R : Dep_Bin_Rel A' B"
  unfolding Dep_Bin_Rel_def
  by (elim Collection_covariant) (blast intro: Dep_Pair_covariant_fst)

lemma Dep_Bin_Rel_covariant_codom:
  assumes "R : Dep_Bin_Rel A B"
  and "\<And>x y. x : A \<Longrightarrow> y : B x \<Longrightarrow> \<langle>x, y\<rangle> \<in> R \<Longrightarrow> y : B' x"
  shows "R : Dep_Bin_Rel A B'"
  using assms unfolding Dep_Bin_Rel_def
  by (elim Collection_covariant) (auto intro: Dep_Pair_covariant_snd)


end
