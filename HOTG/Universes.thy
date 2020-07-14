section \<open>Universes\<close>

theory Universes
imports Union_Intersection
begin

abbreviation V :: set where "V \<equiv> univ {}"

lemma
  assumes "ZF_closed U" and "X \<in> U"
  shows
    ZF_closed_union [elim!]: "\<Union>X \<in> U" and
    ZF_closed_powerset [elim!]: "powerset X \<in> U" and
    ZF_closed_replacement: "(\<And>x. x \<in> X \<Longrightarrow> f x \<in> U) \<Longrightarrow> repl X f \<in> U"
  using assms by (auto simp: ZF_closed_def)

lemma
  assumes "A \<in> univ X"
  shows univ_closed_union [intro!]: "\<Union>A \<in> univ X"
  and univ_closed_powerset [intro!]: "powerset A \<in> univ X"
  and univ_closed_replacement [intro]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> univ X) \<Longrightarrow> repl A f \<in> univ X"
  using univ_ZF_closed[of X] assms by (auto intro: ZF_closed_replacement)

text \<open>Variations on transitivity:\<close>

lemma univ_transitive: "A \<in> univ X \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> univ X"
  using univ_trans[unfolded mem_transitive_def] by auto

lemma univ_transitive2: "A \<in> univ X \<Longrightarrow> A \<subseteq> univ X"
  using univ_transitive by auto

lemma univ_transitive3: "x \<in> X \<Longrightarrow> x \<in> univ X"
  using univ_transitive univ_elem by auto

lemma empty_in_univ [simp]: "{} \<in> univ X"
proof -
  have "X \<in> univ X" by (rule univ_elem)
  then have "powerset X \<subseteq> univ X" by (intro univ_transitive2) blast
  then show "{} \<in> univ X" by auto
qed

lemma univ_subset [simp]: "A \<subseteq> univ A"
  by (auto intro: univ_transitive univ_elem)

lemma univ_upair_closed [intro]:
  "\<lbrakk>x \<in> univ X; y \<in> univ X\<rbrakk> \<Longrightarrow> upair x y \<in> univ X"
  unfolding upair_def by (intro univ_closed_replacement) auto

lemma univ_cons_closed [intro]:
  "x \<in> univ X \<Longrightarrow> A \<in> univ X \<Longrightarrow> cons x A \<in> univ X"
  unfolding cons_def by (intro univ_closed_union univ_upair_closed)

corollary univ_pair_closed [intro]:
  "\<lbrakk>x \<in> univ X; y \<in> univ X\<rbrakk> \<Longrightarrow> {x, y} \<in> univ X"
  by (subst pair_eq_upair, blast)

lemma univ_bin_union_closed [intro]: "\<lbrakk>x \<in> univ X; y \<in> univ X\<rbrakk> \<Longrightarrow> x \<union> y \<in> univ X"
  unfolding bin_union_def by auto

lemma univ_singleton_closed [intro]: "x \<in> univ U \<Longrightarrow> {x} \<in> univ U"
  by auto

lemma bin_union_univ_eq_univ: "A \<in> univ U \<Longrightarrow> A \<union> univ U = univ U"
  by (rule extensionality) (auto intro: univ_transitive)


end
