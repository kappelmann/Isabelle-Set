section \<open>Universes\<close>

theory Universes
imports Coproduct
begin

abbreviation V :: set where "V \<equiv> univ {}"

lemma
  assumes "ZF_closed U"
  and "X \<in> U"
  shows ZF_closed_union [elim!]: "\<Union>X \<in> U"
  and ZF_closed_powerset [elim!]: "powerset X \<in> U"
  and ZF_closed_repl:
    "(\<And>x. x \<in> X \<Longrightarrow> f x \<in> U) \<Longrightarrow> {f x | x \<in> X} \<in> U"
  using assms by (auto simp: ZF_closed_def)

lemma
  assumes "A \<in> univ X"
  shows univ_closed_union [intro!]: "\<Union>A \<in> univ X"
  and univ_closed_powerset [intro!]: "powerset A \<in> univ X"
  and univ_closed_repl [intro]:
    "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> univ X) \<Longrightarrow> {f x | x \<in> A} \<in> univ X"
  using ZF_closed_univ[of X]
  by (auto simp only: assms ZF_closed_repl)

text \<open>Variations on transitivity:\<close>

lemma mem_univ_trans: "A \<in> univ X \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> univ X"
  using mem_trans_univ unfolding mem_trans_def by auto

lemma mem_univ_trans': "x \<in> X \<Longrightarrow> x \<in> univ X"
  by (rule mem_univ_trans) auto

lemma subset_univ_if_mem: "A \<in> univ X \<Longrightarrow> A \<subseteq> univ X"
  using mem_univ_trans by auto

lemma empty_mem_univ [simp, intro!]: "{} \<in> univ X"
proof -
  have "X \<in> univ X" by (fact mem_univ)
  then have "powerset X \<subseteq> univ X" by (intro subset_univ_if_mem) blast
  then show "{} \<in> univ X" by auto
qed

lemma subset_univ [simp, intro!]: "A \<subseteq> univ A"
  by (auto intro: mem_univ_trans)

lemma univ_closed_upair [intro!]:
  "\<lbrakk>x \<in> univ X; y \<in> univ X\<rbrakk> \<Longrightarrow> upair x y \<in> univ X"
  unfolding upair_def
  by (intro univ_closed_repl, intro univ_closed_powerset) auto

lemma univ_closed_cons [intro!]:
  "x \<in> univ X \<Longrightarrow> A \<in> univ X \<Longrightarrow> cons x A \<in> univ X"
  unfolding cons_def using univ_closed_upair by auto

lemma univ_closed_pair [intro!]:
  "\<lbrakk>x \<in> univ X; y \<in> univ X\<rbrakk> \<Longrightarrow> \<langle>x, y\<rangle> \<in> univ X"
  unfolding pair_def by auto

lemma univ_closed_bin_union [intro!]: "\<lbrakk>x \<in> univ X; y \<in> univ X\<rbrakk> \<Longrightarrow> x \<union> y \<in> univ X"
  unfolding bin_union_def by auto

lemma univ_closed_singleton [intro!]: "x \<in> univ U \<Longrightarrow> {x} \<in> univ U"
  by auto

lemma bin_union_univ_eq_univ_if_mem: "A \<in> univ U \<Longrightarrow> A \<union> univ U = univ U"
  by (rule subset_antisym) (auto intro: mem_univ_trans)

lemma univ_closed_dep_pairs [intro]:
  assumes A_mem_univ: "A \<in> univ U"
  and univ_B_closed: "\<And>x. x \<in> A \<Longrightarrow> B x \<in> univ U"
  shows "\<Sum>x \<in> A. (B x) \<in> univ U"
proof -
  {
    fix x y
    assume "x \<in> A" "y \<in> B x"
    with univ_B_closed have "B x \<in> univ U" by simp
    with A_mem_univ \<open>x \<in> A\<close> \<open>y \<in> B x\<close> have "x \<in> univ U" and "y \<in> univ U"
      using mem_univ_trans by auto
  }
  then show ?thesis unfolding dep_pairs_def using assms
    by (intro univ_closed_union univ_closed_repl univ_closed_singleton
      univ_closed_pair)
qed

lemma subset_univ_if_subset_univ_pairs:
  "X \<subseteq> univ A \<times> univ A \<Longrightarrow> X \<subseteq> univ A"
  by auto

lemma univ_closed_pairs [intro!]:
  "X \<subseteq> univ A \<Longrightarrow> Y \<subseteq> univ A \<Longrightarrow> X \<times> Y \<subseteq> univ A"
  by auto

lemma univ_closed_inl [intro!]: "x \<in> univ A \<Longrightarrow> inl x \<in> univ A"
  unfolding inl_def by auto

lemma univ_closed_inr [intro!]: "x \<in> univ A \<Longrightarrow> inr x \<in> univ A"
  unfolding inr_def by auto

end
