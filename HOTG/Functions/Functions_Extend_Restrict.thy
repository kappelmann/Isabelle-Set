theory Functions_Extend_Restrict
  imports Functions_Base
begin

subsection \<open>Extending Functions\<close>

lemma extend_mem_dep_functionsI:
  assumes f_dep_fun: "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "x \<notin> A"
  shows "extend x y f \<in> (x' \<in> insert x A) \<rightarrow> (if x' = x then {y} else B x')"
    (is "?lhs \<in> dep_functions ?rhs_dom ?rhs_fun")
proof
  show "left_total (insert x A) (extend x y f)"
  proof (standard, standard)
    fix x' assume "x' \<in> insert x A"
    then show "\<exists>y'. \<langle>x', y'\<rangle> \<in> extend x y f"
    proof
      assume "x' \<in> A"
      with assms have "\<langle>x', f`x'\<rangle> \<in> f" by auto
      then show "\<exists>y'. \<langle>x', y'\<rangle> \<in> extend x y f" by (auto intro: mem_extendI')
    qed auto
  qed
  show "right_unique (insert x A) (extend x y f)"
    using assms by (auto intro!: right_uniqueI)
qed (insert assms, auto elim!: mem_dep_functionE)

lemma extend_mem_dep_functionsI':
  assumes f_dep_fun: "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "x \<notin> A"
  and "y \<in> B x"
  shows "extend x y f \<in> (x \<in> insert x A) \<rightarrow> (B x)"
proof (rule mem_dep_functions_covariant_codom)
  show "extend x y f \<in> (x' \<in> insert x A) \<rightarrow> (if x' = x then {y} else B x')"
    by (fact extend_mem_dep_functionsI[OF assms(1-2)])
qed (insert assms, auto split: if_splits)

lemma extend_mem_functionsI:
  assumes "f \<in> A \<rightarrow> B"
  and "x \<notin> A"
  shows "extend x y f \<in> functions (insert x A) (insert y B)"
proof (rule mem_dep_functions_covariant_codom)
  show "extend x y f \<in> (x' \<in> insert x A) \<rightarrow> (if x' = x then {y} else B)"
    by (fact extend_mem_dep_functionsI[OF assms])
qed (insert assms, auto split: if_splits)


subsection \<open>Gluing\<close>

lemma glue_mem_dep_functionsI:
  fixes F defines "D \<equiv> \<Union>f \<in> F. dom f"
  assumes all_fun: "\<And>f. f \<in> F \<Longrightarrow> \<exists>A. f \<in> (x \<in> A) \<rightarrow> B x"
  and F_right_unique: "right_unique D (glue F)"
  shows "glue F \<in> (x \<in> D) \<rightarrow> B x"
proof (rule mem_dep_functionsI)
  show "left_total D (glue F)" unfolding D_def by auto
  show "glue F \<subseteq> \<Sum>x \<in> D. (B x)"
    unfolding D_def using all_fun
    by (intro glue_subset_dep_pairsI) (auto elim!: mem_dep_functionE)
qed (fact F_right_unique)

lemma glue_upair_mem_dep_functionsI:
  assumes "f \<in> (x \<in> A) \<rightarrow> B x" "g \<in> (x \<in> A') \<rightarrow> B x"
  and "agree (A \<inter> A') {f, g}"
  shows "glue {f, g} \<in> (x \<in> A \<union> A') \<rightarrow> B x"
proof -
  have "(\<Union>f \<in> {f, g}. dom f) = (\<Union>f \<in> {f}. dom f) \<union> (\<Union>f \<in> {g}. dom f)"
    by (auto simp only: idx_union_bin_union_dom_eq_bin_union_idx_union)
  also have "... = dom f \<union> dom g" by auto
  also have "... = A \<union> A'" using assms by simp
  finally have "A \<union> A' = (\<Union>f \<in> {f, g}. dom f)" by auto
  moreover have "right_unique (A \<union> A') (glue {f, g})"
    using assms by (auto intro!: right_uniqueI intro: agreeD)
  ultimately show ?thesis using assms by (auto intro: glue_mem_dep_functionsI)
qed


subsection \<open>Restriction\<close>

lemma restrict_mem_dep_functions_if_mem_dep_functions_if_agree:
  assumes "agree A F"
  and "f \<in> (x \<in> A) \<rightarrow> (B x)"
  and "f \<in> F"
  and "g \<in> F"
  shows "g\<restriction>A \<in> (x \<in> A) \<rightarrow> (B x)"
proof -
  from assms have "g\<restriction>A = f\<restriction>A" by (auto elim: restrict_eq_restrict_if_agree)
  also have "... = f" using \<open>f \<in> (x \<in> A) \<rightarrow> (B x)\<close> by auto
  finally show ?thesis using \<open>f \<in> (x \<in> A) \<rightarrow> (B x)\<close> by simp
qed

lemma restriction_mem_dep_functions_collectI:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  shows "f\<restriction>P \<in> (x \<in> {x \<in> A | P x}) \<rightarrow> (B x)"
  using assms
  by (elim mem_dep_functionsE, intro mem_dep_functionsI)
    (auto intro: left_total_and_restrictI
      right_unique_contravariant_set[OF right_unique_contravariant_pred])



end