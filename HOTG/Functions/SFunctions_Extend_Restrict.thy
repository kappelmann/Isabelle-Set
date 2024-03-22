\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Extending Functions\<close>
theory SFunctions_Extend_Restrict
  imports SFunctions_Base
begin

context
  notes [[urule chained = insert]]
begin

lemma extend_mem_dep_functionsI:
  assumes "f \<in> (x \<in> A) \<rightarrow>s (B x)"
  and "x \<notin> A"
  shows "extend x y f \<in> (x' \<in> insert x A) \<rightarrow>s (if x' = x then {y} else B x')"
proof
  show "left_total_on (insert x A) (extend x y f)" supply set_to_HOL_simp[rec_uhint]
  proof (urule left_total_on_if_le_in_dom, urule subsetI)
    fix x' assume "x' \<in> insert x A"
    then show "x' \<in> dom (extend x y f)"
    proof (rule mem_insertE)
      assume "x' \<in> A"
      with assms have "\<langle>x', f`x'\<rangle> \<in> f" by auto
      then show "x' \<in> dom (extend x y f)" by auto
    qed auto
  qed
  from assms show "right_unique_on (insert x A) (extend x y f)"
    by (urule right_unique_onI) auto
qed (use assms in \<open>auto elim!: mem_dep_functionE\<close>)

lemma extend_mem_dep_functionsI':
  assumes "f \<in> (x \<in> A) \<rightarrow>s (B x)"
  and "x \<notin> A"
  and "y \<in> B x"
  shows "extend x y f \<in> (x \<in> insert x A) \<rightarrow>s (B x)"
  using assms
  by (urule mem_dep_functions_covariant_codom, urule extend_mem_dep_functionsI) auto

lemma extend_mem_functionsI:
  assumes "f \<in> A \<rightarrow>s B"
  and "x \<notin> A"
  shows "extend x y f \<in> functions (insert x A) (insert y B)"
  using assms
  by (urule mem_dep_functions_covariant_codom, urule extend_mem_dep_functionsI) auto

end

subsection \<open>Gluing\<close>

lemma glue_mem_dep_functionsI:
  fixes F defines "D \<equiv> \<Union>f \<in> F. dom f"
  assumes all_fun: "\<And>f. f \<in> F \<Longrightarrow> \<exists>A. f \<in> (x \<in> A) \<rightarrow>s B x"
  and F_right_unique: "right_unique_on D (glue F)"
  shows "glue F \<in> (x \<in> D) \<rightarrow>s B x"
proof (rule mem_dep_functionsI)
  show "left_total_on D (glue F)" unfolding D_def by auto
  show "glue F \<subseteq> \<Sum>x \<in> D. (B x)"
    unfolding D_def using all_fun
    by (intro glue_subset_dep_pairsI) (auto elim!: mem_dep_functionE)
qed (fact F_right_unique)

lemma glue_upair_mem_dep_functionsI:
  assumes f_dep_fun: "f \<in> (x \<in> A) \<rightarrow>s B x"
  and g_dep_fun: "g \<in> (x \<in> A') \<rightarrow>s B x"
  and agree_fg: "agree (A \<inter> A') {f, g}"
  shows "glue {f, g} \<in> (x \<in> A \<union> A') \<rightarrow>s B x"
proof -
  have "(\<Union>f \<in> {f, g}. dom f) = (\<Union>f \<in> {f}. dom f) \<union> (\<Union>f \<in> {g}. dom f)"
    by (rule eqI) (auto simp only: idx_union_bin_union_dom_eq_bin_union_idx_union)
  also have "... = dom f \<union> dom g" by (rule eqI) auto
  also have "... = A \<union> A'" using assms by simp
  finally have [simp]: "A \<union> A' = (\<Union>f \<in> {f, g}. dom f)" by auto
  have "right_unique_on (A \<union> A') (glue {f, g})"
  proof (urule right_unique_onI)
    fix x y y' presume "x \<in> A \<union> A'"
      and pairs_mem: "\<langle>x, y\<rangle> \<in> glue {f, g}" "\<langle>x, y'\<rangle> \<in> glue {f, g}"
    show "y = y'"
    proof (cases "x \<in> A \<inter> A'")
      case True
      with agree_fg pairs_mem have "\<langle>x, y\<rangle> \<in> f" "\<langle>x, y'\<rangle> \<in> f" by (auto dest: agree_setD)
      with f_dep_fun show "y = y'" by (auto dest: right_unique_onD)
    qed (insert f_dep_fun g_dep_fun pairs_mem,
      auto 0 3 elim!: mem_dep_functionsE dest: right_unique_onD)
  qed auto
  with assms show ?thesis by (urule glue_mem_dep_functionsI where chained = insert) auto
qed


subsection \<open>Restriction\<close>

lemma restrict_left_mem_dep_functions_if_mem_dep_functions_if_agree:
  assumes "agree A F"
  and "f \<in> (x \<in> A) \<rightarrow>s (B x)"
  and "f \<in> F"
  and "g \<in> F"
  shows "g\<restriction>\<^bsub>A\<^esub> \<in> (x \<in> A) \<rightarrow>s (B x)"
proof -
  from assms have "g\<restriction>\<^bsub>A\<^esub>  = f\<restriction>\<^bsub>A\<^esub>" by (auto elim: set_restrict_left_eq_set_restrict_left_if_agree_set)
  also have "... = f" using \<open>f \<in> (x \<in> A) \<rightarrow>s (B x)\<close> by auto
  finally show ?thesis using \<open>f \<in> (x \<in> A) \<rightarrow>s (B x)\<close> by simp
qed

lemma restrict_left_mem_dep_functions_collectI:
  assumes "f \<in> (x \<in> A) \<rightarrow>s (B x)"
  shows "f\<restriction>\<^bsub>P\<^esub> \<in> (x \<in> {x \<in> A | P x}) \<rightarrow>s (B x)"
proof (rule mem_dep_functionsI)
  have "right_unique_on A f \<le> right_unique_on {x \<in> A | P x} f\<restriction>\<^bsub>P\<^esub>"
    by (urule antimono_right_unique_on[THEN dep_mono_wrt_relD, THEN Dep_Fun_Rel_relD]) auto
  moreover from assms have "right_unique_on A f" by blast
  ultimately show "right_unique_on {x \<in> A | P x} f\<restriction>\<^bsub>P\<^esub>" by auto
qed (use assms in \<open>force\<close>)+


end