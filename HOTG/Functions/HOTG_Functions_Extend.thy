\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Extending Functions\<close>
theory HOTG_Functions_Extend
  imports
    HOTG_Binary_Relations_Extend
    HOTG_Binary_Relations_Left_Total
    HOTG_Binary_Relations_Right_Unique
    HOTG_Clean_Functions
    Transport.Binary_Relations_Function_Extend
begin

context
  notes set_to_HOL_simp[uhint]
  fixes R :: set
begin

lemma left_total_on_insert_extend_if_left_total_on:
  assumes "left_total_on A R"
  shows "left_total_on (insert x A) (extend x y R)"
  using assms by (urule left_total_on_eq_sup_extend_if_left_total_on)

lemma right_unique_on_insert_extend_if_not_mem_dom_if_right_unique_on:
  assumes "right_unique_on A R"
  and "x \<notin> dom R"
  shows "right_unique_on (insert x A) (extend x y R)"
  using assms by (urule right_unique_on_eq_sup_extend_if_not_in_dom_if_right_unique_on)

lemma set_rel_dep_mono_wrt_insert_if_extend_if_set_rel_dep_mono_wrt_setI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "x \<notin> dom R"
  shows "((x' : insert x A) \<rightarrow> (if x' = x then {y} else B x')) (extend x y R)"
proof -
  have [uhint]: "mem_of (if x' = x then {y} else B x') = (if x' = x then (=) y else mem_of (B x'))"
    for x' by auto
  from assms show ?thesis by (urule rel_dep_mono_wrt_eq_sup_if_extend_if_rel_dep_mono_wrt_predI)
qed

lemma set_rel_dep_mono_wrt_insert_extend_if_set_rel_dep_mono_wrt_setI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "x \<notin> dom R"
  and "y \<in> B x"
  shows "((x' : insert x A) \<rightarrow> B x') (extend x y R)"
  using assms by (urule rel_dep_mono_wrt_eq_sup_extend_if_rel_dep_mono_wrt_predI)

lemma set_crel_dep_mono_wrt_insert_if_extend_if_set_crel_dep_mono_wrt_setI:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "x \<notin> dom R"
  shows "((x' : insert x A) \<rightarrow>\<^sub>c (if x' = x then {y} else B x')) (extend x y R)"
proof -
  from assms have [uhint]:
    "mem_of (if x' = x then {y} else B x') = (if x' = x then (=) y else mem_of (B x'))"
    "is_bin_rel R" "is_bin_rel (extend x y R)" for x'
    by auto
  from assms show ?thesis by (urule crel_dep_mono_wrt_eq_sup_if_extend_if_crel_dep_mono_wrt_predI)
qed

lemma set_crel_dep_mono_wrt_insert_extend_if_set_crel_dep_mono_wrt_setI:
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "x \<notin> dom R"
  and "y \<in> B x"
  shows "((x' : insert x A) \<rightarrow>\<^sub>c B x') (extend x y R)"
proof -
  from assms have [uhint]: "is_bin_rel R" "is_bin_rel (extend x y R)" by auto
  from assms show ?thesis by (urule crel_dep_mono_wrt_eq_sup_extend_if_rel_dep_mono_wrt_predI)
qed

lemma set_crel_dep_mono_wrt_pred_sup_bin_union_if_eval_eq_if_set_crel_dep_mono_wrt_pred:
  assumes dep_funs: "((x : A) \<rightarrow>\<^sub>c B x) R" "((x : A') \<rightarrow>\<^sub>c B x) R'"
  and "\<And>x. A x \<Longrightarrow> A' x \<Longrightarrow> R`x = R'`x"
  shows "((x : A \<squnion> A') \<rightarrow>\<^sub>c B x) (R \<union> R')"
proof -
  from dep_funs have [simp]: "is_bin_rel R" "is_bin_rel R'" "is_bin_rel (R \<union> R')" by auto
  from assms show ?thesis by (urule crel_dep_mono_wrt_pred_sup_if_eval_eq_if_crel_dep_mono_wrt_pred)
qed

end

context
  fixes \<R> :: "set" and A :: "set \<Rightarrow> set" and D
  defines "D \<equiv> \<Union>R \<in> \<R>. A R"
begin

text \<open>TODO: this should be provable from
@{thm rel_dep_mono_wrt_pred_glue_if_right_unique_if_rel_dep_mono_wrt_pred} - but maybe requires
Hilbert-Choice?\<close>

lemma set_rel_dep_mono_wrt_set_glue_if_right_unique_if_set_rel_dep_mono_wrt_set:
  assumes funs: "\<And>R. R \<in> \<R> \<Longrightarrow> ((x : A R) \<rightarrow> B x) R"
  and runique: "right_unique_on D (glue \<R>)"
  shows "((x : D) \<rightarrow> B x) (glue \<R>)"
proof (urule (rr) rel_dep_mono_wrt_predI dep_mono_wrt_predI left_total_onI)
  note D_def[simp]
  fix x presume "x \<in> D"
  with funs obtain R where hyps: "R \<in> \<R>" "x \<in> A R" "((x : A R) \<rightarrow> B x) R" by auto
  then have "R`x \<in> B x" by auto
  moreover have "(glue \<R>)`x = R`x"
  proof (rule glue_set_eval_eqI)
    from hyps show "mem_of (A R) x" "R \<in> \<R>" by auto
    then have "A R \<subseteq> D" by fastforce
    with runique show "right_unique_on (mem_of (A R)) (glue \<R>)" by (blast dest: right_unique_onD)
  qed (use hyps in \<open>auto elim: rel_dep_mono_wrt_pred_relE\<close>)
  ultimately show "mem_of (B x) (rel (glue \<R>)`x)" by simp
qed (use assms in \<open>(fastforce simp: D_def mem_of_eq)+\<close>)

lemma crel_dep_mono_wrt_pred_glue_if_right_unique_if_crel_dep_mono_wrt_pred:
  assumes "\<And>R. R \<in> \<R> \<Longrightarrow> ((x : A R) \<rightarrow>\<^sub>c B x) R"
  and "right_unique_on D (glue \<R>)"
  shows "((x : D) \<rightarrow>\<^sub>c B x) (glue \<R>)"
  by (urule set_crel_dep_mono_wrt_pred_if_mem_of_dom_le_if_set_rel_dep_mono_wrt_pred,
  urule set_rel_dep_mono_wrt_set_glue_if_right_unique_if_set_rel_dep_mono_wrt_set)
  (use assms in \<open>auto simp: D_def mem_of_eq, fastforce\<close>)

end

end