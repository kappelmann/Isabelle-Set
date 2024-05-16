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

context
  fixes \<R> :: "set" and A :: "set \<Rightarrow> set" and D
  defines "D \<equiv> \<Union>R \<in> \<R>. A R"
begin

lemma rel_dep_mono_wrt_pred_glue_if_right_unique_if_rel_dep_mono_wrt_pred:
  assumes funs: "\<And>R. R \<in> \<R> \<Longrightarrow> ((x : A R) \<rightarrow> B x) R"
  and runique: "right_unique_on D (glue \<R>)"
  shows "((x : D) \<rightarrow> B x) (glue \<R>)"
  (*TODO*)
  sorry
(* unfolding
set_rel_dep_mono_wrt_set_eq_set_rel_dep_mono_wrt_pred
set_rel_dep_mono_wrt_pred_iff_rel_dep_mono_wrt_pred
rel_glue_eq_glue_has_inverse_on_rel *)
(* proof -
  (* have bla: "mem_of (\<Union>R \<in> \<R>. A R) = in_codom_on (has_inverse_on \<R> rel) *)
    (* (\<lambda>R. mem_of (A (THE R'. rel R' = R)))" sorry *)

  show ?thesis
    unfolding rel_glue_eq_glue_has_inverse_on_rel[simp] D_def[simp]
      mem_of_idx_union_eq_in_codom_on_has_inverse_on_if_mem_of_eq_app_rel[of dom in_dom, simp]
      (* thm rel_dep_mono_wrt_pred_glue_if_right_unique_if_rel_dep_mono_wrt_pred[where ?A=A] *)
set_rel_dep_mono_wrt_set_eq_set_rel_dep_mono_wrt_pred
set_rel_dep_mono_wrt_pred_iff_rel_dep_mono_wrt_pred
rel_glue_eq_glue_has_inverse_on_rel
bla
    apply (rule rel_dep_mono_wrt_pred_glue_if_right_unique_if_rel_dep_mono_wrt_pred)
    apply (use assms in auto)
qed *)

(* lemma crel_dep_mono_wrt_pred_glue_if_right_unique_if_crel_dep_mono_wrt_pred:
  assumes "\<And>R. \<R> R \<Longrightarrow> ((x : A R) \<rightarrow>\<^sub>c B x) R"
  and "right_unique_on D (glue \<R>)"
  shows "((x : D) \<rightarrow>\<^sub>c B x) (glue \<R>)"
  using assms by (intro crel_dep_mono_wrt_predI rel_dep_mono_wrt_pred_glue_if_right_unique_if_rel_dep_mono_wrt_pred) fastforce+ *)
end

lemma set_crel_dep_mono_wrt_pred_sup_bin_union_if_eval_eq_if_set_crel_dep_mono_wrt_pred:
  assumes dep_funs: "((x : A) \<rightarrow>\<^sub>c B x) R" "((x : A') \<rightarrow>\<^sub>c B x) R'"
  and "\<And>x. A x \<Longrightarrow> A' x \<Longrightarrow> R`x = R'`x"
  shows "((x : A \<squnion> A') \<rightarrow>\<^sub>c B x) (R \<union> R')"
proof -
  from dep_funs have [simp]: "is_bin_rel R" "is_bin_rel R'" "is_bin_rel (R \<union> R')" by auto
  from assms show ?thesis by (urule crel_dep_mono_wrt_pred_sup_if_eval_eq_if_crel_dep_mono_wrt_pred)
qed

end

end