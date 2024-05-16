\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Composition\<close>
theory HOTG_Functions_Composition
  imports
    HOTG_Clean_Functions
    Transport.Binary_Relations_Function_Composition
    ML_Unification.Unification_Attributes
begin

definition "comp_set (f :: set) (g :: set) \<equiv> g \<circ>\<circ> f"
adhoc_overloading comp comp_set

lemma comp_set_eq_rel_comp_set [simp]: "(f :: set) \<circ> g = g \<circ>\<circ> f"
  unfolding comp_set_def by simp

lemma comp_set_eq_rel_comp_set_uhint [uhint]:
  assumes "f :: set \<equiv> f'"
  and "g \<equiv> g'"
  shows "f \<circ> g \<equiv> g' \<circ>\<circ> f'"
  using assms by simp

context
  notes set_to_HOL_simp[simp, symmetric, simp del]
begin

lemma set_dep_bin_rel_eval_rel_comp_if_set_dep_bin_rel_if_set_crel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) (R :: set)"
  and "\<And>x. A x \<Longrightarrow> ({\<Sum>}y : B x. C x y) R'"
  shows "({\<Sum>}x : A. C x (R`x)) (R \<circ>\<circ> R')"
  by (urule dep_bin_rel_eval_rel_comp_if_dep_bin_rel_if_crel_dep_mono_wrt_pred) (use assms in auto)

lemma set_crel_dep_mono_wrt_pred_eval_comp_if_set_rel_dep_mono_wrt_pred_if_set_crel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) (R :: set)"
  and "\<And>x. A x \<Longrightarrow> ((y : B x) \<rightarrow> C x y) R'"
  shows "((x : A) \<rightarrow>\<^sub>c C x (R`x)) (R' \<circ> R)"
  by (urule crel_dep_mono_wrt_pred_eval_rel_comp_if_rel_dep_mono_wrt_pred_if_crel_dep_mono_wrt_pred)
  (use assms in auto)

lemma comp_set_eval_eq_if_set_rel_dep_mono_wrt_pred_if_set_crel_dep_mono_wrt_predI [simp]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) (R :: set)"
  and "\<And>x. A x \<Longrightarrow> ((y : B x) \<rightarrow> C x y) R'"
  and "A x"
  shows "(R' \<circ> R)`x = R'`(R`x)"
  by (urule rel_comp_eval_eq_if_rel_dep_mono_wrt_pred_if_crel_dep_mono_wrt_predI)
  (use assms in blast)+

lemma comp_set_id_eq_if_set_crel_dep_mono_wrt_set [simp]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "R \<circ> set_id A = R"
  supply is_bin_rel_if_set_crel_dep_mono_wrt_pred[uOF assms, simp]
  using assms by (urule eq_restrict_comp_eq_if_crel_dep_mono_wrt_pred)

lemma set_id_comp_eq_if_set_crel_dep_mono_wrt_set [simp]:
  assumes "(A \<rightarrow>\<^sub>c B) R"
  shows "set_id B \<circ> R = R"
  supply is_bin_rel_if_set_crel_dep_mono_wrt_pred[uOF assms, simp]
  using assms by (urule comp_eq_restrict_if_crel_dep_mono_wrt_pred)

end

end