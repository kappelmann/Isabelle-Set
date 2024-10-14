\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Functions on Relations\<close>
theory TSBinary_Relation_Functions
  imports
    HOTG.HOTG_Binary_Relations_Extend
    TSBinary_Relations_Base
begin

unbundle no HOL_ascii_syntax

lemma dom_type [type]: "dom \<Ztypecolon> ({\<Sum>}x : A. B x) \<Rightarrow> Collection A"
  by unfold_types fastforce

lemma codom_type [type]: "codom \<Ztypecolon> A {\<times>} B \<Rightarrow> Collection B"
  by unfold_types fastforce

lemma field_type [type]: "field \<Ztypecolon> A {\<times>} B \<Rightarrow> Collection (A \<bar> B)"
  by unfold_types fastforce

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
begin

lemma rel_comp_set_type [type]: "rel_comp_set \<Ztypecolon> A {\<times>} B \<Rightarrow> B {\<times>} C \<Rightarrow> A {\<times>} C"
  by (urule mono_bin_rel_bin_rel_bin_rel_rel_comp_set)

lemma rel_inv_set_type [type]: "rel_inv_set \<Ztypecolon> A {\<times>} B \<Rightarrow> B {\<times>} A"
  by (urule mono_bin_rel_rel_inv_set)

definition "set_rel_restrict_left_type (R :: set) (T :: set type) \<equiv>
  rel_restrict_left R (of_type T)"
adhoc_overloading rel_restrict_left set_rel_restrict_left_type

lemma set_rel_restrict_left_type_eq_set_rel_restrict_left_pred [simp]:
  "(R :: set)\<restriction>\<^bsub>T :: set type\<^esub> = R\<restriction>\<^bsub>of_type T\<^esub>"
  unfolding set_rel_restrict_left_type_def by simp

lemma set_rel_restrict_left_type_eq_set_rel_restrict_left_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "(R :: set)\<restriction>\<^bsub>T :: set type\<^esub> \<equiv> R\<restriction>\<^bsub>P\<^esub>"
  using assms by simp

lemma mono_pred_map_comp_type_set_rel_restrict_left_eq_mono_rel_restrict_left_pred [simp, type_to_HOL_simp]:
  "((x : A) \<Rightarrow> pred_map (\<lambda>f. f \<circ> type) ((y : B x) \<Rightarrow> C x y)) rel_restrict_left
  = ((x : A) \<Rightarrow> (y : (B x :: _ \<Rightarrow> bool)) \<Rightarrow> C x y) rel_restrict_left"
  by (simp cong: dep_mono_wrt_pred_codom_iff_cong)

definition "set_rel_restrict_right_type (R :: set) (T :: set type) \<equiv>
  rel_restrict_right R (of_type T)"
adhoc_overloading rel_restrict_right set_rel_restrict_right_type

lemma set_rel_restrict_right_type_eq_set_rel_restrict_right_pred [simp]:
  "(R :: set)\<upharpoonleft>\<^bsub>T :: set type\<^esub> = R\<upharpoonleft>\<^bsub>of_type T\<^esub>"
  unfolding set_rel_restrict_right_type_def by simp

lemma set_rel_restrict_right_type_eq_set_rel_restrict_right_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "(R :: set)\<upharpoonleft>\<^bsub>T :: set type\<^esub> \<equiv> R\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms by simp

lemma mono_pred_map_comp_type_set_rel_restrict_right_eq_mono_rel_restrict_right_pred [simp, type_to_HOL_simp]:
  "((x : A) \<Rightarrow> pred_map (\<lambda>f. f \<circ> type) ((y : B x) \<Rightarrow> C x y)) rel_restrict_right
  = ((x : A) \<Rightarrow> (y : (B x :: _ \<Rightarrow> bool)) \<Rightarrow> C x y) rel_restrict_right"
  by (simp cong: dep_mono_wrt_pred_codom_iff_cong)

definition "set_rel_restrict_type (R :: set) (T :: set type) \<equiv> rel_restrict R (of_type T)"
adhoc_overloading rel_restrict set_rel_restrict_type

lemma set_rel_restrict_type_eq_set_rel_restrict_pred [simp]:
  "(R :: set)\<up>\<^bsub>T :: set type\<^esub> = R\<up>\<^bsub>of_type T\<^esub>"
  unfolding set_rel_restrict_type_def by simp

lemma set_rel_restrict_type_eq_set_rel_restrict_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "(R :: set)\<up>\<^bsub>T :: set type\<^esub> \<equiv> R\<up>\<^bsub>P\<^esub>"
  using assms by simp

lemma mono_pred_map_comp_type_set_rel_restrict_eq_mono_rel_restrict_pred [simp, type_to_HOL_simp]:
  "((x : A) \<Rightarrow> pred_map (\<lambda>f. f \<circ> type) ((y : B x) \<Rightarrow> C x y)) rel_restrict
  = ((x : A) \<Rightarrow> (y : (B x :: _ \<Rightarrow> bool)) \<Rightarrow> C x y) rel_restrict"
  by (simp cong: dep_mono_wrt_pred_codom_iff_cong)

context
  notes dep_mono_wrt_type_eq_pred_map_dep_mono_wrt_pred_comp_type_if_iff[simp]
begin

lemma rel_restrict_left_Set_dep_bin_rel_type [type]:
  "rel_restrict_left \<Ztypecolon> ({\<Sum>}x : A. B x) \<Rightarrow> (A' : Any) \<Rightarrow> {\<Sum>}x : A & A'. B x"
  by (urule mono_dep_bin_rel_top_dep_bin_rel_inf_set_rel_restrict_left)

lemma rel_restrict_right_Dep_bin_rel_type [type]:
  "rel_restrict_right \<Ztypecolon> ({\<Sum>}x : A. B x) \<Rightarrow> (B' : Any) \<Rightarrow> ({\<Sum>}x : A. B x & B')"
  by (urule mono_dep_bin_rel_top_dep_bin_rel_inf_set_rel_restrict_right)

lemma rel_restrict_Dep_bin_rel_type [type]:
  "rel_restrict \<Ztypecolon> ({\<Sum>}x : A. B x) \<Rightarrow> (C : Any) \<Rightarrow> ({\<Sum>}x : A & C. B x & C)"
  by (urule mono_dep_bin_rel_top_dep_bin_rel_inf_set_rel_restrict)

lemma extend_set_type [type]:
  "extend_set \<Ztypecolon> (x : A) \<Rightarrow> B x \<Rightarrow> ({\<Sum>}x : A'. B' x) \<Rightarrow> ({\<Sum>}x : A \<bar> A'. (B x \<bar> B' x))"
  by (urule dep_mono_set_dep_bin_rel_extend)

end

end

end