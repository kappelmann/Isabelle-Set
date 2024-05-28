\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Functions on Relations\<close>
theory TBinary_Relation_Functions
  imports
    Transport.Binary_Relations_Extend
    TDependent_Binary_Relations
begin

unbundle no_HOL_ascii_syntax

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
begin

lemma rel_comp_type [type]: "(\<circ>\<circ>) \<Ztypecolon> A {\<times>} B \<Rightarrow> B {\<times>} C \<Rightarrow> A {\<times>} C"
  by (urule mono_bin_rel_bin_rel_bin_rel_rel_comp)

lemma rel_inv_type [type]: "rel_inv \<Ztypecolon> A {\<times>} B \<Rightarrow> B {\<times>} A"
  by (urule mono_bin_rel_rel_inv)

definition "rel_restrict_left_type (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (T :: 'a type) \<equiv>
  rel_restrict_left R (of_type T)"
adhoc_overloading rel_restrict_left rel_restrict_left_type

definition "rel_restrict_right_type (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (T :: 'b type) \<equiv>
  rel_restrict_right R (of_type T)"
adhoc_overloading rel_restrict_right rel_restrict_right_type

lemma rel_restrict_left_type_eq_rel_restrict_left_pred [simp]:
  "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>T :: 'a type\<^esub> = R\<restriction>\<^bsub>of_type T\<^esub>"
  unfolding rel_restrict_left_type_def by simp

lemma rel_restrict_left_type_eq_rel_restrict_left_pred_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "P \<equiv> of_type T"
  shows "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>T :: 'a type\<^esub> \<equiv> R'\<restriction>\<^bsub>P\<^esub>"
  using assms by simp

lemma rel_restrict_right_type_eq_rel_restrict_right_pred [simp]:
  "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<upharpoonleft>\<^bsub>T :: 'b type\<^esub> = R\<upharpoonleft>\<^bsub>of_type T\<^esub>"
  unfolding rel_restrict_right_type_def by simp

lemma rel_restrict_right_type_eq_rel_restrict_right_pred_uhint [uhint]:
  assumes "R \<equiv> R'"
  and "P \<equiv> of_type T"
  shows "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<upharpoonleft>\<^bsub>T :: 'b type\<^esub> \<equiv> R'\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms by simp

context
  notes dep_mono_wrt_type_eq_pred_map_dep_mono_wrt_pred_comp_type_if_iff[simp]
begin

lemma rel_restrict_left_Dep_bin_rel_type [type]:
  "rel_restrict_left \<Ztypecolon> ({\<Sum>}x : A. B x) \<Rightarrow> (A' : Any) \<Rightarrow> {\<Sum>}x : A & A'. B x"
  by (urule mono_dep_bin_rel_top_dep_bin_rel_inf_rel_restrict_left)

lemma rel_restrict_right_Dep_bin_rel_type [type]:
  "rel_restrict_right \<Ztypecolon> ({\<Sum>}x : A. B x) \<Rightarrow> (B' : Any) \<Rightarrow> ({\<Sum>}x : A. B x & B')"
  by (urule mono_dep_bin_rel_top_dep_bin_rel_inf_rel_restrict_right)

end

lemma extend_type [type]:
  "extend \<Ztypecolon> (x : A) \<Rightarrow> B x \<Rightarrow> ({\<Sum>}x : A'. B' x) \<Rightarrow> ({\<Sum>}x : A \<bar> A'. (B x \<bar> B' x))"
  by (urule dep_mono_dep_bin_rel_extend)

end

end
