\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Clean Functions\<close>
theory TSClean_Functions
  imports
    HOTG.HOTG_Functions_Composition
    HOTG.HOTG_Functions_Lambda
    TSFunctions_Base
begin

definition "set_crel_dep_mono_wrt_type A B :: set \<Rightarrow> bool \<equiv> (x : of_type A) \<rightarrow>\<^sub>c of_type (B x)"
adhoc_overloading crel_dep_mono_wrt set_crel_dep_mono_wrt_type
definition "set_crel_mono_wrt_type A B :: set \<Rightarrow> bool \<equiv> of_type A \<rightarrow>\<^sub>c of_type B"
adhoc_overloading crel_mono_wrt set_crel_mono_wrt_type

lemma set_crel_dep_mono_wrt_type_eq_set_crel_dep_mono_wrt_pred [simp]:
  "((x : A) \<rightarrow>\<^sub>c B x :: set \<Rightarrow> bool) = ((x : of_type A) \<rightarrow>\<^sub>c of_type (B x))"
  unfolding set_crel_dep_mono_wrt_type_def by simp

lemma set_crel_dep_mono_wrt_type_eq_set_crel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> of_type A"
  and "\<And>x. Q x \<equiv> of_type (B x)"
  shows "(x : A) \<rightarrow>\<^sub>c B x :: set \<Rightarrow> bool \<equiv> (x : P) \<rightarrow>\<^sub>c Q x"
  using assms by simp

lemma set_crel_dep_mono_wrt_type_iff_set_crel_dep_mono_wrt_pred [iff]:
  "((x : A) \<rightarrow>\<^sub>c B x) (R :: set) \<longleftrightarrow> ((x : of_type A) \<rightarrow>\<^sub>c of_type (B x)) R"
  by simp

lemma set_crel_mono_wrt_type_eq_set_crel_mono_wrt_pred [simp]:
  "(A \<rightarrow>\<^sub>c B :: set \<Rightarrow> bool) = (of_type A \<rightarrow>\<^sub>c of_type B)"
  unfolding set_crel_mono_wrt_type_def by simp

lemma set_crel_mono_wrt_type_eq_set_crel_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> of_type A"
  and "Q \<equiv> of_type B"
  shows "A \<rightarrow>\<^sub>c B :: set \<Rightarrow> bool \<equiv> P \<rightarrow>\<^sub>c Q"
  using assms by simp

lemma set_crel_mono_wrt_type_iff_set_crel_mono_wrt_pred [iff]:
  "(A \<rightarrow>\<^sub>c B) (R :: set) \<longleftrightarrow> (of_type A \<rightarrow>\<^sub>c of_type B) R"
  by simp

definition [typedef]: "Set_crel_dep_fun (A :: set type) B \<equiv> type ((x : A) \<rightarrow>\<^sub>c B x :: set \<Rightarrow> bool)"
adhoc_overloading crel_dep_mono_wrt Set_crel_dep_fun

lemma of_type_Set_crel_dep_fun_eq_set_crel_dep_mono_wrt_type [type_to_HOL_simp]:
  "of_type ((x : A) \<rightarrow>\<^sub>c B x :: set type) = ((x : A) \<rightarrow>\<^sub>c B x)"
  unfolding Set_crel_dep_fun_def type_to_HOL_simp by simp

soft_type_translation
  "((x : (A :: set type)) \<rightarrow>\<^sub>c B x) (R :: set)" \<rightleftharpoons> "(R :: set) \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  unfolding of_type_Set_crel_dep_fun_eq_set_crel_dep_mono_wrt_type[symmetric] by simp_all

lemma mem_of_crel_dep_fun_eq_of_type_Set_crel_dep_fun_Element:
  "mem_of ((x : A) \<rightarrow>\<^sub>c B x) = of_type ((x : Element A) \<rightarrow>\<^sub>c Element (B x))"
  using type_to_HOL_simp by simp

soft_type_translation
  "R \<in> ((x : A) \<rightarrow>\<^sub>c B x)" \<rightleftharpoons> "(R :: set) \<Ztypecolon> (x : Element A) \<rightarrow>\<^sub>c Element (B x)"
  using mem_of_crel_dep_fun_eq_of_type_Set_crel_dep_fun_Element by simp_all

definition [typedef]: "Set_crel_fun (A :: set type) B \<equiv> type (A \<rightarrow>\<^sub>c B :: set \<Rightarrow> bool)"
adhoc_overloading crel_mono_wrt Set_crel_fun

lemma of_type_Set_crel_fun_eq_set_crel_mono_wrt_type [type_to_HOL_simp]:
  "of_type (A \<rightarrow>\<^sub>c B :: set type) = (A \<rightarrow>\<^sub>c B)"
  unfolding Set_crel_fun_def type_to_HOL_simp by simp

soft_type_translation
  "((A :: set type) \<rightarrow>\<^sub>c B) (R :: set)" \<rightleftharpoons> "(R :: set) \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  unfolding of_type_Set_crel_fun_eq_set_crel_mono_wrt_type[symmetric] by simp_all

lemma mem_of_crel_fun_eq_of_type_Set_crel_fun_Element:
  "mem_of (A \<rightarrow>\<^sub>c B) = of_type (Element A \<rightarrow>\<^sub>c Element B)"
  using type_to_HOL_simp by simp

soft_type_translation
  "R \<in> (A \<rightarrow>\<^sub>c B)" \<rightleftharpoons> "(R :: set) \<Ztypecolon> Element A \<rightarrow>\<^sub>c Element B"
  using mem_of_crel_fun_eq_of_type_Set_crel_fun_Element by simp_all

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
begin

lemma Set_crel_dep_funI:
  assumes "rel R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  and "is_bin_rel R"
  shows "R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  using assms by (urule set_crel_dep_mono_wrt_predI)

lemma Set_crel_dep_funE:
  assumes "R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  obtains "rel R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x" "is_bin_rel R"
  using assms by (urule (e) set_crel_dep_mono_wrt_predE)

lemma Set_crel_dep_funE':
  assumes "R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  obtains "rel R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x" "R \<Ztypecolon> {\<Sum>}x : A. B x"
  using assms by (urule (e) set_crel_dep_mono_wrt_predE')

lemma rel_Crel_dep_fun_if_Set_crel_dep_fun [derive]:
  assumes "R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  shows "rel R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  using assms by (urule (e) Set_crel_dep_funE)

lemma Set_dep_bin_rel_if_Set_crel_dep_fun [derive]:
  assumes "R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  shows "(R :: set) \<Ztypecolon> {\<Sum>}x : A. B x"
  using assms by (urule (e) Set_crel_dep_funE')

lemma Set_rel_dep_fun_if_Set_crel_dep_fun [derive]:
  assumes "(R :: set) \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  shows "R \<Ztypecolon> (x : A) \<rightarrow> B x"
  using assms by (urule set_rel_dep_mono_wrt_pred_if_set_crel_dep_mono_wrt_pred)

lemma Set_crel_dep_fun_cong [cong]:
  assumes "\<And>x. x \<Ztypecolon> A \<longleftrightarrow> x \<Ztypecolon> A'"
  and "\<And>x y. x \<Ztypecolon> A' \<Longrightarrow> y \<Ztypecolon> B x \<longleftrightarrow> y \<Ztypecolon> B' x"
  shows "((R :: set) \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x) \<longleftrightarrow> (R \<Ztypecolon> (x : A') \<rightarrow>\<^sub>c B' x)"
  by (urule set_crel_dep_mono_wrt_pred_cong[THEN fun_cong]) (use assms in auto)

lemma Set_crel_fun_eq_Set_crel_dep_fun: "(A \<rightarrow>\<^sub>c B) = Set_crel_dep_fun A (\<lambda>_. B)"
  supply set_crel_mono_wrt_pred_eq_set_crel_dep_mono_wrt_pred[simp] by (urule refl)

lemma Set_crel_fun_eq_Set_crel_dep_fun_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A \<rightarrow>\<^sub>c B \<equiv> Set_crel_dep_fun A' B'"
  by (rule eq_reflection) (use assms Set_crel_fun_eq_Set_crel_dep_fun in simp)

lemma Set_crel_fun_iff_Set_crel_dep_fun: "((R :: set) \<Ztypecolon> A \<rightarrow>\<^sub>c B) \<longleftrightarrow> R \<Ztypecolon> (_ : A) \<rightarrow>\<^sub>c B"
  unfolding Set_crel_fun_eq_Set_crel_dep_fun by simp

lemma Set_crel_funI:
  assumes "rel R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  and "is_bin_rel R"
  shows "R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  using assms by (urule set_crel_mono_wrt_predI)

lemma Set_crel_funE:
  assumes "R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  obtains "rel R \<Ztypecolon> A \<rightarrow>\<^sub>c B" "is_bin_rel R"
  using assms by (urule (e) set_crel_mono_wrt_predE)

lemma Set_crel_funE':
  assumes "R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  obtains "rel R \<Ztypecolon> A \<rightarrow>\<^sub>c B" "R \<Ztypecolon> A {\<times>} B"
  using assms by (urule (e) set_crel_mono_wrt_predE')

lemma rel_Crel_fun_if_Set_crel_fun [derive]:
  assumes "R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  shows "rel R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  using assms by (urule (e) Set_crel_funE)

lemma Set_bin_rel_if_Set_crel_fun [derive]:
  assumes "R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  shows  "(R :: set) \<Ztypecolon> A {\<times>} B"
  using assms by (urule (e) Set_crel_funE')

lemma Set_rel_fun_if_Set_crel_fun [derive]:
  assumes "(R :: set) \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  shows "R \<Ztypecolon> A \<rightarrow> B"
  using assms by (urule set_rel_dep_mono_wrt_pred_if_set_crel_dep_mono_wrt_pred)

lemma set_id_type [type]: "set_id \<Ztypecolon> (A : Set) \<Rightarrow> (Element A \<rightarrow>\<^sub>c Element A)"
  by (urule mono_set_crel_mono_set_id)

lemma comp_set_type [type]: "comp_set \<Ztypecolon> (B \<rightarrow> C) \<Rightarrow> (A \<rightarrow>\<^sub>c B) \<Rightarrow> A \<rightarrow>\<^sub>c C"
  by (urule mono_set_crel_mono_set_rel_mono_set_crel_mono_comp)

lemma set_rel_restrict_left_Set_rel_dep_fun_type [type]:
  "set_rel_restrict_left_type \<Ztypecolon> ((x : A) \<rightarrow>\<^sub>c B x) \<Rightarrow> (A' : Any) \<Rightarrow> ((x : A & A') \<rightarrow>\<^sub>c B x)"
  supply dep_mono_wrt_type_eq_pred_map_dep_mono_wrt_pred_comp_type_if_iff[simp]
  by (urule mono_set_crel_dep_mono_wrt_pred_top_set_crel_dep_mono_wrt_pred_inf_rel_restrict_left)

lemma set_rel_lambda_set_type [type]:
  "set_rel_lambda_set \<Ztypecolon> ((A : Set) \<Rightarrow> ((x : Element A) \<Rightarrow> Element (B x)) \<Rightarrow> (x : Element A) \<rightarrow>\<^sub>c Element (B x))"
  by (urule mono_dep_mono_wrt_set_crel_dep_mono_wrt_set_rel_lambda)

end

end