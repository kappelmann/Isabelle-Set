\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Functions\<close>
theory TSFunctions_Base
  imports
    Soft_Types.TBinary_Relations_Functions
    TSBinary_Relation_Functions
begin

definition "set_rel_dep_mono_wrt_type A B :: set \<Rightarrow> bool \<equiv> (x : of_type A) \<rightarrow> of_type (B x)"
adhoc_overloading rel_dep_mono_wrt \<rightleftharpoons> set_rel_dep_mono_wrt_type
definition "set_rel_mono_wrt_type A B :: set \<Rightarrow> bool \<equiv> of_type A \<rightarrow> of_type B"
adhoc_overloading rel_mono_wrt \<rightleftharpoons> set_rel_mono_wrt_type

lemma set_rel_dep_mono_wrt_type_eq_set_rel_dep_mono_wrt_pred [simp]:
  "((x : A) \<rightarrow> B x :: set \<Rightarrow> bool) = ((x : of_type A) \<rightarrow> of_type (B x))"
  unfolding set_rel_dep_mono_wrt_type_def by simp

lemma set_rel_dep_mono_wrt_type_eq_set_rel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> of_type A"
  and "\<And>x. Q x \<equiv> of_type (B x)"
  shows "(x : A) \<rightarrow> B x :: set \<Rightarrow> bool \<equiv> (x : P) \<rightarrow> Q x"
  using assms by simp

lemma set_rel_dep_mono_wrt_type_iff_set_rel_dep_mono_wrt_pred [iff]:
  "((x : A) \<rightarrow> B x) (R :: set) \<longleftrightarrow> ((x : of_type A) \<rightarrow> of_type (B x)) R"
  by simp

lemma set_rel_mono_wrt_type_eq_set_rel_mono_wrt_pred [simp]:
  "(A \<rightarrow> B :: set \<Rightarrow> bool) = (of_type A \<rightarrow> of_type B)"
  unfolding set_rel_mono_wrt_type_def by simp

lemma set_rel_mono_wrt_type_eq_set_rel_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> of_type A"
  and "Q \<equiv> of_type B"
  shows "A \<rightarrow> B :: set \<Rightarrow> bool \<equiv> P \<rightarrow> Q"
  using assms by simp

lemma set_rel_mono_wrt_type_iff_set_rel_mono_wrt_pred [iff]:
  "(A \<rightarrow> B) (R :: set) \<longleftrightarrow> (of_type A \<rightarrow> of_type B) R"
  by simp

definition [typedef]: "Set_rel_dep_fun (A :: set type) B \<equiv> type ((x : A) \<rightarrow> B x :: set \<Rightarrow> bool)"
adhoc_overloading rel_dep_mono_wrt \<rightleftharpoons> Set_rel_dep_fun

lemma of_type_Set_rel_dep_fun_eq_set_rel_dep_mono_wrt_type [type_to_HOL_simp]:
  "of_type ((x : A) \<rightarrow> B x :: set type) = ((x : A) \<rightarrow> B x)"
  unfolding Set_rel_dep_fun_def type_to_HOL_simp by simp

soft_type_translation
  "((x : (A :: set type)) \<rightarrow> B x) (R :: set)" \<rightleftharpoons> "(R :: set) \<Ztypecolon> (x : A) \<rightarrow> B x"
  unfolding of_type_Set_rel_dep_fun_eq_set_rel_dep_mono_wrt_type[symmetric] by simp_all

definition [typedef]: "Set_rel_fun (A :: set type) B \<equiv> type (A \<rightarrow> B :: set \<Rightarrow> bool)"
adhoc_overloading rel_mono_wrt \<rightleftharpoons> Set_rel_fun

lemma of_type_Set_rel_fun_eq_set_rel_mono_wrt_type [type_to_HOL_simp]:
  "of_type (A \<rightarrow> B :: set type) = (A \<rightarrow> B)"
  unfolding Set_rel_fun_def type_to_HOL_simp by simp

soft_type_translation
  "((A :: set type) \<rightarrow> B) (R :: set)" \<rightleftharpoons> "(R :: set) \<Ztypecolon> A \<rightarrow> B"
  unfolding of_type_Set_rel_fun_eq_set_rel_mono_wrt_type[symmetric] by simp_all

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
begin

lemma Set_rel_dep_fun_iff_rel_Rel_dep_fun:
  "R \<Ztypecolon> (x : A) \<rightarrow> B x \<longleftrightarrow> rel R \<Ztypecolon> (x : A) \<rightarrow> B x"
  by (urule set_rel_dep_mono_wrt_pred_iff_rel_dep_mono_wrt_pred)

lemma rel_Rel_dep_fun_if_Set_rel_dep_fun [derive]:
  assumes "R \<Ztypecolon> (x : A) \<rightarrow> B x"
  shows "rel R \<Ztypecolon> (x : A) \<rightarrow> B x"
  using assms Set_rel_dep_fun_iff_rel_Rel_dep_fun by blast

lemma Set_rel_dep_fun_cong [cong]:
  assumes "\<And>x. x \<Ztypecolon> A \<longleftrightarrow> x \<Ztypecolon> A'"
  and "\<And>x y. x \<Ztypecolon> A' \<Longrightarrow> y \<Ztypecolon> B x \<longleftrightarrow> y \<Ztypecolon> B' x"
  shows "((R :: set) \<Ztypecolon> (x : A) \<rightarrow> B x) \<longleftrightarrow> (R \<Ztypecolon> (x : A') \<rightarrow> B' x)"
  by (urule rel_dep_mono_wrt_pred_cong[THEN fun_cong]) (use assms in auto)

lemma Set_rel_fun_eq_Set_rel_dep_fun: "(A \<rightarrow> B) = Set_rel_dep_fun A (\<lambda>_. B)"
  supply set_rel_mono_wrt_pred_eq_set_rel_dep_mono_wrt_pred[simp] by (urule refl)

lemma Set_rel_fun_eq_Set_rel_dep_fun_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A \<rightarrow> B \<equiv> Set_rel_dep_fun A' B'"
  by (rule eq_reflection) (use assms Set_rel_fun_eq_Set_rel_dep_fun in simp)

lemma Set_rel_fun_iff_Set_rel_dep_fun: "((R :: set) \<Ztypecolon> A \<rightarrow> B) \<longleftrightarrow> R \<Ztypecolon> (_ : A) \<rightarrow> B"
  unfolding Set_rel_fun_eq_Set_rel_dep_fun by simp
declare
  Set_rel_fun_iff_Set_rel_dep_fun[THEN iffD1, derive]
  Set_rel_fun_iff_Set_rel_dep_fun[THEN iffD2, derive]

lemma Set_rel_fun_iff_rel_Rel_fun: "R \<Ztypecolon> A \<rightarrow> B \<longleftrightarrow> rel R \<Ztypecolon> A \<rightarrow> B"
  by (urule set_rel_mono_wrt_pred_iff_rel_mono_wrt_pred)

lemma rel_Rel_fun_if_Set_rel_fun [derive]:
  assumes "R \<Ztypecolon> A \<rightarrow> B"
  shows "rel R \<Ztypecolon> A \<rightarrow> B"
  using assms Set_rel_fun_iff_rel_Rel_fun by blast

lemma eval_set_type [type]:
  "eval_set \<Ztypecolon> ((x : A) \<rightarrow> B x) \<Rightarrow> (x : A) \<Rightarrow> B x"
  by (urule mono_set_rel_dep_mono_wrt_pred_dep_mono_wrt_pred_eval_set)

lemma set_rel_restrict_left_Set_rel_dep_fun_type [type]:
  "set_rel_restrict_left_type \<Ztypecolon> ((x : A) \<rightarrow> B x) \<Rightarrow> (A' : Any) \<Rightarrow> ((x : A & A') \<rightarrow> B x)"
  supply dep_mono_wrt_type_eq_pred_map_dep_mono_wrt_pred_comp_type_if_iff[simp]
  by (urule mono_set_rel_dep_mono_wrt_pred_top_set_rel_dep_mono_wrt_pred_inf_set_rel_restrict_left)

end

end