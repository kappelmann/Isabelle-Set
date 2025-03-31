\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory TBinary_Relations_Functions
  imports
    TBinary_Relation_Functions
    TBinary_Relations_Left_Total
    TBinary_Relations_Right_Unique
    Transport.Binary_Relations_Function_Lambda
    Transport.Binary_Relations_Function_Composition
begin

definition "rel_dep_mono_wrt_type A B :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> (x : of_type A) \<rightarrow> of_type (B x)"
adhoc_overloading rel_dep_mono_wrt \<rightleftharpoons> rel_dep_mono_wrt_type
definition "rel_mono_wrt_type A B :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> of_type A \<rightarrow> of_type B"
adhoc_overloading rel_mono_wrt \<rightleftharpoons> rel_mono_wrt_type

lemma rel_dep_mono_wrt_type_eq_rel_dep_mono_wrt_pred [simp]:
  "((x : A) \<rightarrow> B x) = ((x : of_type A) \<rightarrow> of_type (B x))"
  unfolding rel_dep_mono_wrt_type_def by simp

lemma rel_dep_mono_wrt_type_eq_rel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> of_type A"
  and "\<And>x. Q x \<equiv> of_type (B x)"
  shows "((x : A) \<rightarrow> B x) \<equiv> ((x : P) \<rightarrow> Q x)"
  using assms by simp

lemma rel_dep_mono_wrt_type_iff_rel_dep_mono_wrt_pred [iff]:
  "((x : A) \<rightarrow> B x) R \<longleftrightarrow> ((x : of_type A) \<rightarrow> of_type (B x)) R"
  by simp

lemma rel_mono_wrt_type_eq_rel_mono_wrt_pred [simp]: "(A \<rightarrow> B) = (of_type A \<rightarrow> of_type B)"
  unfolding rel_mono_wrt_type_def by simp

lemma rel_mono_wrt_type_eq_rel_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> of_type A"
  and "Q \<equiv> of_type B"
  shows "(A \<rightarrow> B) \<equiv> (P \<rightarrow> Q)"
  using assms by simp

lemma rel_mono_wrt_type_iff_rel_mono_wrt_pred [iff]: "(A \<rightarrow> B) R \<longleftrightarrow> (of_type A \<rightarrow> of_type B) R"
  by simp

definition [typedef]: "Rel_dep_fun (A :: 'a type) B \<equiv> type ((x : A) \<rightarrow> B x)"
adhoc_overloading rel_dep_mono_wrt \<rightleftharpoons> Rel_dep_fun

lemma of_type_Rel_dep_fun_eq_rel_dep_mono_wrt_type [type_to_HOL_simp]:
  "of_type ((x : A) \<rightarrow> B x) = ((x : A) \<rightarrow> B x)"
  unfolding Rel_dep_fun_def type_to_HOL_simp by simp

soft_type_translation
  "((x : (A :: 'a type)) \<rightarrow> (B x :: 'b type)) R" \<rightleftharpoons> "R \<Ztypecolon> (x : A) \<rightarrow> B x"
  unfolding of_type_Rel_dep_fun_eq_rel_dep_mono_wrt_type[symmetric] by simp_all

definition [typedef]: "Rel_fun (A :: 'a type) B \<equiv> type (A \<rightarrow> B)"
adhoc_overloading rel_mono_wrt \<rightleftharpoons> Rel_fun

lemma of_type_Rel_fun_eq_rel_mono_wrt_type [type_to_HOL_simp]:
  "of_type (A \<rightarrow> B) = (A \<rightarrow> B)"
  unfolding Rel_fun_def type_to_HOL_simp by simp

soft_type_translation
  "((A :: 'a type) \<rightarrow> B) R" \<rightleftharpoons> "R \<Ztypecolon> A \<rightarrow> B"
  unfolding of_type_Rel_fun_eq_rel_mono_wrt_type[symmetric] by simp_all

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
begin

lemma Rel_dep_funI:
  assumes "left_total_on A R"
  and "right_unique_on A R"
  and "eval R \<Ztypecolon> (x : A) \<Rightarrow> B x"
  shows "R \<Ztypecolon> (x : A) \<rightarrow> B x"
  using assms by (urule rel_dep_mono_wrt_predI)

lemma Rel_dep_funE:
  assumes "R \<Ztypecolon> (x : A) \<rightarrow> B x"
  obtains "left_total_on A R" "right_unique_on A R" "eval R \<Ztypecolon> (x : A) \<Rightarrow> B x"
  using assms by (urule (e) rel_dep_mono_wrt_predE)

lemma eval_Dep_fun_if_Rel_dep_fun [derive]:
  assumes "R \<Ztypecolon> (x : A) \<rightarrow> B x"
  shows "eval R \<Ztypecolon> (x : A) \<Rightarrow> B x"
  using assms by (urule (e) Rel_dep_funE)

lemma Rel_dep_fun_cong [cong]:
  assumes "\<And>x. x \<Ztypecolon> A \<longleftrightarrow> x \<Ztypecolon> A'"
  and "\<And>x y. x \<Ztypecolon> A' \<Longrightarrow> y \<Ztypecolon> B x \<longleftrightarrow> y \<Ztypecolon> B' x"
  shows "(R \<Ztypecolon> (x : A) \<rightarrow> B x) \<longleftrightarrow> (R \<Ztypecolon> (x : A') \<rightarrow> B' x)"
  by (urule rel_dep_mono_wrt_pred_cong[THEN fun_cong]) (use assms in auto)

lemma Rel_fun_eq_Rel_dep_fun: "(A \<rightarrow> B) = Rel_dep_fun A (\<lambda>_. B)"
  supply rel_mono_wrt_pred_eq_rel_dep_mono_wrt_pred[simp] by (urule refl)

lemma Rel_fun_eq_Rel_dep_fun_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A \<rightarrow> B \<equiv> Rel_dep_fun A' B'"
  by (rule eq_reflection) (use assms Rel_fun_eq_Rel_dep_fun in simp)

lemma Rel_fun_iff_Rel_dep_fun: "(R \<Ztypecolon> A \<rightarrow> B) \<longleftrightarrow> R \<Ztypecolon> (_ : A) \<rightarrow> B"
  unfolding Rel_fun_eq_Rel_dep_fun by simp

lemma Rel_funI:
  assumes "left_total_on A R"
  and "right_unique_on A R"
  and "eval R \<Ztypecolon> A \<Rightarrow> B"
  shows "R \<Ztypecolon> A \<rightarrow> B"
  using assms by (urule rel_mono_wrt_predI)

lemma Rel_funE:
  assumes "R \<Ztypecolon> A \<rightarrow> B"
  obtains "left_total_on A R" "right_unique_on A R" "eval R \<Ztypecolon> A \<Rightarrow> B"
  using assms by (urule (e) rel_mono_wrt_predE)

lemma eval_Fun_if_Rel_fun [derive]:
  assumes "R \<Ztypecolon> A \<rightarrow> B"
  shows "eval R \<Ztypecolon> A \<Rightarrow> B"
  using assms by (urule (e) Rel_funE)

lemma eval_type [type]: "eval \<Ztypecolon> ((x : A) \<rightarrow> B x) \<Rightarrow> (x : A) \<Rightarrow> B x"
  by (urule mono_rel_dep_mono_wrt_pred_dep_mono_wrt_pred_eval)

lemma rel_restrict_left_Rel_dep_fun_type [type]:
  "rel_restrict_left \<Ztypecolon> ((x : A) \<rightarrow> B x) \<Rightarrow> (A' : Any) \<Rightarrow> ((x : A & A') \<rightarrow> B x)"
  supply dep_mono_wrt_type_eq_pred_map_dep_mono_wrt_pred_comp_type_if_iff[simp]
  by (urule mono_rel_dep_mono_wrt_pred_top_rel_dep_mono_wrt_pred_inf_rel_restrict_left)

end

definition "crel_dep_mono_wrt_type A B :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> (x : of_type A) \<rightarrow>\<^sub>c of_type (B x)"
adhoc_overloading crel_dep_mono_wrt \<rightleftharpoons> crel_dep_mono_wrt_type
definition "crel_mono_wrt_type A B :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> (of_type A) \<rightarrow>\<^sub>c of_type B"
adhoc_overloading crel_mono_wrt \<rightleftharpoons> crel_mono_wrt_type

lemma crel_dep_mono_wrt_type_eq_crel_dep_mono_wrt_pred [simp]:
  "((x : A) \<rightarrow>\<^sub>c B x) = ((x : of_type A) \<rightarrow>\<^sub>c of_type (B x))"
  unfolding crel_dep_mono_wrt_type_def by simp

lemma crel_dep_mono_wrt_type_eq_crel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> of_type A"
  and "\<And>x. Q x \<equiv> of_type (B x)"
  shows "(x : A) \<rightarrow>\<^sub>c B x \<equiv> (x : P) \<rightarrow>\<^sub>c Q x"
  using assms by simp

lemma crel_dep_mono_wrt_type_iff_crel_dep_mono_wrt_pred [iff]:
  "((x : A) \<rightarrow>\<^sub>c B x) R \<longleftrightarrow> ((x : of_type A) \<rightarrow>\<^sub>c of_type (B x)) R"
  by simp

lemma crel_mono_wrt_type_eq_crel_mono_wrt_pred [simp]: "(A \<rightarrow>\<^sub>c B) = (of_type A \<rightarrow>\<^sub>c of_type B)"
  unfolding crel_mono_wrt_type_def by simp

lemma crel_mono_wrt_type_eq_crel_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> of_type A"
  and "Q \<equiv> of_type B"
  shows "A \<rightarrow>\<^sub>c B \<equiv> P \<rightarrow>\<^sub>c Q"
  using assms by simp

lemma crel_mono_wrt_type_iff_crel_mono_wrt_pred [iff]: "(A \<rightarrow>\<^sub>c B) R \<longleftrightarrow> (of_type A \<rightarrow>\<^sub>c of_type B) R"
  by simp

definition [typedef]: "Crel_dep_fun (A :: 'a type) B \<equiv> type ((x : A) \<rightarrow>\<^sub>c B x)"
adhoc_overloading crel_dep_mono_wrt \<rightleftharpoons> Crel_dep_fun

lemma of_type_Crel_dep_fun_eq_crel_dep_mono_wrt_type [type_to_HOL_simp]:
  "of_type ((x : A) \<rightarrow>\<^sub>c B x) = ((x : A) \<rightarrow>\<^sub>c B x)"
  unfolding Crel_dep_fun_def type_to_HOL_simp by simp

soft_type_translation
  "((x : (A :: 'a type)) \<rightarrow>\<^sub>c (B x :: 'b type)) R" \<rightleftharpoons> "R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  unfolding of_type_Crel_dep_fun_eq_crel_dep_mono_wrt_type[symmetric] by simp_all

definition [typedef]: "Crel_fun (A :: 'a type) B \<equiv> type (A \<rightarrow>\<^sub>c B)"
adhoc_overloading crel_mono_wrt \<rightleftharpoons> Crel_fun

lemma of_type_Crel_fun_eq_crel_mono_wrt_type [type_to_HOL_simp]:
  "of_type (A \<rightarrow>\<^sub>c B) = (A \<rightarrow>\<^sub>c B)"
  unfolding Crel_fun_def type_to_HOL_simp by simp

soft_type_translation
  "((A :: 'a type) \<rightarrow>\<^sub>c B) R" \<rightleftharpoons> "R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  unfolding of_type_Crel_fun_eq_crel_mono_wrt_type[symmetric] by simp_all

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
begin

lemma Crel_dep_funI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "in_dom R \<le> of_type A"
  shows "R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  using assms by (urule crel_dep_mono_wrt_predI)

lemma Crel_dep_funE:
  assumes "R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  obtains "((x : A) \<rightarrow> B x) R" "in_dom R = of_type A"
  using assms by (urule (e) crel_dep_mono_wrt_predE)

lemma Rel_dep_fun_if_Crel_dep_fun [derive]:
  assumes "R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x"
  shows "R \<Ztypecolon> (x : A) \<rightarrow> B x"
  using assms by (urule (e) Crel_dep_funE)

lemma Crel_dep_fun_cong [cong]:
  assumes "\<And>x. x \<Ztypecolon> A \<longleftrightarrow> x \<Ztypecolon> A'"
  and "\<And>x y. x \<Ztypecolon> A' \<Longrightarrow> y \<Ztypecolon> B x \<longleftrightarrow> y \<Ztypecolon> B' x"
  shows "(R \<Ztypecolon> (x : A) \<rightarrow>\<^sub>c B x) \<longleftrightarrow> (R \<Ztypecolon> (x : A') \<rightarrow>\<^sub>c B' x)"
  by (urule crel_dep_mono_wrt_pred_cong[THEN fun_cong]) (use assms in auto)

lemma Crel_fun_eq_Crel_dep_fun: "(A \<rightarrow>\<^sub>c B) = Crel_dep_fun A (\<lambda>_. B)"
  supply crel_mono_wrt_pred_eq_crel_dep_mono_wrt_pred[simp] by (urule refl)

lemma Crel_fun_eq_Crel_dep_fun_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A \<rightarrow>\<^sub>c B \<equiv> Crel_dep_fun A' B'"
  by (rule eq_reflection) (use assms Crel_fun_eq_Crel_dep_fun in simp)

lemma Crel_fun_iff_Crel_dep_fun: "(R \<Ztypecolon> A \<rightarrow>\<^sub>c B) \<longleftrightarrow> R \<Ztypecolon> (_ : A) \<rightarrow>\<^sub>c B"
  unfolding Crel_fun_eq_Crel_dep_fun by simp

lemma Crel_funI:
  assumes "R \<Ztypecolon> A \<rightarrow> B"
  and "in_dom R \<le> of_type A"
  shows "R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  using assms by (urule crel_mono_wrt_predI)

lemma Crel_funE:
  assumes "R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  obtains "R \<Ztypecolon> A \<rightarrow> B" "in_dom R = of_type A"
  using assms by (urule (e) crel_mono_wrt_predE)

lemma Rel_fun_if_Crel_fun [derive]:
  assumes "R \<Ztypecolon> A \<rightarrow>\<^sub>c B"
  shows "R \<Ztypecolon> A \<rightarrow> B"
  using assms by (urule (e) Crel_funE)

lemma rel_comp_type [type]: "(\<circ>\<circ>) \<Ztypecolon> (A \<rightarrow>\<^sub>c B) \<Rightarrow> (B \<rightarrow> C) \<Rightarrow> A \<rightarrow>\<^sub>c C"
  by (urule mono_crel_mono_rel_mono_crel_mono_rel_comp)

lemma rel_restrict_left_Crel_dep_fun_type [type]:
  "rel_restrict_left \<Ztypecolon> ((x : A) \<rightarrow>\<^sub>c B x) \<Rightarrow> (A' : Any) \<Rightarrow> (x : A & A') \<rightarrow>\<^sub>c B x"
  supply dep_mono_wrt_type_eq_pred_map_dep_mono_wrt_pred_comp_type_if_iff[simp]
  by (urule mono_crel_dep_mono_wrt_pred_top_crel_dep_mono_wrt_pred_inf_rel_restrict_left)

end

definition "rel_lambda_type (T :: 'a type) :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool \<equiv> rel_lambda (of_type T)"
adhoc_overloading rel_lambda \<rightleftharpoons> rel_lambda_type

lemma rel_lambda_type_eq_rel_lambda_pred [simp]: "rel_lambda_type T = rel_lambda_pred (of_type T)"
  unfolding rel_lambda_type_def by simp

lemma rel_lambda_type_eq_rel_lambda_pred_uhint [uhint]:
  assumes "P = of_type T"
  shows "rel_lambda_type T \<equiv> rel_lambda_pred P"
  using assms by simp

lemma rel_lambda_type_iff_rel_lambda_pred [iff]: "(\<lambda>x : T. f x) x y \<longleftrightarrow> (\<lambda>x : of_type T. f x) x y"
  by (simp only: rel_lambda_type_eq_rel_lambda_pred)

lemma rel_lambda_type_type [type]: "rel_lambda \<Ztypecolon> ((A : Any) \<Rightarrow> ((x : A) \<Rightarrow> B x) \<Rightarrow> (x : A) \<rightarrow>\<^sub>c B x)"
  supply type_to_HOL_simp[simp] dep_mono_wrt_type_eq_pred_map_dep_mono_wrt_pred_comp_type_if_iff[simp]
  by (urule mono_dep_mono_wrt_pred_crel_dep_mono_wrt_pred_rel_lambda)

end
