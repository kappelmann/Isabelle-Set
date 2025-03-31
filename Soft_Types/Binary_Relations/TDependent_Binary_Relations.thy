\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Binary Relations\<close>
theory TDependent_Binary_Relations
  imports
    Soft_Types_HOL
    Transport.Dependent_Binary_Relations
begin

definition "dep_bin_rel_type A B \<equiv> {\<Sum>}x : of_type A. of_type (B x)"
adhoc_overloading dep_bin_rel \<rightleftharpoons> dep_bin_rel_type

lemma dep_bin_rel_type_eq_dep_bin_rel_pred [simp]:
  "({\<Sum>}x : A. B x) = {\<Sum>}x : of_type A. of_type (B x)"
  unfolding dep_bin_rel_type_def by simp

lemma dep_bin_rel_type_eq_dep_bin_rel_pred_uhint [uhint]:
  assumes "A' \<equiv> of_type A"
  and "\<And>x. B' x \<equiv> of_type (B x)"
  shows "{\<Sum>}x : A. B x \<equiv> {\<Sum>}x : A'. B' x"
  using assms by simp

lemma dep_bin_rel_type_iff_dep_bin_rel_pred [iff]:
  "({\<Sum>}x : A. B x) R \<longleftrightarrow> ({\<Sum>}x : of_type A. of_type (B x)) R"
  by simp

definition "bin_rel_type A B \<equiv> of_type A {\<times>} of_type B"
adhoc_overloading bin_rel \<rightleftharpoons> bin_rel_type

lemma bin_rel_type_eq_bin_rel_pred [simp]: "(A {\<times>} B) = (of_type A {\<times>} of_type B)"
  unfolding bin_rel_type_def by simp

lemma bin_rel_type_eq_bin_rel_pred_uhint [uhint]:
  assumes "A' \<equiv> of_type A"
  and "B' \<equiv> of_type B"
  shows "A {\<times>} B \<equiv> A' {\<times>} B'"
  using assms by simp

lemma bin_rel_type_iff_bin_rel_pred [iff]:
  "(A {\<times>} B) R \<longleftrightarrow> (of_type A {\<times>} of_type B) R"
  by simp

definition [typedef]: "Dep_bin_rel (A :: 'a type) B \<equiv> type ({\<Sum>}x : A. B x)"
adhoc_overloading dep_bin_rel \<rightleftharpoons> Dep_bin_rel

lemma of_type_Dep_bin_rel_eq_dep_bin_rel_type [type_to_HOL_simp]:
  "of_type ({\<Sum>}x : A. B x) = ({\<Sum>}x : A. B x)"
  unfolding Dep_bin_rel_def type_to_HOL_simp by simp

soft_type_translation
  "({\<Sum>}x : (A :: _ type). B x) R" \<rightleftharpoons> "R \<Ztypecolon> {\<Sum>}x : A. B x"
  unfolding type_to_HOL_simp by simp

definition [typedef]: "Bin_rel (A :: 'a type) B \<equiv> type (A {\<times>} B)"
adhoc_overloading bin_rel \<rightleftharpoons> Bin_rel

lemma of_type_Bin_rel_eq_bin_rel_type [type_to_HOL_simp]:
  "of_type (A {\<times>} B) = (A {\<times>} B)"
  unfolding Bin_rel_def type_to_HOL_simp by simp

soft_type_translation
  "((A :: _ type) {\<times>} B) R" \<rightleftharpoons> "R \<Ztypecolon> A {\<times>} B"
  unfolding type_to_HOL_simp by simp

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
begin

lemma Dep_bin_relI [type_intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> x \<Ztypecolon> A"
  and "\<And>x y. R x y \<Longrightarrow> x \<Ztypecolon> A \<Longrightarrow> y \<Ztypecolon> B x"
  shows "R \<Ztypecolon> {\<Sum>}x : A. B x"
  by (urule dep_bin_relI) (use assms in simp_all)

lemma Dep_bin_rel_if_bin_rel_and:
  assumes "\<And>x y. R x y \<Longrightarrow> x \<Ztypecolon> A \<and> y \<Ztypecolon> B x"
  shows "R \<Ztypecolon> {\<Sum>}x : A. B x"
  using assms by (urule dep_bin_rel_if_bin_rel_and)

lemma Dep_bin_relE:
  assumes "R \<Ztypecolon> {\<Sum>}x : A. B x"
  and "R x y"
  obtains "x \<Ztypecolon> A" "y \<Ztypecolon> B x"
  using assms by (urule (e) dep_bin_relE)

lemma Dep_bin_relE':
  assumes "R \<Ztypecolon> {\<Sum>}x : A. B x"
  obtains "\<And>x y. R x y \<Longrightarrow> x \<Ztypecolon> A \<and> y \<Ztypecolon> B x"
  using assms by (urule (e) dep_bin_relE')

lemma Dep_bin_rel_cong [cong]:
  assumes "\<And>x. x \<Ztypecolon> A \<longleftrightarrow> x \<Ztypecolon> A'"
  and "\<And>x y. x \<Ztypecolon> A' \<Longrightarrow> y \<Ztypecolon> B x \<longleftrightarrow> y \<Ztypecolon> B' x"
  shows "(R \<Ztypecolon> {\<Sum>}x : A. B x) \<longleftrightarrow> (R \<Ztypecolon> {\<Sum>}x : A'. B' x)"
  by (urule dep_bin_rel_cong[THEN fun_cong]) (use assms in auto)

lemma Dep_bin_rel_covariant_dom:
  assumes "R \<Ztypecolon> {\<Sum>}x : A. B x"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> x \<Ztypecolon> A'"
  shows "R \<Ztypecolon> {\<Sum>}x : A'. B x"
  using assms by auto

lemma Dep_bin_rel_covariant_codom:
  assumes "R \<Ztypecolon> {\<Sum>}x : A. (B x)"
  and "\<And>x y. R x y \<Longrightarrow> x \<Ztypecolon> A \<Longrightarrow> y \<Ztypecolon> B x \<Longrightarrow> y \<Ztypecolon> B' x"
  shows "R \<Ztypecolon> {\<Sum>}x : A. (B' x)"
  using assms by (urule dep_bin_rel_covariant_codom where chained = fact)

lemma Bin_rel_eq_Dep_bin_rel: "(A {\<times>} B) = Dep_bin_rel A (\<lambda>_. B)"
  supply bin_rel_pred_eq_dep_bin_rel_pred[simp] by (urule refl)

lemma Bin_rel_eq_Dep_bin_rel_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A {\<times>} B \<equiv> Dep_bin_rel A' B'"
  by (rule eq_reflection) (use assms Bin_rel_eq_Dep_bin_rel in simp)

lemma Bin_rel_iff_Dep_bin_rel: "(R \<Ztypecolon> A {\<times>} B) \<longleftrightarrow> R \<Ztypecolon> {\<Sum>}_ : A. B"
  unfolding Bin_rel_eq_Dep_bin_rel by simp

lemma Bin_relI [type_intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> x \<Ztypecolon> A"
  and "\<And>x y. R x y \<Longrightarrow> x \<Ztypecolon> A \<Longrightarrow> y \<Ztypecolon> B"
  shows "R \<Ztypecolon> A {\<times>} B"
  using assms by (urule bin_relI where chained = fact)

lemma Bin_rel_if_bin_rel_and:
  assumes "\<And>x y. R x y \<Longrightarrow> x \<Ztypecolon> A \<and> y \<Ztypecolon> B"
  shows "R \<Ztypecolon> A {\<times>} B"
  using assms by (urule bin_rel_if_bin_rel_and)

lemma Bin_relE:
  assumes "R \<Ztypecolon> A {\<times>} B"
  and "R x y"
  obtains "x \<Ztypecolon> A" "y \<Ztypecolon> B"
  using assms by (urule (e) bin_relE)

lemma Bin_relE':
  assumes "R \<Ztypecolon> A {\<times>} B"
  obtains "\<And>x y. R x y \<Longrightarrow> x \<Ztypecolon> A \<and> y \<Ztypecolon> B"
  using assms by (urule (e) dep_bin_relE')

lemma Bin_rel_covariant_dom:
  assumes "R \<Ztypecolon> A {\<times>} B"
  and "\<And>x. x \<Ztypecolon> A \<Longrightarrow> x \<Ztypecolon> A'"
  shows "R \<Ztypecolon> A' {\<times>} B"
  using assms by (urule Dep_bin_rel_covariant_dom)

lemma Bin_rel_covariant_codom:
  assumes "R \<Ztypecolon> A {\<times>} B"
  and "\<And>x. x \<Ztypecolon> B \<Longrightarrow> x \<Ztypecolon> B'"
  shows "R \<Ztypecolon> A {\<times>} B'"
  using assms by (urule Dep_bin_rel_covariant_codom)

end

end