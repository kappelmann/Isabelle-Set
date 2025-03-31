\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Typed Set-Theoretic Binary Relations\<close>
theory TSBinary_Relations_Base
  imports
    TSBasics
    Soft_Types.TDependent_Binary_Relations
    HOTG.HOTG_Binary_Relations_Base
    HOTG.HOTG_Functions_Monotone
begin

definition "set_dep_bin_rel_type A B :: set \<Rightarrow> bool \<equiv> {\<Sum>}x : of_type A. of_type (B x)"
adhoc_overloading dep_bin_rel \<rightleftharpoons> set_dep_bin_rel_type

lemma set_dep_bin_rel_type_eq_set_dep_bin_rel_pred [simp]:
  "({\<Sum>}x : A. B x :: set \<Rightarrow> bool) = {\<Sum>}x : of_type A. of_type (B x)"
  unfolding set_dep_bin_rel_type_def by simp

lemma set_dep_bin_rel_type_eq_dep_bin_rel_pred_uhint [uhint]:
  assumes "A' \<equiv> of_type A"
  and "\<And>x. B' x \<equiv> of_type (B x)"
  shows "{\<Sum>}x : A. B x :: set \<Rightarrow> bool \<equiv> {\<Sum>}x : A'. B' x"
  using assms by simp

lemma set_dep_bin_rel_type_iff_set_dep_bin_rel_pred [iff]:
  "({\<Sum>}x : A. B x) (R :: set) \<longleftrightarrow> ({\<Sum>}x : of_type A. of_type (B x)) R"
  by simp

definition "set_bin_rel_type A B :: set \<Rightarrow> bool \<equiv> of_type A {\<times>} of_type B"
adhoc_overloading bin_rel \<rightleftharpoons> set_bin_rel_type

lemma set_bin_rel_type_eq_set_bin_rel_pred [simp]:
  "(A {\<times>} B :: set \<Rightarrow> bool) = of_type A {\<times>} of_type B"
  unfolding set_bin_rel_type_def by simp

lemma set_bin_rel_type_eq_bin_rel_pred_uhint [uhint]:
  assumes "A :: set type \<equiv> A'"
  and "B \<equiv> B'"
  shows "A {\<times>} B :: set \<Rightarrow> bool \<equiv> A' {\<times>} B'"
  using assms by simp

lemma set_bin_rel_type_iff_set_bin_rel_pred [iff]:
  "(A {\<times>} B :: set \<Rightarrow> bool) R \<longleftrightarrow> (of_type A {\<times>} of_type B) R"
  by simp

definition [typedef]: "Set_dep_bin_rel (A :: set type) B \<equiv> type ({\<Sum>}x : A. B x :: set \<Rightarrow> bool)"
adhoc_overloading dep_bin_rel \<rightleftharpoons> Set_dep_bin_rel

lemma of_type_Set_dep_bin_rel_eq_set_set_dep_bin_rel_type [type_to_HOL_simp]:
  "of_type ({\<Sum>}x : A. B x :: set type) = ({\<Sum>}x : A. B x)"
  unfolding Set_dep_bin_rel_def type_to_HOL_simp by simp

soft_type_translation
  "({\<Sum>}x : (A :: set type). B x) (R :: set)" \<rightleftharpoons> "(R :: set) \<Ztypecolon> {\<Sum>}x : A. B x"
  unfolding type_to_HOL_simp by simp

lemma supset_dep_pair_eq_of_type_Set_dep_bin_rel_Element:
  "(\<supseteq>) (\<Sum>x : A. B x) = of_type ({\<Sum>}x : Element A. Element (B x))"
  by (simp add: type_to_HOL_simp)

soft_type_translation
  "R \<subseteq> \<Sum>x : A. B x" \<rightleftharpoons> "(R :: set) \<Ztypecolon> {\<Sum>}x : Element A. Element (B x)"
  using supset_dep_pair_eq_of_type_Set_dep_bin_rel_Element by simp_all

corollary Subset_dep_pair_iff_Set_dep_bin_rel_Element [iff]:
  "(R \<Ztypecolon> Subset (\<Sum>x : A. B x)) \<longleftrightarrow> (R \<Ztypecolon> {\<Sum>}x : Element A. Element (B x))"
  by (simp only: supset_dep_pair_eq_of_type_Set_dep_bin_rel_Element type_to_HOL_simp)

definition [typedef]: "Set_bin_rel (A :: set type) B \<equiv> type (A {\<times>} B :: set \<Rightarrow> bool)"
adhoc_overloading bin_rel \<rightleftharpoons> Set_bin_rel

lemma of_type_Set_bin_rel_eq_set_set_bin_rel_type [type_to_HOL_simp]:
  "of_type (A {\<times>} B :: set type) = (A {\<times>} B)"
  unfolding Set_bin_rel_def type_to_HOL_simp by simp

soft_type_translation
  "((A :: set type) {\<times>} B) (R :: set)" \<rightleftharpoons> "(R :: set) \<Ztypecolon> A {\<times>} B"
  unfolding type_to_HOL_simp by simp

lemma supset_pair_eq_of_type_Set_bin_rel_Element: "(\<supseteq>) (A \<times> B) = of_type (Element A {\<times>} Element B)"
  by (simp add: type_to_HOL_simp)

soft_type_translation
  "R \<subseteq> A \<times> B" \<rightleftharpoons> "(R :: set) \<Ztypecolon> Element A {\<times>} Element B"
  using supset_pair_eq_of_type_Set_bin_rel_Element by simp_all

corollary Subset_pair_iff_Set_bin_rel_Element [iff]:
  "(R \<Ztypecolon> Subset (A \<times> B)) \<longleftrightarrow> (R \<Ztypecolon> Element A {\<times>} Element B)"
  by (simp only: supset_pair_eq_of_type_Set_bin_rel_Element type_to_HOL_simp)

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
begin

lemma Set_dep_bin_relI:
  assumes "rel R \<Ztypecolon> {\<Sum>}x : A. B x"
  and "is_bin_rel R"
  shows "R \<Ztypecolon> {\<Sum>}x : A. B x"
  using assms by (urule set_dep_bin_relI)

lemma Set_dep_bin_relE:
  assumes "R \<Ztypecolon> {\<Sum>}x : A. B x"
  obtains "rel R \<Ztypecolon> {\<Sum>}x : A. B x" "is_bin_rel R"
  using assms by (urule (e) set_dep_bin_relE)

lemma rel_Dep_bin_rel_if_Set_dep_bin_rel [derive]:
  assumes "R \<Ztypecolon> {\<Sum>}x : A. B x"
  shows "rel R \<Ztypecolon> {\<Sum>}x : A. B x"
  using assms by (urule (e) Set_dep_bin_relE)

lemma Set_dep_bin_rel_cong [cong]:
  assumes "\<And>x. x \<Ztypecolon> A \<longleftrightarrow> x \<Ztypecolon> A'"
  and "\<And>x y. x \<Ztypecolon> A' \<Longrightarrow> y \<Ztypecolon> B x \<longleftrightarrow> y \<Ztypecolon> B' x"
  shows "((R :: set) \<Ztypecolon> {\<Sum>}x : A. B x) \<longleftrightarrow> (R \<Ztypecolon> {\<Sum>}x : A'. B' x)"
  by (urule set_dep_bin_rel_cong[THEN fun_cong]) (use assms in auto)

lemma Set_bin_rel_eq_Set_dep_bin_rel: "(A {\<times>} B) = Set_dep_bin_rel A (\<lambda>_. B)"
  supply set_bin_rel_pred_eq_set_dep_bin_rel_pred[simp]
  by (urule refl)

lemma Set_bin_rel_eq_Set_dep_bin_rel_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A {\<times>} B \<equiv> Set_dep_bin_rel A' B'"
  by (rule eq_reflection) (use assms Set_bin_rel_eq_Set_dep_bin_rel in simp)

lemma Set_bin_rel_iff_Set_dep_bin_rel: "((R :: set) \<Ztypecolon> A {\<times>} B) \<longleftrightarrow> R \<Ztypecolon> {\<Sum>}_ : A. B"
  using Set_bin_rel_eq_Set_dep_bin_rel by simp

lemma Set_bin_relI:
  assumes "rel R \<Ztypecolon> A {\<times>} B"
  and "is_bin_rel R"
  shows "R \<Ztypecolon> A {\<times>} B"
  using assms by (urule set_bin_relI)

lemma Set_bin_relE:
  assumes "R \<Ztypecolon> A {\<times>} B"
  obtains "rel R \<Ztypecolon> A {\<times>} B" "is_bin_rel R"
  using assms by (urule (e) set_bin_relE)

lemma rel_Bin_rel_if_Set_bin_rel [derive]:
  assumes "R \<Ztypecolon> A {\<times>} B"
  shows "rel R \<Ztypecolon> A {\<times>} B"
  using assms by (urule (e) Set_bin_relE)

lemma rel_type [type]:
  "rel \<Ztypecolon> ({\<Sum>}x : A. B x :: set type) \<Rightarrow> ({\<Sum>}x : A. B x :: (set \<Rightarrow> set \<Rightarrow> bool) type)"
  by (urule mono_set_dep_bin_rel_dep_bin_rel_rel)

end

end
