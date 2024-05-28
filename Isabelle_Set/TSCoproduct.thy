\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Set-Theoretic \<Coprod>-type\<close>
theory TSCoproduct
  imports
    HOTG.HOTG_Coproduct
    TSBasics
begin

definition "set_coprod_type A B \<equiv> of_type A \<Coprod> of_type B"
adhoc_overloading coprod set_coprod_type

lemma set_coprod_type_eq_set_coprod_pred [simp]: "A \<Coprod> B = of_type A \<Coprod> of_type B"
  unfolding set_coprod_type_def by simp

lemma set_coprod_type_eq_set_coprod_pred_uhint [uhint]:
  assumes "A' \<equiv> of_type A"
  assumes "B' \<equiv> of_type B"
  shows "A \<Coprod> B = A' \<Coprod> B'"
  using assms by simp

lemma set_coprod_type_iff_set_coprod_pred [iff]: "(A \<Coprod> B) x \<longleftrightarrow> (of_type A \<Coprod> of_type B) x"
  by simp

definition [typedef]: "Coprod (A :: set type) B \<equiv> type (A \<Coprod> B)"
adhoc_overloading coprod Coprod

lemma of_type_Coprod_eq_set_coprod_type [type_to_HOL_simp]:
  "of_type (A \<Coprod> B) = (A \<Coprod> B)"
  unfolding Coprod_def type_to_HOL_simp by simp

soft_type_translation
  "((A :: set type) \<Coprod> B) x" \<rightleftharpoons> "x \<Ztypecolon> A \<Coprod> B"
  unfolding type_to_HOL_simp by simp

lemma mem_of_coprod_eq_of_type_Coprod_Element:
  "mem_of (A \<Coprod> B) = of_type (Element A \<Coprod> Element B)"
  unfolding type_to_HOL_simp by force

soft_type_translation
  "x \<in> A \<Coprod> B" \<rightleftharpoons> "x \<Ztypecolon> Element A \<Coprod> Element B"
  unfolding type_to_HOL_simp by fastforce+

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
begin

lemma CoprodE [elim]:
  assumes "x \<Ztypecolon> A \<Coprod> B"
  obtains (inl) a where "a \<Ztypecolon> A" "x = inl a" | (inr) b where "b \<Ztypecolon> B" "x = inr b"
  using assms by (urule (e) set_coprodE) simp

lemma inl_type [type]: "inl \<Ztypecolon> A \<Rightarrow> (A \<Coprod> B)" by (urule mono_set_coprod_inl)

lemma inr_type [type]: "inr \<Ztypecolon> B \<Rightarrow> (A \<Coprod> B)" by (urule mono_set_coprod_inr)

lemma coprod_rec_type [type]: "coprod_rec \<Ztypecolon> (A \<Rightarrow> X) \<Rightarrow> (B \<Rightarrow> X) \<Rightarrow> (A \<Coprod> B) \<Rightarrow> X"
  by (urule mono_set_coprod_coprod_rec)

end


end
