section \<open>Sum type\<close>

text \<open>Aka binary disjoint union/coproduct.\<close>

theory Sum
imports Ordered_Pairs

begin

definition "inl a = \<langle>{}, a\<rangle>"
definition "inr b = \<langle>{{}}, b\<rangle>"
definition "Sum A B = {inl a | a \<in> A} \<union> {inr b | b \<in> B}"

lemma Sum_iff: "x \<in> Sum A B \<longleftrightarrow> (\<exists>a \<in> A. x = inl a) \<or> (\<exists>b \<in> B. x = inr b)"
  unfolding Sum_def inl_def inr_def by blast

lemma
  inl_inject [iff]: "inl x = inl y \<longleftrightarrow> x = y" and
  inr_inject [iff]: "inr x = inr y \<longleftrightarrow> x = y" and
  inl_inr [simp]: "inl x = inr y \<longleftrightarrow> False" and
  inr_inl [simp]: "inr y = inl x \<longleftrightarrow> False"

  unfolding inl_def inr_def by auto

lemma inl_in_Sum_iff [iff]: "inl a \<in> Sum A B \<longleftrightarrow> a \<in> A"
  unfolding Sum_def by auto

lemma inr_in_Sum_iff [iff]: "inr b \<in> Sum A B \<longleftrightarrow> b \<in> B"
  unfolding Sum_def by auto

definition "Sum_case l r x = (if fst x = {} then l (snd x) else r (snd x))"

lemma
  Sum_case_inl [simp]: "Sum_case l r (inl a) = l a" and
  Sum_case_inr [simp]: "Sum_case l r (inr b) = r b"
  unfolding Sum_case_def inl_def inr_def by auto

lemma SumE [elim, case_names inl inr]:
  assumes "x \<in> Sum A B"
  obtains a where "a \<in> A" "x = inl a" | b where "b \<in> B" "x = inr b"
  using assms unfolding Sum_def by blast

lemma Sum_caseE [elim]:
  assumes
    "x \<in> Sum A B"
    "\<And>a. a \<in> A \<Longrightarrow> l a \<in> C"
    "\<And>b. b \<in> B \<Longrightarrow> r b \<in> C"
  shows "Sum_case l r x \<in> C"
  using assms by auto

lemma Sum_case_type [type]:
  "Sum_case : (element A \<Rightarrow> X) \<Rightarrow> (element B \<Rightarrow> X) \<Rightarrow> element (Sum A B) \<Rightarrow> X"
  by unfold_types auto

lemma inl_type [type]: "inl : element A \<Rightarrow> element (Sum A B)"
  unfolding inl_def Sum_def by unfold_types blast

lemma inr_type [type]: "inr : element B \<Rightarrow> element (Sum A B)"
  unfolding inr_def Sum_def by unfold_types blast

lemma Univ_closed_inl [intro]: "x \<in> Univ A \<Longrightarrow> inl x \<in> Univ A"
  unfolding inl_def by auto

lemma Univ_closed_inr [intro]: "x \<in> Univ A \<Longrightarrow> inr x \<in> Univ A"
  unfolding inr_def by auto


end
