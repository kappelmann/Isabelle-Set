section \<open>Sum type, aka binary disjoint union/coproduct\<close>

theory Sum
imports Ordered_Pair

begin

definition "inl a = \<langle>{}, a\<rangle>"
definition "inr b = \<langle>{{}}, b\<rangle>"
definition "Sum A B = Repl A inl \<union> Repl B inr"

lemma Sum_type_iff: "x \<in> Sum A B \<longleftrightarrow> (\<exists>a \<in> A. x = inl a) \<or> (\<exists>b \<in> B. x = inr b)"
  unfolding Sum_def inl_def inr_def by blast

lemma
  inl_inject [iff]: "inl x = inl y \<longleftrightarrow> x = y" and
  inr_inject [iff]: "inr x = inr y \<longleftrightarrow> x = y" and
  inl_inr [simp]: "inl x = inr y \<longleftrightarrow> False" and
  inr_inl [simp]: "inr y = inl x \<longleftrightarrow> False"

  unfolding inl_def inr_def by auto

definition "Sum_case l r x = (if fst x = {} then l (snd x) else r (snd x))"

lemma
  Sum_case_inl [simp]: "Sum_case l r (inl a) = l a" and
  Sum_case_inr [simp]: "Sum_case l r (inr b) = r b" 
  unfolding Sum_case_def inl_def inr_def by auto


lemma Sum_elim [case_names inl inr]:
  assumes "x \<in> Sum A B"
  obtains a where "a \<in> A" "x = inl a" | b where "b \<in> B" "x = inr b"
  using assms unfolding Sum_def by blast

lemma inl_type [type]: "inl : element A \<Rightarrow> element (Sum A B)"
  unfolding inl_def Sum_def by squash_types blast

lemma inr_type [type]: "inr : element B \<Rightarrow> element (Sum A B)"
  unfolding inr_def Sum_def by squash_types blast

lemma Univ_closed_inl [derive]: "x : element (Univ A) \<Longrightarrow> inl x : element (Univ A)"
  unfolding inl_def by discharge_types

lemma Univ_closed_inr [derive]: "x : element (Univ A) \<Longrightarrow> inr x : element (Univ A)"
  unfolding inr_def by discharge_types


end
