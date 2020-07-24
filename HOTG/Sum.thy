section \<open>Set-Theoretic sum Type\<close>

text \<open>Aka binary disjoint union/coproduct.\<close>

theory Sum          
imports Ordered_Pairs
begin

definition "inl a = \<langle>{}, a\<rangle>"
definition "inr b = \<langle>{{}}, b\<rangle>"
definition "sum A B = {inl a | a \<in> A} \<union> {inr b | b \<in> B}"

lemma sum_iff: "x \<in> sum A B \<longleftrightarrow> (\<exists>a \<in> A. x = inl a) \<or> (\<exists>b \<in> B. x = inr b)"
  unfolding sum_def inl_def inr_def by blast

lemma
  inl_inject [iff]: "inl x = inl y \<longleftrightarrow> x = y" and
  inr_inject [iff]: "inr x = inr y \<longleftrightarrow> x = y" and
  inl_inr [simp]: "inl x = inr y \<longleftrightarrow> False" and
  inr_inl [simp]: "inr y = inl x \<longleftrightarrow> False"    

  unfolding inl_def inr_def by auto

lemma inl_in_sum_iff [simp]: "inl a \<in> sum A B \<longleftrightarrow> a \<in> A"
  unfolding sum_def by auto

lemma inr_in_sum_iff [simp]: "inr b \<in> sum A B \<longleftrightarrow> b \<in> B"
  unfolding sum_def by auto

definition "sum_case l r x = (if fst x = {} then l (snd x) else r (snd x))"

lemma
  sum_case_inl [simp]: "sum_case l r (inl a) = l a" and
  sum_case_inr [simp]: "sum_case l r (inr b) = r b"
  unfolding sum_case_def inl_def inr_def by auto

lemma sumE [elim, case_names inl inr]:
  assumes "x \<in> sum A B"
  obtains a where "a \<in> A" "x = inl a"
        | b where "b \<in> B" "x = inr b"
  using assms unfolding sum_def by blast


end
