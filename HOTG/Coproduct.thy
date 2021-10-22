section \<open>Coproduct (\<Coprod>-types)\<close>

text \<open>Aka binary disjoint union.\<close>

theory Coproduct
imports Pairs
begin

definition "inl a = \<langle>{}, a\<rangle>"
definition "inr b = \<langle>{{}}, b\<rangle>"
definition coprod :: \<open>[set, set] \<Rightarrow> set\<close> (infixl "\<Coprod>" 70)
  where "A \<Coprod> B = {inl a | a \<in> A} \<union> {inr b | b \<in> B}"

lemma elem_coprod_iff [iff]:
  "x \<in> A \<Coprod> B \<longleftrightarrow> (\<exists>a \<in> A. x = inl a) \<or> (\<exists>b \<in> B. x = inr b)"
  unfolding coprod_def inl_def inr_def by auto

lemma
  inl_eq_iff [iff]: "inl x = inl y \<longleftrightarrow> x = y" and
  inr_eq_iff [iff]: "inr x = inr y \<longleftrightarrow> x = y" and
  inl_ne_inr [simp, intro!]: "inl x \<noteq> inr y" and
  inr_ne_inl [simp, intro!]: "inr x \<noteq> inl y"
  unfolding inl_def inr_def by auto

lemma inl_mem_coprod_iff [iff]: "inl a \<in> A \<Coprod> B \<longleftrightarrow> a \<in> A"
  unfolding coprod_def by auto

lemma inr_mem_coprod_iff [iff]: "inr b \<in> A \<Coprod> B \<longleftrightarrow> b \<in> B"
  unfolding coprod_def by auto

definition "coprod_rec l r x = (if fst x = {} then l (snd x) else r (snd x))"

lemma
  coprod_rec_inl_eq [simp]: "coprod_rec l r (inl a) = l a" and
  coprod_rec_inr_eq [simp]: "coprod_rec l r (inr b) = r b"
  unfolding coprod_rec_def inl_def inr_def by auto

lemma mem_coprodE [elim]:
  assumes coprodes "x \<in> coprod A B"
  obtains (inl) a where "a \<in> A" "x = inl a"
        | (inr) b where "b \<in> B" "x = inr b"
  using assms by blast


end
