\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Coproduct (\<open>\<Coprod>\<close>-types)\<close>
text \<open>Aka binary disjoint union.\<close>
theory Coproduct
  imports Pairs
begin

unbundle no_HOL_ascii_syntax

definition "inl a = \<langle>{}, a\<rangle>"
definition "inr b = \<langle>{{}}, b\<rangle>"
definition "coprod A B \<equiv> {inl a | a \<in> A} \<union> {inr b | b \<in> B}"

bundle hotg_coprod_syntax begin notation coprod (infixl "\<Coprod>" 70) end
bundle no_hotg_coprod_syntax begin no_notation coprod (infixl "\<Coprod>" 70) end

unbundle hotg_coprod_syntax

lemma mem_coprod_iff [iff]:
  "x \<in> A \<Coprod> B \<longleftrightarrow> (\<exists>a \<in> A. x = inl a) \<or> (\<exists>b \<in> B. x = inr b)"
  unfolding coprod_def inl_def inr_def by auto

lemma mem_coprodE:
  assumes "x \<in> A \<Coprod> B"
  obtains (inl) a where "a \<in> A" "x = inl a" | (inr) b where "b \<in> B" "x = inr b"
  using assms by blast

lemma
  inl_inj_iff [iff]: "inl x = inl y \<longleftrightarrow> x = y" and
  inr_inj_iff [iff]: "inr x = inr y \<longleftrightarrow> x = y" and
  inl_ne_inr [iff]: "inl x \<noteq> inr y" and
  inr_ne_inl [iff]: "inr x \<noteq> inl y"
  unfolding inl_def inr_def by auto

lemma inl_mem_coprod_iff [iff]: "inl a \<in> A \<Coprod> B \<longleftrightarrow> a \<in> A"
  unfolding coprod_def by auto

lemma inr_mem_coprod_iff [iff]: "inr b \<in> A \<Coprod> B \<longleftrightarrow> b \<in> B"
  unfolding coprod_def by auto

definition "coprod_rec l r x = (if fst x = {} then l (snd x) else r (snd x))"

lemma coprod_rec_eq:
  shows coprod_rec_inl_eq [simp]: "coprod_rec l r (inl a) = l a"
  and coprod_rec_inr_eq [simp]: "coprod_rec l r (inr b) = r b"
  unfolding coprod_rec_def inl_def inr_def by auto

lemma mono_subset_coprod: "((\<subseteq>) \<Rrightarrow>\<^sub>m (\<subseteq>) \<Rrightarrow> (\<subseteq>)) (\<Coprod>)" by blast

end
