\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Coproduct (\<open>\<Coprod>\<close>-Types, Binary Disjoint Union)\<close>
theory HOTG_Coproduct
  imports
    HOTG_Functions_Base
begin

unbundle no HOL_ascii_syntax

definition "inl a = \<langle>{}, a\<rangle>"
definition "inr b = \<langle>{{}}, b\<rangle>"

lemma
  shows inl_eq_iff_eq [iff]: "inl x = inl y \<longleftrightarrow> x = y"
  and inr_eq_iff_eq [iff]: "inr x = inr y \<longleftrightarrow> x = y"
  and inl_ne_inr [iff]: "inl x \<noteq> inr y"
  and inr_ne_inl [iff]: "inr x \<noteq> inl y"
  unfolding inl_def inr_def by auto

definition "coprod_rec l r x = (if fst x = {} then l (snd x) else r (snd x))"

lemma coprod_rec_eq:
  shows coprod_rec_inl_eq [simp]: "coprod_rec l r (inl a) = l a"
  and coprod_rec_inr_eq [simp]: "coprod_rec l r (inr b) = r b"
  unfolding coprod_rec_def inl_def inr_def by auto

consts coprod :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

open_bundle coprod_syntax begin notation coprod (infixr "\<Coprod>" 70) end

definition "set_coprod_pred (A :: set \<Rightarrow> bool) (B :: set \<Rightarrow> bool) \<equiv>
  has_inverse_on A inl \<squnion> has_inverse_on B inr"
adhoc_overloading coprod \<rightleftharpoons> set_coprod_pred

lemma set_coprod_if_has_inverse_on_inl:
  assumes "has_inverse_on A inl x"
  shows "(A \<Coprod> B) x"
  using assms unfolding set_coprod_pred_def by simp

lemma set_coprod_if_has_inverse_on_inr:
  assumes "has_inverse_on B inr x"
  shows "(A \<Coprod> B) x"
  using assms unfolding set_coprod_pred_def by simp

lemma set_coprodE:
  assumes "(A \<Coprod> B) x"
  obtains (inl) a where "A a" "x = inl a" | (inr) b where "B b" "x = inr b"
  using assms unfolding set_coprod_pred_def by auto

corollary set_coprod_iff [iff]:
  "(A \<Coprod> B) x \<longleftrightarrow> (\<exists>a : A. x = inl a) \<or> (\<exists>b : B. x = inr b)"
  by (auto intro: set_coprod_if_has_inverse_on_inl set_coprod_if_has_inverse_on_inr elim: set_coprodE)

lemma set_coprod_inl_iff [iff]: "(A \<Coprod> B) (inl a) \<longleftrightarrow> A a" by auto
lemma set_coprod_inr_iff [iff]: "(A \<Coprod> B) (inr b) \<longleftrightarrow> B b" by auto

lemma mono_set_coprod_inl: "(A \<Rightarrow> A \<Coprod> B) inl" by auto
lemma mono_set_coprod_inr: "(B \<Rightarrow> A \<Coprod> B) inr" by auto
lemma mono_set_coprod_coprod_rec: "((A \<Rightarrow> C) \<Rightarrow> (B \<Rightarrow> C) \<Rightarrow> A \<Coprod> B \<Rightarrow> C) coprod_rec" by fastforce

lemma mono_set_coprod: "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<le>)) (\<Coprod>)" by blast

definition "set_coprod_set A B \<equiv> mem_of A \<Coprod> mem_of B"
adhoc_overloading coprod \<rightleftharpoons> set_coprod_set

lemma set_coprod_set_eq_set_coprod_pred [simp]: "A \<Coprod> B = mem_of A \<Coprod> mem_of B"
  unfolding set_coprod_set_def by simp

lemma set_coprod_set_eq_set_coprod_pred_uhint [uhint]:
  assumes "A' \<equiv> mem_of A"
  assumes "B' \<equiv> mem_of B"
  shows "A \<Coprod> B = A' \<Coprod> B'"
  using assms by simp

lemma set_coprod_set_iff_set_coprod_pred [iff]: "(A \<Coprod> B) x \<longleftrightarrow> (mem_of A \<Coprod> mem_of B) x"
  by simp

definition "set_set_coprod_set A B \<equiv> {inl a | a \<in> A} \<union> {inr b | b \<in> B}"
adhoc_overloading coprod \<rightleftharpoons> set_set_coprod_set

lemma mem_coprod_set_if_has_inverse_on_inl:
  assumes "has_inverse_on A inl x"
  shows "x \<in> A \<Coprod> B"
  using assms unfolding set_set_coprod_set_def by auto

lemma mem_coprod_set_if_has_inverse_on_inr:
  assumes "has_inverse_on B inr x"
  shows "x \<in> A \<Coprod> B"
  using assms unfolding set_set_coprod_set_def by auto

lemma mem_coprod_setE:
  assumes "x \<in> A \<Coprod> B"
  obtains (inl) a where "a \<in> A" "x = inl a" | (inr) b where "b \<in> B" "x = inr b"
  using assms unfolding set_set_coprod_set_def by auto

lemma mem_of_coprod_set_eq_set_coprod_set [simp, set_to_HOL_simp]: "mem_of (A \<Coprod> B) = A \<Coprod> B"
  by (force intro: mem_coprod_set_if_has_inverse_on_inl mem_coprod_set_if_has_inverse_on_inr
    elim: mem_coprod_setE)

corollary mem_coprod_set_iff_set_coprod_set [iff]: "x \<in> A \<Coprod> B \<longleftrightarrow> (A \<Coprod> B) x"
  by (simp flip: mem_of_iff)

lemma mono_subset_coprod_set: "((\<subseteq>) \<Rightarrow> (\<subseteq>) \<Rrightarrow> (\<subseteq>)) (\<Coprod>)" by blast

end
