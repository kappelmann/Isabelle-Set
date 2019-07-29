theory Sum_Type
  imports Pair Universe
begin

definition "Inl a = \<langle>{}, a\<rangle>"
definition "Inr b = \<langle>{{}}, b\<rangle>"
definition "Sum_Type A B = Repl A Inl \<union> Repl B Inr"

lemma sum_type_iff: "x \<in> Sum_Type A B \<longleftrightarrow> (\<exists>a\<in>A. x = Inl a) \<or> (\<exists>b\<in>B. x = Inr b)"
  unfolding Sum_Type_def Inl_def Inr_def by blast

lemma
  Inl_inject[iff]: "Inl x = Inl y \<longleftrightarrow> x = y" and
  Inr_inject[iff]: "Inr x = Inr y \<longleftrightarrow> x = y" and
  Inl_Inr[simp]: "Inl x = Inr y \<longleftrightarrow> False" and
  Inr_Inl[simp]: "Inr y = Inl x \<longleftrightarrow> False"

  unfolding Inl_def Inr_def by auto

definition "sum_case l r x = (if fst x = {} then l (snd x) else r (snd x))"

lemma
  sum_case_Inl[simp]: "sum_case l r (Inl a) = l a" and
  sum_case_Inr[simp]: "sum_case l r (Inr b) = r b" 
  unfolding sum_case_def Inl_def Inr_def by auto


lemma sum_elim[case_names Inl Inr]:
  assumes "x \<in> Sum_Type A B"
  obtains a where "a \<in> A" "x = Inl a" | b where "b \<in> B" "x = Inr b"
  using assms unfolding Sum_Type_def by blast


lemma Inl_type[type]: "Inl : element A \<Rightarrow> element (Sum_Type A B)"
  unfolding Inl_def Sum_Type_def by squash_types blast

lemma Inr_type[type]: "Inr : element B \<Rightarrow> element (Sum_Type A B)"
  unfolding Inr_def Sum_Type_def by squash_types blast

lemma Pair_Univ[derive]: "x : element (Univ A) \<Longrightarrow> y : element (Univ A) \<Longrightarrow> \<langle>x, y\<rangle> : element (Univ A)"
  unfolding Pair_def 
  by squash_types (auto intro!: Univ_Cons Univ_empty)

lemma Inl_Univ [derive]: "x : element (Univ A) \<Longrightarrow> Inl x : element (Univ A)"
  unfolding Inl_def 
  by discharge_types

lemma Inr_Univ [derive]: "x : element (Univ A) \<Longrightarrow> Inr x : element (Univ A)"
  unfolding Inr_def 
  by discharge_types

lemma times_Univ[derive]: "X : element (Univ A) \<Longrightarrow> Y : element (Univ A) \<Longrightarrow> X \<times> Y : element (Univ A)"
  unfolding DUnion_def 
  apply (rule Univ_type_Union)
  apply (rule Univ_type_Repl)
   apply assumption
  apply (rule Univ_type_Union)
  apply (rule Univ_type_Repl)
   apply assumption
  apply (rule Univ_type_Cons)
   apply (rule Pair_Univ)
  apply (rule Univ_element_closed_type, assumption+)
   apply (rule Univ_element_closed_type, assumption+)
  by (rule Univ_type_empty)



end