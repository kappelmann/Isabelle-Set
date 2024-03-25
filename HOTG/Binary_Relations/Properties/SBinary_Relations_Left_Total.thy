\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Left Total\<close>
theory SBinary_Relations_Left_Total
  imports
    SBinary_Relation_Functions
    Transport.Binary_Relations_Left_Total
begin

overloading
  left_total_on_set \<equiv> "left_total_on :: set \<Rightarrow> (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  set_left_total_on_pred \<equiv> "left_total_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_left_total_on_set \<equiv> "left_total_on :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "left_total_on_set (A :: set) (R :: set \<Rightarrow> 'a \<Rightarrow> bool) \<equiv>
    left_total_on (mem_of A) R"
  definition "set_left_total_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> left_total_on P (rel R)"
  definition "set_left_total_on_set (A :: set) (R :: set) \<equiv> left_total_on (mem_of A) R"
end

lemma left_total_on_set_eq_left_total_on_pred [simp]:
  "(left_total_on (S :: set) :: (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = left_total_on (mem_of S)"
  unfolding left_total_on_set_def by simp

lemma left_total_on_set_eq_left_total_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "left_total_on (S :: set) :: (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> left_total_on P"
  using assms by simp

lemma left_total_on_set_iff_left_total_on_pred [iff]:
  "left_total_on (S :: set) (R :: set \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> left_total_on (mem_of S) R"
  by simp

lemma set_left_total_on_pred_iff_left_total_on_pred [iff]:
  "left_total_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> left_total_on P (rel R)"
  unfolding set_left_total_on_pred_def by simp

lemma set_left_total_on_pred_iff_left_total_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "left_total_on (P :: set \<Rightarrow> bool) S \<equiv> left_total_on P R"
  using assms by simp

lemma set_left_total_on_set_eq_set_left_total_on_pred [simp]:
  "(left_total_on (S :: set) :: set \<Rightarrow> bool) = left_total_on (mem_of S)"
  unfolding set_left_total_on_set_def by simp

lemma set_left_total_on_set_eq_set_left_total_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "left_total_on (S :: set) :: set \<Rightarrow> bool \<equiv> left_total_on P"
  using assms by simp

lemma set_left_total_on_set_iff_set_left_total_on_pred [iff]:
  "left_total_on (S :: set) (R :: set) \<longleftrightarrow> left_total_on (mem_of S) R"
  by simp

lemma set_left_total_on_compI:
  fixes P :: "set \<Rightarrow> bool" and R S :: set
  assumes "left_total_on P R"
  and "left_total_on (codom (R\<restriction>\<^bsub>P\<^esub>)) S"
  shows "left_total_on P (set_rel_comp R S)"
  using assms by (urule left_total_on_compI)

end