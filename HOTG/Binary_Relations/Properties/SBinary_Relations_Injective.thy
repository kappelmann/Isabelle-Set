\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Injective\<close>
theory SBinary_Relations_Injective
  imports
    SBinary_Relation_Functions
    Transport.Binary_Relations_Injective
begin

overloading
  rel_injective_on_set \<equiv> "rel_injective_on :: set \<Rightarrow> (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  set_rel_injective_on_pred \<equiv> "rel_injective_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_rel_injective_on_set \<equiv> "rel_injective_on :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "rel_injective_on_set (A :: set) (R :: set \<Rightarrow> 'a \<Rightarrow> bool) \<equiv>
    rel_injective_on (mem_of A) R"
  definition "set_rel_injective_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> rel_injective_on P (rel R)"
  definition "set_rel_injective_on_set (A :: set) (R :: set) \<equiv> rel_injective_on (mem_of A) R"
end

lemma rel_injective_on_set_eq_rel_injective_on_pred [simp]:
  "(rel_injective_on (S :: set) :: (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = rel_injective_on (mem_of S)"
  unfolding rel_injective_on_set_def by simp

lemma rel_injective_on_set_eq_rel_injective_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "rel_injective_on (S :: set) :: (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_injective_on P"
  using assms by simp

lemma rel_injective_on_set_iff_rel_injective_on_pred [iff]:
  "rel_injective_on (S :: set) (R :: set \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> rel_injective_on (mem_of S) R"
  by simp

lemma set_rel_injective_on_pred_iff_rel_injective_on_pred [iff]:
  "rel_injective_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> rel_injective_on P (rel R)"
  unfolding set_rel_injective_on_pred_def by simp

lemma set_rel_injective_on_pred_iff_rel_injective_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "rel_injective_on (P :: set \<Rightarrow> bool) S \<equiv> rel_injective_on P R"
  using assms by simp

lemma set_rel_injective_on_set_eq_set_rel_injective_on_pred [simp]:
  "(rel_injective_on (S :: set) :: set \<Rightarrow> bool) = rel_injective_on (mem_of S)"
  unfolding set_rel_injective_on_set_def by simp

lemma set_rel_injective_on_set_eq_set_rel_injective_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "rel_injective_on (S :: set) :: set \<Rightarrow> bool \<equiv> rel_injective_on P"
  using assms by simp

lemma set_rel_injective_on_set_iff_set_rel_injective_on_pred [iff]:
  "rel_injective_on (S :: set) (R :: set) \<longleftrightarrow> rel_injective_on (mem_of S) R"
  by simp


overloading
  rel_injective_at_set \<equiv> "rel_injective_at :: set \<Rightarrow> ('a \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
  set_rel_injective_at_pred \<equiv> "rel_injective_at :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_rel_injective_at_set \<equiv> "rel_injective_at :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "rel_injective_at_set (A :: set) (R :: 'a \<Rightarrow> set \<Rightarrow> bool) \<equiv>
    rel_injective_at (mem_of A) R"
  definition "set_rel_injective_at_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> rel_injective_at P (rel R)"
  definition "set_rel_injective_at_set (A :: set) (R :: set) \<equiv> rel_injective_at (mem_of A) R"
end

lemma rel_injective_at_set_eq_rel_injective_at_pred [simp]:
  "(rel_injective_at (S :: set) :: ('a \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = rel_injective_at (mem_of S)"
  unfolding rel_injective_at_set_def by simp

lemma rel_injective_at_set_eq_rel_injective_at_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "rel_injective_at (S :: set) :: ('a \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_injective_at P"
  using assms by simp

lemma rel_injective_at_set_iff_rel_injective_at_pred [iff]:
  "rel_injective_at (S :: set) (R :: 'a \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> rel_injective_at (mem_of S) R"
  by simp

lemma set_rel_injective_at_pred_iff_rel_injective_at_pred [iff]:
  "rel_injective_at (P :: set \<Rightarrow> bool) R \<longleftrightarrow> rel_injective_at P (rel R)"
  unfolding set_rel_injective_at_pred_def by simp

lemma set_rel_injective_at_pred_iff_rel_injective_at_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "rel_injective_at (P :: set \<Rightarrow> bool) S \<equiv> rel_injective_at P R"
  using assms by simp

lemma set_rel_injective_at_set_eq_set_rel_injective_at_pred [simp]:
  "(rel_injective_at (S :: set) :: set \<Rightarrow> bool) = rel_injective_at (mem_of S)"
  unfolding set_rel_injective_at_set_def by simp

lemma set_rel_injective_at_set_eq_set_rel_injective_at_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "rel_injective_at (S :: set) :: set \<Rightarrow> bool \<equiv> rel_injective_at P"
  using assms by simp

lemma set_rel_injective_at_set_iff_set_rel_injective_at_pred [iff]:
  "rel_injective_at (S :: set) (R :: set) \<longleftrightarrow> rel_injective_at (mem_of S) R"
  by simp


end