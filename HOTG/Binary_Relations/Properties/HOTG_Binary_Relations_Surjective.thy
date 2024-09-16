\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Surjective\<close>
theory HOTG_Binary_Relations_Surjective
  imports
    HOTG_Binary_Relations_Base
    Transport.Binary_Relations_Surjective
begin

overloading
  rel_surjective_at_set \<equiv> "rel_surjective_at :: set \<Rightarrow> ('a \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
  set_rel_surjective_at_pred \<equiv> "rel_surjective_at :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_rel_surjective_at_set \<equiv> "rel_surjective_at :: set \<Rightarrow> set \<Rightarrow> bool"
  rel_surjective_set \<equiv> "rel_surjective :: set \<Rightarrow> bool"
begin
  definition "rel_surjective_at_set (A :: set) (R :: 'a \<Rightarrow> set \<Rightarrow> bool) \<equiv>
    rel_surjective_at (mem_of A) R"
  definition "set_rel_surjective_at_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> rel_surjective_at P (rel R)"
  definition "set_rel_surjective_at_set (A :: set) (R :: set) \<equiv> rel_surjective_at (mem_of A) R"
  definition "rel_surjective_set :: set \<Rightarrow> bool \<equiv> rel_surjective_at (\<top> :: set \<Rightarrow> bool)"
end

lemma rel_surjective_at_set_eq_rel_surjective_at_pred [simp]:
  "(rel_surjective_at (S :: set) :: ('a \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = rel_surjective_at (mem_of S)"
  unfolding rel_surjective_at_set_def by simp

lemma rel_surjective_at_set_eq_rel_surjective_at_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "rel_surjective_at (S :: set) :: ('a \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_surjective_at P"
  using assms by simp

lemma rel_surjective_at_set_iff_rel_surjective_at_pred [iff]:
  "rel_surjective_at (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> rel_surjective_at (mem_of S) R"
  by simp

lemma set_rel_surjective_at_pred_iff_rel_surjective_at_pred [iff]:
  "rel_surjective_at (P :: set \<Rightarrow> bool) R \<longleftrightarrow> rel_surjective_at P (rel R)"
  unfolding set_rel_surjective_at_pred_def by simp

lemma set_rel_surjective_at_pred_iff_rel_surjective_at_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "rel_surjective_at P S \<equiv> rel_surjective_at P' R"
  using assms by simp

lemma set_rel_surjective_at_set_eq_set_rel_surjective_at_pred [simp]:
  "(rel_surjective_at (S :: set) :: set \<Rightarrow> bool) = rel_surjective_at (mem_of S)"
  unfolding set_rel_surjective_at_set_def by simp

lemma set_rel_surjective_at_set_eq_set_rel_surjective_at_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "rel_surjective_at (S :: set) :: set \<Rightarrow> bool \<equiv> rel_surjective_at P"
  using assms by simp

lemma set_rel_surjective_at_set_iff_set_rel_surjective_at_pred [iff]:
  "rel_surjective_at (S :: set) (R :: set) \<longleftrightarrow> rel_surjective_at (mem_of S) R"
  by simp

lemma rel_surjective_set_eq_set_rel_surjective_at:
  "(rel_surjective :: set \<Rightarrow> _) = rel_surjective_at (\<top> :: set \<Rightarrow> bool)"
  unfolding rel_surjective_set_def ..

lemma rel_surjective_set_eq_set_rel_surjective_at_uhint [uhint]:
  "P \<equiv> (\<top> :: set \<Rightarrow> bool) \<Longrightarrow> (rel_surjective :: set \<Rightarrow> _) \<equiv> rel_surjective_at P"
  by (simp add: rel_surjective_set_eq_set_rel_surjective_at)

lemma rel_surjective_set_iff_rel_surjective_pred [iff]:
  "rel_surjective S \<longleftrightarrow> rel_surjective (rel S)"
  unfolding rel_surjective_set_eq_set_rel_surjective_at by (urule refl)

lemma rel_surjective_set_eq_rel_surjective_pred_uhint [uhint]:
  "R \<equiv> rel A \<Longrightarrow> rel_surjective A \<equiv> rel_surjective R"
  by simp

end