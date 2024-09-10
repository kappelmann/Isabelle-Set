\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Partial Equivalence Relations\<close>
theory HOTG_Partial_Equivalence_Relations
  imports
    HOTG_Binary_Relations_Symmetric
    HOTG_Binary_Relations_Transitive
    Transport.Partial_Equivalence_Relations
begin

lemma partial_equivalence_rel_on_set_eq_partial_equivalence_rel_on_pred [simp]:
  "(partial_equivalence_rel_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = partial_equivalence_rel_on (mem_of S)"
  unfolding partial_equivalence_rel_on_def by simp

lemma partial_equivalence_rel_on_set_eq_partial_equivalence_rel_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "partial_equivalence_rel_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> partial_equivalence_rel_on P"
  using assms by simp

lemma partial_equivalence_rel_on_set_iff_partial_equivalence_rel_on_pred [iff]:
  "partial_equivalence_rel_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> partial_equivalence_rel_on (mem_of S) R"
  by simp

lemma set_partial_equivalence_rel_on_pred_iff_partial_equivalence_rel_on_pred [iff]:
  "partial_equivalence_rel_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> partial_equivalence_rel_on P (rel R)"
  unfolding partial_equivalence_rel_on_def by simp

lemma set_partial_equivalence_rel_on_pred_iff_partial_equivalence_rel_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "partial_equivalence_rel_on P S \<equiv> partial_equivalence_rel_on P' R"
  using assms by simp

lemma set_partial_equivalence_rel_on_set_eq_set_partial_equivalence_rel_on_pred [simp]:
  "(partial_equivalence_rel_on (S :: set) :: set \<Rightarrow> bool) = partial_equivalence_rel_on (mem_of S)"
  unfolding partial_equivalence_rel_on_def by simp

lemma set_partial_equivalence_rel_on_set_eq_set_partial_equivalence_rel_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "partial_equivalence_rel_on (S :: set) :: set \<Rightarrow> bool \<equiv> partial_equivalence_rel_on P"
  using assms by simp

lemma set_partial_equivalence_rel_on_set_iff_set_partial_equivalence_rel_on_pred [iff]:
  "partial_equivalence_rel_on (S :: set) (R :: set) \<longleftrightarrow> partial_equivalence_rel_on (mem_of S) R"
  by simp

overloading
  partial_equivalence_rel_set \<equiv> "partial_equivalence_rel :: set \<Rightarrow> bool"
begin
  definition "(partial_equivalence_rel_set :: set \<Rightarrow> bool) \<equiv>
    partial_equivalence_rel_on (\<top> :: set \<Rightarrow> bool)"
end

lemma partial_equivalence_rel_set_eq_partial_equivalence_rel_on:
  "(partial_equivalence_rel :: set \<Rightarrow> bool) = partial_equivalence_rel_on (\<top> :: set \<Rightarrow> bool)"
  unfolding partial_equivalence_rel_set_def ..

lemma partial_equivalence_rel_set_eq_partial_equivalence_rel_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: set \<Rightarrow> bool"
  shows "(partial_equivalence_rel :: set \<Rightarrow> bool) \<equiv> partial_equivalence_rel_on P"
  using assms by (simp add: partial_equivalence_rel_set_eq_partial_equivalence_rel_on)

lemma partial_equivalence_rel_set_iff_partial_equivalence_rel_pred [iff]:
  "partial_equivalence_rel S \<longleftrightarrow> partial_equivalence_rel (rel S)"
  unfolding partial_equivalence_rel_set_def by (urule refl)

lemma partial_equivalence_rel_set_iff_partial_equivalence_rel_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "partial_equivalence_rel S \<equiv> partial_equivalence_rel R"
  using assms by simp

end
