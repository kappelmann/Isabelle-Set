\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Equivalence Relations\<close>
theory HOTG_Equivalence_Relations
  imports
    HOTG_Binary_Relations_Reflexive
    HOTG_Partial_Equivalence_Relations
    Transport.Equivalence_Relations
begin

lemma equivalence_rel_on_set_eq_equivalence_rel_on_pred [simp]:
  "(equivalence_rel_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = equivalence_rel_on (mem_of S)"
  unfolding equivalence_rel_on_def by simp

lemma equivalence_rel_on_set_eq_equivalence_rel_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "equivalence_rel_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> equivalence_rel_on P"
  using assms by simp

lemma equivalence_rel_on_set_iff_equivalence_rel_on_pred [iff]:
  "equivalence_rel_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> equivalence_rel_on (mem_of S) R"
  by simp

lemma set_equivalence_rel_on_pred_iff_equivalence_rel_on_pred [iff]:
  "equivalence_rel_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> equivalence_rel_on P (rel R)"
  unfolding equivalence_rel_on_def by simp

lemma set_equivalence_rel_on_pred_iff_equivalence_rel_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "equivalence_rel_on P S \<equiv> equivalence_rel_on P' R"
  using assms by simp

lemma set_equivalence_rel_on_set_eq_set_equivalence_rel_on_pred [simp]:
  "(equivalence_rel_on (S :: set) :: set \<Rightarrow> bool) = equivalence_rel_on (mem_of S)"
  unfolding equivalence_rel_on_def by simp

lemma set_equivalence_rel_on_set_eq_set_equivalence_rel_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "equivalence_rel_on (S :: set) :: set \<Rightarrow> bool \<equiv> equivalence_rel_on P"
  using assms by simp

lemma set_equivalence_rel_on_set_iff_set_equivalence_rel_on_pred [iff]:
  "equivalence_rel_on (S :: set) (R :: set) \<longleftrightarrow> equivalence_rel_on (mem_of S) R"
  by simp

overloading
  equivalence_rel_set \<equiv> "equivalence_rel :: set \<Rightarrow> bool"
begin
  definition "(equivalence_rel_set :: set \<Rightarrow> bool) \<equiv>
    equivalence_rel_on (\<top> :: set \<Rightarrow> bool)"
end

lemma equivalence_rel_set_eq_equivalence_rel_on:
  "(equivalence_rel :: set \<Rightarrow> bool) = equivalence_rel_on (\<top> :: set \<Rightarrow> bool)"
  unfolding equivalence_rel_set_def ..

lemma equivalence_rel_set_eq_equivalence_rel_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: set \<Rightarrow> bool"
  shows "(equivalence_rel :: set \<Rightarrow> bool) \<equiv> equivalence_rel_on P"
  using assms by (simp add: equivalence_rel_set_eq_equivalence_rel_on)

lemma equivalence_rel_set_iff_equivalence_rel_pred [iff]:
  "equivalence_rel S \<longleftrightarrow> equivalence_rel (rel S)"
  unfolding equivalence_rel_set_def by (urule refl)

lemma equivalence_rel_set_iff_equivalence_rel_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "equivalence_rel S \<equiv> equivalence_rel R"
  using assms by simp

end


