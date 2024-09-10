\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Preorders\<close>
theory HOTG_Preorders
  imports
    HOTG_Binary_Relations_Reflexive
    HOTG_Binary_Relations_Transitive
    Transport.Preorders
begin

lemma preorder_on_set_eq_preorder_on_pred [simp]:
  "(preorder_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = preorder_on (mem_of S)"
  unfolding preorder_on_def by simp

lemma preorder_on_set_eq_preorder_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "preorder_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> preorder_on P"
  using assms by simp

lemma preorder_on_set_iff_preorder_on_pred [iff]:
  "preorder_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> preorder_on (mem_of S) R"
  by simp

lemma set_preorder_on_pred_iff_preorder_on_pred [iff]:
  "preorder_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> preorder_on P (rel R)"
  unfolding preorder_on_def by simp

lemma set_preorder_on_pred_iff_preorder_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "preorder_on P S \<equiv> preorder_on P' R"
  using assms by simp

lemma set_preorder_on_set_eq_set_preorder_on_pred [simp]:
  "(preorder_on (S :: set) :: set \<Rightarrow> bool) = preorder_on (mem_of S)"
  unfolding preorder_on_def by simp

lemma set_preorder_on_set_eq_set_preorder_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "preorder_on (S :: set) :: set \<Rightarrow> bool \<equiv> preorder_on P"
  using assms by simp

lemma set_preorder_on_set_iff_set_preorder_on_pred [iff]:
  "preorder_on (S :: set) (R :: set) \<longleftrightarrow> preorder_on (mem_of S) R"
  by simp

overloading
  preorder_set \<equiv> "preorder :: set \<Rightarrow> bool"
begin
  definition "(preorder_set :: set \<Rightarrow> bool) \<equiv> preorder_on (\<top> :: set \<Rightarrow> bool)"
end

lemma preorder_set_eq_preorder_on:
  "(preorder :: set \<Rightarrow> bool) = preorder_on (\<top> :: set \<Rightarrow> bool)"
  unfolding preorder_set_def ..

lemma preorder_set_eq_preorder_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: set \<Rightarrow> bool"
  shows "(preorder :: set \<Rightarrow> bool) \<equiv> preorder_on P"
  using assms by (simp add: preorder_set_eq_preorder_on)

lemma preorder_set_iff_preorder_pred [iff]: "preorder S \<longleftrightarrow> preorder (rel S)"
  unfolding preorder_set_def by (urule refl)

lemma preorder_set_iff_preorder_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "preorder S \<equiv> preorder R"
  using assms by simp

end
