\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Well-Orders\<close>
theory HOTG_Wellorders
  imports
    HOTG_Binary_Relations_Wellfounded
    HOTG_Strict_Linear_Orders
    Transport.Wellorders
begin

lemma wellorder_on_set_eq_wellorder_on_pred [simp]:
  "(wellorder_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = wellorder_on (mem_of S)"
  unfolding wellorder_on_def by simp

lemma wellorder_on_set_eq_wellorder_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "wellorder_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> wellorder_on P"
  using assms by simp

lemma wellorder_on_set_iff_wellorder_on_pred [iff]:
  "wellorder_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> wellorder_on (mem_of S) R"
  by simp

lemma set_wellorder_on_pred_iff_wellorder_on_pred [iff]:
  "wellorder_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> wellorder_on P (rel R)"
  unfolding wellorder_on_def by simp

lemma set_wellorder_on_pred_iff_wellorder_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "wellorder_on P S \<equiv> wellorder_on P' R"
  using assms by simp

lemma set_wellorder_on_set_eq_set_wellorder_on_pred [simp]:
  "(wellorder_on (S :: set) :: set \<Rightarrow> bool) = wellorder_on (mem_of S)"
  unfolding wellorder_on_def by simp

lemma set_wellorder_on_set_eq_set_wellorder_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "wellorder_on (S :: set) :: set \<Rightarrow> bool \<equiv> wellorder_on P"
  using assms by simp

lemma set_wellorder_on_set_iff_set_wellorder_on_pred [iff]:
  "wellorder_on (S :: set) (R :: set) \<longleftrightarrow> wellorder_on (mem_of S) R"
  by simp

overloading
  wellorder_set \<equiv> "wellorder :: set \<Rightarrow> bool"
begin
  definition "(wellorder_set :: set \<Rightarrow> bool) \<equiv> wellorder_on (\<top> :: set \<Rightarrow> bool)"
end

lemma wellorder_set_eq_wellorder_on:
  "(wellorder :: set \<Rightarrow> bool) = wellorder_on (\<top> :: set \<Rightarrow> bool)"
  unfolding wellorder_set_def ..

lemma wellorder_set_eq_wellorder_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: set \<Rightarrow> bool"
  shows "(wellorder :: set \<Rightarrow> bool) \<equiv> wellorder_on P"
  using assms by (simp add: wellorder_set_eq_wellorder_on)

lemma wellorder_set_iff_wellorder_pred [iff]: "wellorder S \<longleftrightarrow> wellorder (rel S)"
  unfolding wellorder_set_def by (urule refl)

lemma wellorder_set_iff_wellorder_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "wellorder S \<equiv> wellorder R"
  using assms by simp

end