\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Left Total\<close>
theory HOTG_Binary_Relations_Left_Total
  imports
    HOTG_Binary_Relations_Base
    Transport.Binary_Relations_Left_Total
begin

overloading
  left_total_on_set \<equiv> "left_total_on :: set \<Rightarrow> (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  set_left_total_on_pred \<equiv> "left_total_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_left_total_on_set \<equiv> "left_total_on :: set \<Rightarrow> set \<Rightarrow> bool"
  left_total_set \<equiv> "left_total :: set \<Rightarrow> bool"
begin
  definition "left_total_on_set (A :: set) (R :: set \<Rightarrow> 'a \<Rightarrow> bool) \<equiv>
    left_total_on (mem_of A) R"
  definition "set_left_total_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> left_total_on P (rel R)"
  definition "set_left_total_on_set (A :: set) (R :: set) \<equiv> left_total_on (mem_of A) R"
  definition "left_total_set :: set \<Rightarrow> bool \<equiv> left_total_on (\<top> :: set \<Rightarrow> bool)"
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
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "left_total_on P S \<equiv> left_total_on P' R"
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

lemma left_total_set_eq_set_left_total_on:
  "(left_total :: set \<Rightarrow> _) = left_total_on (\<top> :: set \<Rightarrow> bool)"
  unfolding left_total_set_def ..

lemma left_total_set_eq_set_left_total_on_uhint [uhint]:
  "P \<equiv> (\<top> :: set \<Rightarrow> bool) \<Longrightarrow> (left_total :: set \<Rightarrow> _) \<equiv> left_total_on P"
  by (simp add: left_total_set_eq_set_left_total_on)

lemma left_total_set_iff_left_total_pred [iff]:
  "left_total S \<longleftrightarrow> left_total (rel S)"
  unfolding left_total_set_eq_set_left_total_on by (urule refl)

lemma left_total_set_eq_left_total_pred_uhint [uhint]:
  "R \<equiv> rel A \<Longrightarrow> left_total A \<equiv> left_total R"
  by simp

end