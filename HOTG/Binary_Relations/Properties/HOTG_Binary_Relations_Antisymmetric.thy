\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Antisymmetric\<close>
theory HOTG_Binary_Relations_Antisymmetric
  imports HOTG_Binary_Relations_Base
begin

overloading
  antisymmetric_on_set \<equiv> "antisymmetric_on :: set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
  set_antisymmetric_on_pred \<equiv> "antisymmetric_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_antisymmetric_on_set \<equiv> "antisymmetric_on :: set \<Rightarrow> set \<Rightarrow> bool"
  antisymmetric_set \<equiv> "antisymmetric :: set \<Rightarrow> bool"
begin
  definition "antisymmetric_on_set (A :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<equiv>
    antisymmetric_on (mem_of A) R"
  definition "set_antisymmetric_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> antisymmetric_on P (rel R)"
  definition "set_antisymmetric_on_set (A :: set) (R :: set) \<equiv> antisymmetric_on (mem_of A) R"
  definition "antisymmetric_set :: set \<Rightarrow> bool \<equiv> antisymmetric_on (\<top> :: set \<Rightarrow> bool)"
end

lemma antisymmetric_on_set_eq_antisymmetric_on_pred [simp]:
  "(antisymmetric_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = antisymmetric_on (mem_of S)"
  unfolding antisymmetric_on_set_def by simp

lemma antisymmetric_on_set_eq_antisymmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "antisymmetric_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> antisymmetric_on P"
  using assms by simp

lemma antisymmetric_on_set_iff_antisymmetric_on_pred [iff]:
  "antisymmetric_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> antisymmetric_on (mem_of S) R"
  by simp

lemma set_antisymmetric_on_pred_iff_antisymmetric_on_pred [iff]:
  "antisymmetric_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> antisymmetric_on P (rel R)"
  unfolding set_antisymmetric_on_pred_def by simp

lemma set_antisymmetric_on_pred_iff_antisymmetric_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "antisymmetric_on P S \<equiv> antisymmetric_on P' R"
  using assms by simp

lemma set_antisymmetric_on_set_eq_set_antisymmetric_on_pred [simp]:
  "(antisymmetric_on (S :: set) :: set \<Rightarrow> bool) = antisymmetric_on (mem_of S)"
  unfolding set_antisymmetric_on_set_def by simp

lemma set_antisymmetric_on_set_eq_set_antisymmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "antisymmetric_on (S :: set) :: set \<Rightarrow> bool \<equiv> antisymmetric_on P"
  using assms by simp

lemma set_antisymmetric_on_set_iff_set_antisymmetric_on_pred [iff]:
  "antisymmetric_on (S :: set) (R :: set) \<longleftrightarrow> antisymmetric_on (mem_of S) R"
  by simp

lemma antisymmetric_set_eq_set_antisymmetric_on:
  "(antisymmetric :: set \<Rightarrow> _) = antisymmetric_on (\<top> :: set \<Rightarrow> bool)"
  unfolding antisymmetric_set_def ..

lemma antisymmetric_set_eq_set_antisymmetric_on_uhint [uhint]:
  "P \<equiv> (\<top> :: set \<Rightarrow> bool) \<Longrightarrow> (antisymmetric :: set \<Rightarrow> _) \<equiv> antisymmetric_on P"
  by (simp add: antisymmetric_set_eq_set_antisymmetric_on)

lemma antisymmetric_set_iff_antisymmetric_pred [iff]:
  "antisymmetric S \<longleftrightarrow> antisymmetric (rel S)"
  unfolding antisymmetric_set_eq_set_antisymmetric_on by (urule refl)

lemma antisymmetric_set_eq_antisymmetric_pred_uhint [uhint]:
  "R \<equiv> rel A \<Longrightarrow> antisymmetric A \<equiv> antisymmetric R"
  by simp

end