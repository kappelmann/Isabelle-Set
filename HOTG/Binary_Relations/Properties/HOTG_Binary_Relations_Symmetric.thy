\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Symmetric\<close>
theory HOTG_Binary_Relations_Symmetric
  imports
    HOTG_Binary_Relations_Base
    Transport.Binary_Relations_Symmetric
begin

overloading
  symmetric_on_set \<equiv> "symmetric_on :: set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
  set_symmetric_on_pred \<equiv> "symmetric_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_symmetric_on_set \<equiv> "symmetric_on :: set \<Rightarrow> set \<Rightarrow> bool"
  symmetric_set \<equiv> "symmetric :: set \<Rightarrow> bool"
begin
  definition "symmetric_on_set (A :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<equiv>
    symmetric_on (mem_of A) R"
  definition "set_symmetric_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> symmetric_on P (rel R)"
  definition "set_symmetric_on_set (A :: set) (R :: set) \<equiv> symmetric_on (mem_of A) R"
  definition "symmetric_set :: set \<Rightarrow> bool \<equiv> symmetric_on (\<top> :: set \<Rightarrow> bool)"
end

lemma symmetric_on_set_eq_symmetric_on_pred [simp]:
  "(symmetric_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = symmetric_on (mem_of S)"
  unfolding symmetric_on_set_def by simp

lemma symmetric_on_set_eq_symmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "symmetric_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> symmetric_on P"
  using assms by simp

lemma symmetric_on_set_iff_symmetric_on_pred [iff]:
  "symmetric_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> symmetric_on (mem_of S) R"
  by simp

lemma set_symmetric_on_pred_iff_symmetric_on_pred [iff]:
  "symmetric_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> symmetric_on P (rel R)"
  unfolding set_symmetric_on_pred_def by simp

lemma set_symmetric_on_pred_iff_symmetric_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "symmetric_on P S \<equiv> symmetric_on P' R"
  using assms by simp

lemma set_symmetric_on_set_eq_set_symmetric_on_pred [simp]:
  "(symmetric_on (S :: set) :: set \<Rightarrow> bool) = symmetric_on (mem_of S)"
  unfolding set_symmetric_on_set_def by simp

lemma set_symmetric_on_set_eq_set_symmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "symmetric_on (S :: set) :: set \<Rightarrow> bool \<equiv> symmetric_on P"
  using assms by simp

lemma set_symmetric_on_set_iff_set_symmetric_on_pred [iff]:
  "symmetric_on (S :: set) (R :: set) \<longleftrightarrow> symmetric_on (mem_of S) R"
  by simp

lemma symmetric_set_eq_set_symmetric_on:
  "(symmetric :: set \<Rightarrow> _) = symmetric_on (\<top> :: set \<Rightarrow> bool)"
  unfolding symmetric_set_def ..

lemma symmetric_set_eq_set_symmetric_on_uhint [uhint]:
  "P \<equiv> (\<top> :: set \<Rightarrow> bool) \<Longrightarrow> (symmetric :: set \<Rightarrow> _) \<equiv> symmetric_on P"
  by (simp add: symmetric_set_eq_set_symmetric_on)

lemma symmetric_set_iff_symmetric_pred [iff]:
  "symmetric S \<longleftrightarrow> symmetric (rel S)"
  unfolding symmetric_set_eq_set_symmetric_on by (urule refl)

lemma symmetric_set_eq_symmetric_pred_uhint [uhint]:
  "R \<equiv> rel A \<Longrightarrow> symmetric A \<equiv> symmetric R"
  by simp

end