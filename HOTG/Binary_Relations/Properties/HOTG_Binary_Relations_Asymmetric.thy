\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Antisymmetric\<close>
theory HOTG_Binary_Relations_Asymmetric
  imports
    HOTG_Binary_Relations_Base
    Transport.Binary_Relations_Asymmetric
begin

overloading
  asymmetric_on_set \<equiv> "asymmetric_on :: set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
  set_asymmetric_on_pred \<equiv> "asymmetric_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_asymmetric_on_set \<equiv> "asymmetric_on :: set \<Rightarrow> set \<Rightarrow> bool"
  asymmetric_set \<equiv> "asymmetric :: set \<Rightarrow> bool"
begin
  definition "asymmetric_on_set (A :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<equiv> asymmetric_on (mem_of A) R"
  definition "set_asymmetric_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> asymmetric_on P (rel R)"
  definition "set_asymmetric_on_set (A :: set) (R :: set) \<equiv> asymmetric_on (mem_of A) R"
  definition "asymmetric_set :: set \<Rightarrow> bool \<equiv> asymmetric_on (\<top> :: set \<Rightarrow> bool)"
end

lemma asymmetric_on_set_eq_asymmetric_on_pred [simp]:
  "(asymmetric_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = asymmetric_on (mem_of S)"
  unfolding asymmetric_on_set_def by simp

lemma asymmetric_on_set_eq_asymmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "asymmetric_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> asymmetric_on P"
  using assms by simp

lemma asymmetric_on_set_iff_asymmetric_on_pred [iff]:
  "asymmetric_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> asymmetric_on (mem_of S) R"
  by simp

lemma set_asymmetric_on_pred_iff_asymmetric_on_pred [iff]:
  "asymmetric_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> asymmetric_on P (rel R)"
  unfolding set_asymmetric_on_pred_def by simp

lemma set_asymmetric_on_pred_iff_asymmetric_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "asymmetric_on P S \<equiv> asymmetric_on P' R"
  using assms by simp

lemma set_asymmetric_on_set_eq_set_asymmetric_on_pred [simp]:
  "(asymmetric_on (S :: set) :: set \<Rightarrow> bool) = asymmetric_on (mem_of S)"
  unfolding set_asymmetric_on_set_def by simp

lemma set_asymmetric_on_set_eq_set_asymmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "asymmetric_on (S :: set) :: set \<Rightarrow> bool \<equiv> asymmetric_on P"
  using assms by simp

lemma set_asymmetric_on_set_iff_set_asymmetric_on_pred [iff]:
  "asymmetric_on (S :: set) (R :: set) \<longleftrightarrow> asymmetric_on (mem_of S) R"
  by simp

lemma asymmetric_set_eq_set_asymmetric_on:
  "(asymmetric :: set \<Rightarrow> _) = asymmetric_on (\<top> :: set \<Rightarrow> bool)"
  unfolding asymmetric_set_def ..

lemma asymmetric_set_eq_set_asymmetric_on_uhint [uhint]:
  "P \<equiv> (\<top> :: set \<Rightarrow> bool) \<Longrightarrow> (asymmetric :: set \<Rightarrow> _) \<equiv> asymmetric_on P"
  by (simp add: asymmetric_set_eq_set_asymmetric_on)

lemma asymmetric_set_iff_asymmetric_pred [iff]:
  "asymmetric S \<longleftrightarrow> asymmetric (rel S)"
  unfolding asymmetric_set_eq_set_asymmetric_on by (urule refl)

lemma asymmetric_set_eq_asymmetric_pred_uhint [uhint]:
  "R \<equiv> rel A \<Longrightarrow> asymmetric A \<equiv> asymmetric R"
  by simp


end