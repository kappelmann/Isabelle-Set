\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Reflexive\<close>
theory HOTG_Binary_Relations_Reflexive
  imports
    HOTG_Binary_Relations_Base
    Transport.Binary_Relations_Reflexive
begin

overloading
  reflexive_on_set \<equiv> "reflexive_on :: set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
  set_reflexive_on_pred \<equiv> "reflexive_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_reflexive_on_set \<equiv> "reflexive_on :: set \<Rightarrow> set \<Rightarrow> bool"
  reflexive_set \<equiv> "reflexive :: set \<Rightarrow> bool"
begin
  definition "reflexive_on_set (A :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> reflexive_on (mem_of A)"
  definition "set_reflexive_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> reflexive_on P (rel R)"
  definition "set_reflexive_on_set (A :: set) (R :: set) \<equiv> reflexive_on (mem_of A) R"
  definition "reflexive_set :: set \<Rightarrow> bool \<equiv> reflexive_on (\<top> :: set \<Rightarrow> bool)"
end

lemma reflexive_on_set_eq_reflexive_on_pred [simp]:
  "(reflexive_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = reflexive_on (mem_of S)"
  unfolding reflexive_on_set_def by simp

lemma reflexive_on_set_eq_reflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "reflexive_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> reflexive_on P"
  using assms by simp

lemma reflexive_on_set_iff_reflexive_on_pred [iff]:
  "reflexive_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> reflexive_on (mem_of S) R"
  by simp

lemma set_reflexive_on_pred_iff_reflexive_on_pred [iff]:
  "reflexive_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> reflexive_on P (rel R)"
  unfolding set_reflexive_on_pred_def by simp

lemma set_reflexive_on_pred_iff_reflexive_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "reflexive_on P S \<equiv> reflexive_on P' R"
  using assms by simp

lemma set_reflexive_on_set_eq_set_reflexive_on_pred [simp]:
  "(reflexive_on (S :: set) :: set \<Rightarrow> bool) = reflexive_on (mem_of S)"
  unfolding set_reflexive_on_set_def by simp

lemma set_reflexive_on_set_eq_set_reflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "reflexive_on (S :: set) :: set \<Rightarrow> bool \<equiv> reflexive_on P"
  using assms by simp

lemma set_reflexive_on_set_iff_set_reflexive_on_pred [iff]:
  "reflexive_on (S :: set) (R :: set) \<longleftrightarrow> reflexive_on (mem_of S) R"
  by simp

lemma reflexive_set_eq_set_reflexive_on:
  "(reflexive :: set \<Rightarrow> _) = reflexive_on (\<top> :: set \<Rightarrow> bool)"
  unfolding reflexive_set_def ..

lemma reflexive_set_eq_set_reflexive_on_uhint [uhint]:
  "P \<equiv> (\<top> :: set \<Rightarrow> bool) \<Longrightarrow> (reflexive :: set \<Rightarrow> _) \<equiv> reflexive_on P"
  by (simp add: reflexive_set_eq_set_reflexive_on)

lemma reflexive_set_iff_reflexive_pred [iff]:
  "reflexive S \<longleftrightarrow> reflexive (rel S)"
  unfolding reflexive_set_eq_set_reflexive_on by (urule refl)

lemma reflexive_set_eq_reflexive_pred_uhint [uhint]:
  "R \<equiv> rel A \<Longrightarrow> reflexive A \<equiv> reflexive R"
  by simp

end