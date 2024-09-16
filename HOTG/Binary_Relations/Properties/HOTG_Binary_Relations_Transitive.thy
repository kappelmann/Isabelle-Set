\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transitive\<close>
theory HOTG_Binary_Relations_Transitive
  imports
    HOTG_Binary_Relations_Base
    Transport.Binary_Relations_Transitive
begin

overloading
  transitive_on_set \<equiv> "transitive_on :: set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
  set_transitive_on_pred \<equiv> "transitive_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_transitive_on_set \<equiv> "transitive_on :: set \<Rightarrow> set \<Rightarrow> bool"
  transitive_set \<equiv> "transitive :: set \<Rightarrow> bool"
begin
  definition "transitive_on_set (A :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<equiv>
    transitive_on (mem_of A) R"
  definition "set_transitive_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> transitive_on P (rel R)"
  definition "set_transitive_on_set (A :: set) (R :: set) \<equiv> transitive_on (mem_of A) R"
  definition "transitive_set :: set \<Rightarrow> bool \<equiv> transitive_on (\<top> :: set \<Rightarrow> bool)"
end

lemma transitive_on_set_eq_transitive_on_pred [simp]:
  "(transitive_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = transitive_on (mem_of S)"
  unfolding transitive_on_set_def by simp

lemma transitive_on_set_eq_transitive_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "transitive_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> transitive_on P"
  using assms by simp

lemma transitive_on_set_iff_transitive_on_pred [iff]:
  "transitive_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> transitive_on (mem_of S) R"
  by simp

lemma set_transitive_on_pred_iff_transitive_on_pred [iff]:
  "transitive_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> transitive_on P (rel R)"
  unfolding set_transitive_on_pred_def by simp

lemma set_transitive_on_pred_iff_transitive_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "transitive_on P S \<equiv> transitive_on P' R"
  using assms by simp

lemma set_transitive_on_set_eq_set_transitive_on_pred [simp]:
  "(transitive_on (S :: set) :: set \<Rightarrow> bool) = transitive_on (mem_of S)"
  unfolding set_transitive_on_set_def by simp

lemma set_transitive_on_set_eq_set_transitive_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "transitive_on (S :: set) :: set \<Rightarrow> bool \<equiv> transitive_on P"
  using assms by simp

lemma set_transitive_on_set_iff_set_transitive_on_pred [iff]:
  "transitive_on (S :: set) (R :: set) \<longleftrightarrow> transitive_on (mem_of S) R"
  by simp

lemma transitive_set_eq_set_transitive_on:
  "(transitive :: set \<Rightarrow> _) = transitive_on (\<top> :: set \<Rightarrow> bool)"
  unfolding transitive_set_def ..

lemma transitive_set_eq_set_transitive_on_uhint [uhint]:
  "P \<equiv> (\<top> :: set \<Rightarrow> bool) \<Longrightarrow> (transitive :: set \<Rightarrow> _) \<equiv> transitive_on P"
  by (simp add: transitive_set_eq_set_transitive_on)

lemma transitive_set_iff_transitive_pred [iff]:
  "transitive S \<longleftrightarrow> transitive (rel S)"
  unfolding transitive_set_eq_set_transitive_on by (urule refl)

lemma transitive_set_eq_transitive_pred_uhint [uhint]:
  "R \<equiv> rel A \<Longrightarrow> transitive A \<equiv> transitive R"
  by simp


end