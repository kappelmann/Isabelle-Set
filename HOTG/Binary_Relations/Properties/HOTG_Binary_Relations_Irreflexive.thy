\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Irreflexive\<close>
theory HOTG_Binary_Relations_Irreflexive
  imports
    HOTG_Binary_Relations_Base
    Transport.Binary_Relations_Irreflexive
begin

overloading
  irreflexive_on_set \<equiv> "irreflexive_on :: set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
  set_irreflexive_on_pred \<equiv> "irreflexive_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_irreflexive_on_set \<equiv> "irreflexive_on :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "irreflexive_on_set (A :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<equiv>
    irreflexive_on (mem_of A) R"
  definition "set_irreflexive_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> irreflexive_on P (rel R)"
  definition "set_irreflexive_on_set (A :: set) (R :: set) \<equiv> irreflexive_on (mem_of A) R"
end

lemma irreflexive_on_set_eq_irreflexive_on_pred [simp]:
  "(irreflexive_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = irreflexive_on (mem_of S)"
  unfolding irreflexive_on_set_def by simp

lemma irreflexive_on_set_eq_irreflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "irreflexive_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> irreflexive_on P"
  using assms by simp

lemma irreflexive_on_set_iff_irreflexive_on_pred [iff]:
  "irreflexive_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> irreflexive_on (mem_of S) R"
  by simp

lemma set_irreflexive_on_pred_iff_irreflexive_on_pred [iff]:
  "irreflexive_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> irreflexive_on P (rel R)"
  unfolding set_irreflexive_on_pred_def by simp

lemma set_irreflexive_on_pred_iff_irreflexive_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  shows "irreflexive_on (P :: set \<Rightarrow> bool) S \<equiv> irreflexive_on P R"
  using assms by simp

lemma set_irreflexive_on_set_eq_set_irreflexive_on_pred [simp]:
  "(irreflexive_on (S :: set) :: set \<Rightarrow> bool) = irreflexive_on (mem_of S)"
  unfolding set_irreflexive_on_set_def by simp

lemma set_irreflexive_on_set_eq_set_irreflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "irreflexive_on (S :: set) :: set \<Rightarrow> bool \<equiv> irreflexive_on P"
  using assms by simp

lemma set_irreflexive_on_set_iff_set_irreflexive_on_pred [iff]:
  "irreflexive_on (S :: set) (R :: set) \<longleftrightarrow> irreflexive_on (mem_of S) R"
  by simp


end