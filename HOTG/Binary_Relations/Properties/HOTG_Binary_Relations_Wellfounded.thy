\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Well-Founded\<close>
theory HOTG_Binary_Relations_Wellfounded
  imports
    HOTG_Binary_Relations_Base
    Transport.Binary_Relations_Wellfounded
begin

overloading
  wellfounded_on_set \<equiv> "wellfounded_on :: set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
  set_wellfounded_on_pred \<equiv> "wellfounded_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_wellfounded_on_set \<equiv> "wellfounded_on :: set \<Rightarrow> set \<Rightarrow> bool"
  wellfounded_set \<equiv> "wellfounded :: set \<Rightarrow> bool"
begin
  definition "wellfounded_on_set (A :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<equiv>
    wellfounded_on (mem_of A) R"
  definition "set_wellfounded_on_pred (P :: set \<Rightarrow> bool) (R :: set) \<equiv> wellfounded_on P (rel R)"
  definition "set_wellfounded_on_set (A :: set) (R :: set) \<equiv> wellfounded_on (mem_of A) R"
  definition "wellfounded_set :: set \<Rightarrow> bool \<equiv> wellfounded_on (\<top> :: set \<Rightarrow> bool)"
end

lemma wellfounded_on_set_eq_wellfounded_on_pred [simp]:
  "(wellfounded_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = wellfounded_on (mem_of S)"
  unfolding wellfounded_on_set_def by simp

lemma wellfounded_on_set_eq_wellfounded_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "wellfounded_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> wellfounded_on P"
  using assms by simp

lemma wellfounded_on_set_iff_wellfounded_on_pred [iff]:
  "wellfounded_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> wellfounded_on (mem_of S) R"
  by simp

lemma set_wellfounded_on_pred_iff_wellfounded_on_pred [iff]:
  "wellfounded_on (P :: set \<Rightarrow> bool) R \<longleftrightarrow> wellfounded_on P (rel R)"
  unfolding set_wellfounded_on_pred_def by simp

lemma set_wellfounded_on_pred_iff_wellfounded_on_pred_uhint [uhint]:
  assumes "R \<equiv> rel S"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "wellfounded_on P S \<equiv> wellfounded_on P' R"
  using assms by simp

lemma set_wellfounded_on_set_eq_set_wellfounded_on_pred [simp]:
  "(wellfounded_on (S :: set) :: set \<Rightarrow> bool) = wellfounded_on (mem_of S)"
  unfolding set_wellfounded_on_set_def by simp

lemma set_wellfounded_on_set_eq_set_wellfounded_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "wellfounded_on (S :: set) :: set \<Rightarrow> bool \<equiv> wellfounded_on P"
  using assms by simp

lemma set_wellfounded_on_set_iff_set_wellfounded_on_pred [iff]:
  "wellfounded_on (S :: set) (R :: set) \<longleftrightarrow> wellfounded_on (mem_of S) R"
  by simp

lemma wellfounded_set_eq_set_wellfounded_on:
  "(wellfounded :: set \<Rightarrow> _) = wellfounded_on (\<top> :: set \<Rightarrow> bool)"
  unfolding wellfounded_set_def ..

lemma wellfounded_set_eq_set_wellfounded_on_uhint [uhint]:
  "P \<equiv> (\<top> :: set \<Rightarrow> bool) \<Longrightarrow> (wellfounded :: set \<Rightarrow> _) \<equiv> wellfounded_on P"
  by (simp add: wellfounded_set_eq_set_wellfounded_on)

lemma wellfounded_set_iff_wellfounded_pred [iff]:
  "wellfounded S \<longleftrightarrow> wellfounded (rel S)"
  unfolding wellfounded_set_eq_set_wellfounded_on by (urule refl)

lemma wellfounded_set_eq_wellfounded_pred_uhint [uhint]:
  "R \<equiv> rel A \<Longrightarrow> wellfounded A \<equiv> wellfounded R"
  by simp

end
