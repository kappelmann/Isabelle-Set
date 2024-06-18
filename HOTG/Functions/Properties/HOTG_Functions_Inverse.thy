\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Inverse\<close>
theory HOTG_Functions_Inverse
  imports
    HOTG_Bounded_Definite_Description
    HOTG_Functions_Evaluation
    Transport.Functions_Inverse
begin

definition "the_inverse_on_set A \<equiv> the_inverse_on (mem_of A)"
adhoc_overloading the_inverse_on the_inverse_on_set

lemma the_inverse_on_set_eq_the_inverse_on_pred [simp]:
  "the_inverse_on A = the_inverse_on (mem_of A)"
  unfolding the_inverse_on_set_def by simp

lemma the_inverse_on_set_eq_the_inverse_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "the_inverse_on (A :: set) \<equiv> the_inverse_on P"
  using assms by simp

overloading
  inverse_on_set \<equiv> "inverse_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool"
  set_inverse_on_pred \<equiv> "inverse_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  set_inverse_on_set \<equiv> "inverse_on :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "inverse_on_set (A :: set) :: (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool \<equiv> inverse_on (mem_of A)"
  definition "set_inverse_on_pred (P :: set \<Rightarrow> bool) (f :: set) (g :: set) \<equiv>
    inverse_on P (eval f) (eval g)"
  definition "set_inverse_on_set (A :: set) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> inverse_on (mem_of A)"
end

lemma inverse_on_set_eq_inverse_on_pred [simp]:
  "(inverse_on (A :: set) :: (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool) = inverse_on (mem_of A)"
  unfolding inverse_on_set_def by simp

lemma inverse_on_set_eq_inverse_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "inverse_on (A :: set) :: (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool \<equiv> inverse_on P"
  using assms by simp

lemma inverse_on_set_iff_inverse_on_pred [iff]:
  "inverse_on (A :: set) (f :: set \<Rightarrow> 'a) (g :: 'a \<Rightarrow> set) \<longleftrightarrow> inverse_on (mem_of A) f g"
  by simp

lemma set_inverse_on_pred_iff_inverse_on_pred [iff]:
  "inverse_on (P :: set \<Rightarrow> bool) (f :: set) (g :: set) \<longleftrightarrow> inverse_on P (eval f) (eval g)"
  unfolding set_inverse_on_pred_def by simp

lemma set_inverse_on_pred_eq_inverse_on_pred_uhint [uhint]:
  assumes "f' \<equiv> eval f"
  and "g' \<equiv> eval g"
  and "P \<equiv> P'"
  shows "inverse_on (P :: set \<Rightarrow> bool) (f :: set) (g :: set) \<equiv> inverse_on P' f' g'"
  using assms by simp

lemma set_inverse_on_set_eq_set_inverse_on_pred [simp]:
  "(inverse_on (A :: set) :: set \<Rightarrow> set \<Rightarrow> bool) = inverse_on (mem_of A)"
  unfolding set_inverse_on_set_def by simp

lemma set_inverse_on_set_eq_set_inverse_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "inverse_on (A :: set) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> inverse_on P"
  using assms by simp

lemma set_inverse_on_set_iff_set_inverse_on_pred [iff]:
  "inverse_on (A :: set) (f :: set) (g :: set) \<longleftrightarrow> inverse_on (mem_of A) f g"
  by simp

end