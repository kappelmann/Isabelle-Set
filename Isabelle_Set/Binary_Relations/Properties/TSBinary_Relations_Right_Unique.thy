\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Right Unique\<close>
theory TSBinary_Relations_Right_Unique
  imports
    HOTG.HOTG_Binary_Relations_Right_Unique
    Soft_Types.Soft_Types_HOL_Base
begin

overloading
  set_right_unique_on_type \<equiv> "right_unique_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_right_unique_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> right_unique_on (of_type T)"
end

lemma set_right_unique_on_type_eq_set_right_unique_on_pred [simp]:
  "(right_unique_on (T :: set type) :: set \<Rightarrow> bool) = right_unique_on (of_type T)"
  unfolding set_right_unique_on_type_def by simp

lemma set_right_unique_on_type_eq_set_right_unique_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "right_unique_on (T :: set type) :: set \<Rightarrow> bool \<equiv> right_unique_on P"
  using assms by simp

lemma set_right_unique_on_type_iff_set_right_unique_on_pred [iff]:
  "right_unique_on (T :: set type) (R :: set) \<longleftrightarrow> right_unique_on (of_type T) R"
  by simp


overloading
  set_right_unique_at_type \<equiv> "right_unique_at :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_right_unique_at_type (T :: set type) :: set \<Rightarrow> bool \<equiv> right_unique_at (of_type T)"
end

lemma set_right_unique_at_type_eq_set_right_unique_at_pred [simp]:
  "(right_unique_at (T :: set type) :: set \<Rightarrow> bool) = right_unique_at (of_type T)"
  unfolding set_right_unique_at_type_def by simp

lemma set_right_unique_at_type_eq_set_right_unique_at_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "right_unique_at (T :: set type) :: set \<Rightarrow> bool \<equiv> right_unique_at P"
  using assms by simp

lemma set_right_unique_at_type_iff_set_right_unique_at_pred [iff]:
  "right_unique_at (T :: set type) (R :: set) \<longleftrightarrow> right_unique_at (of_type T) R"
  by simp


end
