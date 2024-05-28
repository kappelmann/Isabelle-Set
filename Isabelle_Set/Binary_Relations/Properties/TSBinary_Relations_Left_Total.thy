\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Left Total\<close>
theory TSBinary_Relations_Left_Total
  imports
    HOTG.HOTG_Binary_Relations_Left_Total
    Soft_Types.Soft_Types_HOL_Base
begin

overloading
  set_left_total_on_type \<equiv> "left_total_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_left_total_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> left_total_on (of_type T)"
end

lemma set_left_total_on_type_eq_set_left_total_on_pred [simp]:
  "(left_total_on (T :: set type) :: set \<Rightarrow> bool) = left_total_on (of_type T)"
  unfolding set_left_total_on_type_def by simp

lemma set_left_total_on_type_eq_set_left_total_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "left_total_on (T :: set type) :: set \<Rightarrow> bool \<equiv> left_total_on P"
  using assms by simp

lemma set_left_total_on_type_iff_set_left_total_on_pred [iff]:
  "left_total_on (T :: set type) (R :: set) \<longleftrightarrow> left_total_on (of_type T) R"
  by simp


end