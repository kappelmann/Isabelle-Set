\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Asymmetric\<close>
theory TSBinary_Relations_Asymmetric
  imports
    HOTG.HOTG_Binary_Relations_Asymmetric
    Soft_Types.Soft_Types_HOL_Base
begin

overloading
  set_asymmetric_on_type \<equiv> "asymmetric_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_asymmetric_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> asymmetric_on (of_type T)"
end

lemma set_asymmetric_on_type_eq_set_asymmetric_on_pred [simp]:
  "(asymmetric_on (T :: set type) :: set \<Rightarrow> bool) = asymmetric_on (of_type T)"
  unfolding set_asymmetric_on_type_def by simp

lemma set_asymmetric_on_type_eq_set_asymmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "asymmetric_on (T :: set type) :: set \<Rightarrow> bool \<equiv> asymmetric_on P"
  using assms by simp

lemma set_asymmetric_on_type_iff_set_asymmetric_on_pred [iff]:
  "asymmetric_on (T :: set type) (R :: set) \<longleftrightarrow> asymmetric_on (of_type T) R"
  by simp


end