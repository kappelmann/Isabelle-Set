\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Inverse\<close>
theory TSFunctions_Inverse
  imports
    HOTG.HOTG_Functions_Inverse
    Soft_Types.Soft_Types_HOL_Base
begin

overloading
  set_inverse_on_type \<equiv> "inverse_on :: set type \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_inverse_on_type (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> inverse_on (of_type T)"
end

lemma set_inverse_on_type_eq_set_inverse_on_pred [simp]:
  "(inverse_on (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool) = inverse_on (of_type T)"
  unfolding set_inverse_on_type_def by simp

lemma set_inverse_on_type_eq_set_inverse_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "inverse_on (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> inverse_on P"
  using assms by simp

lemma set_inverse_on_type_iff_set_inverse_on_pred [iff]:
  "inverse_on (T :: set type) (f :: set) (g :: set) \<longleftrightarrow> inverse_on (of_type T) f g"
  by simp

end