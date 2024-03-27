\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Inverse\<close>
theory TSFunctions_Inverse
  imports
    HOTG.SFunctions_Inverse
    Soft_Types.TFunctions_Inverse
begin

overloading
  set_inverse_on_type \<equiv> "inverse_on :: set type \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_inverse_on_type (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> inverse_on (type_pred T)"
end

lemma set_inverse_on_type_eq_set_inverse_on_pred [simp]:
  "(inverse_on (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool) = inverse_on (type_pred T)"
  unfolding set_inverse_on_type_def by simp

lemma set_inverse_on_type_eq_set_inverse_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "inverse_on (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> inverse_on P"
  using assms by simp

lemma set_inverse_on_type_iff_set_inverse_on_pred [iff]:
  "inverse_on (T :: set type) (f :: set) (g :: set) \<longleftrightarrow> inverse_on (type_pred T) f g"
  by simp

end