\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Reflexive\<close>
theory TSBinary_Relations_Reflexive
  imports
    HOTG.SBinary_Relations_Reflexive
    Soft_Types.TBinary_Relations_Reflexive
begin

overloading
  set_reflexive_on_type \<equiv> "reflexive_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_reflexive_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> reflexive_on (type_pred T)"
end

lemma set_reflexive_on_type_eq_set_reflexive_on_pred [simp]:
  "(reflexive_on (T :: set type) :: set \<Rightarrow> bool) = reflexive_on (type_pred T)"
  unfolding set_reflexive_on_type_def by simp

lemma set_reflexive_on_type_eq_set_reflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "reflexive_on (T :: set type) :: set \<Rightarrow> bool \<equiv> reflexive_on P"
  using assms by simp

lemma set_reflexive_on_type_iff_set_reflexive_on_pred [iff]:
  "reflexive_on (T :: set type) (R :: set) \<longleftrightarrow> reflexive_on (type_pred T) R"
  by simp


end