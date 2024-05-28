\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Reflexive\<close>
theory TSBinary_Relations_Reflexive
  imports
    HOTG.HOTG_Binary_Relations_Reflexive
    Soft_Types.TBinary_Relations_Reflexive
begin

overloading
  set_reflexive_on_type \<equiv> "reflexive_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_reflexive_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> reflexive_on (of_type T)"
end

lemma set_reflexive_on_type_eq_set_reflexive_on_pred [simp]:
  "(reflexive_on (T :: set type) :: set \<Rightarrow> bool) = reflexive_on (of_type T)"
  unfolding set_reflexive_on_type_def by simp

lemma set_reflexive_on_type_eq_set_reflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "reflexive_on (T :: set type) :: set \<Rightarrow> bool \<equiv> reflexive_on P"
  using assms by simp

lemma set_reflexive_on_type_iff_set_reflexive_on_pred [iff]:
  "reflexive_on (T :: set type) (R :: set) \<longleftrightarrow> reflexive_on (of_type T) R"
  by simp


end