\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Antisymmetric\<close>
theory TSBinary_Relations_Antisymmetric
  imports
    HOTG.SBinary_Relations_Antisymmetric
    Soft_Types.TBinary_Relations_Antisymmetric
begin

overloading
  set_antisymmetric_on_type \<equiv> "antisymmetric_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_antisymmetric_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> antisymmetric_on (type_pred T)"
end

lemma set_antisymmetric_on_type_eq_set_antisymmetric_on_pred [simp]:
  "(antisymmetric_on (T :: set type) :: set \<Rightarrow> bool) = antisymmetric_on (type_pred T)"
  unfolding set_antisymmetric_on_type_def by simp

lemma set_antisymmetric_on_type_eq_set_antisymmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "antisymmetric_on (T :: set type) :: set \<Rightarrow> bool \<equiv> antisymmetric_on P"
  using assms by simp

lemma set_antisymmetric_on_type_iff_set_antisymmetric_on_pred [iff]:
  "antisymmetric_on (T :: set type) (R :: set) \<longleftrightarrow> antisymmetric_on (type_pred T) R"
  by simp


end