\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Symmetric\<close>
theory TSBinary_Relations_Symmetric
  imports
    HOTG.SBinary_Relations_Symmetric
    Soft_Types.TBinary_Relations_Symmetric
begin

overloading
  set_symmetric_on_type \<equiv> "symmetric_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_symmetric_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> symmetric_on (type_pred T)"
end

lemma set_symmetric_on_type_eq_set_symmetric_on_pred [simp]:
  "(symmetric_on (T :: set type) :: set \<Rightarrow> bool) = symmetric_on (type_pred T)"
  unfolding set_symmetric_on_type_def by simp

lemma set_symmetric_on_type_eq_set_symmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "symmetric_on (T :: set type) :: set \<Rightarrow> bool \<equiv> symmetric_on P"
  using assms by simp

lemma set_symmetric_on_type_iff_set_symmetric_on_pred [iff]:
  "symmetric_on (T :: set type) (R :: set) \<longleftrightarrow> symmetric_on (type_pred T) R"
  by simp


end