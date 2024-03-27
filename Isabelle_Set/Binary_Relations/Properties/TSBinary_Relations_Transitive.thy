\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transitive\<close>
theory TSBinary_Relations_Transitive
  imports
    HOTG.SBinary_Relations_Transitive
    Soft_Types.TBinary_Relations_Transitive
begin

overloading
  set_transitive_on_type \<equiv> "transitive_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_transitive_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> transitive_on (type_pred T)"
end

lemma set_transitive_on_type_eq_set_transitive_on_pred [simp]:
  "(transitive_on (T :: set type) :: set \<Rightarrow> bool) = transitive_on (type_pred T)"
  unfolding set_transitive_on_type_def by simp

lemma set_transitive_on_type_eq_set_transitive_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "transitive_on (T :: set type) :: set \<Rightarrow> bool \<equiv> transitive_on P"
  using assms by simp

lemma set_transitive_on_type_iff_set_transitive_on_pred [iff]:
  "transitive_on (T :: set type) (R :: set) \<longleftrightarrow> transitive_on (type_pred T) R"
  by simp

end