\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transitive\<close>
theory TSBinary_Relations_Transitive
  imports
    HOTG.HOTG_Binary_Relations_Transitive
    Soft_Types.Soft_Types_HOL_Base
begin

overloading
  set_transitive_on_type \<equiv> "transitive_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_transitive_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> transitive_on (of_type T)"
end

lemma set_transitive_on_type_eq_set_transitive_on_pred [simp]:
  "(transitive_on (T :: set type) :: set \<Rightarrow> bool) = transitive_on (of_type T)"
  unfolding set_transitive_on_type_def by simp

lemma set_transitive_on_type_eq_set_transitive_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "transitive_on (T :: set type) :: set \<Rightarrow> bool \<equiv> transitive_on P"
  using assms by simp

lemma set_transitive_on_type_iff_set_transitive_on_pred [iff]:
  "transitive_on (T :: set type) (R :: set) \<longleftrightarrow> transitive_on (of_type T) R"
  by simp

end