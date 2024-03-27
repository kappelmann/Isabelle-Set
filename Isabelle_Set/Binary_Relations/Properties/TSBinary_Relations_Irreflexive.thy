\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Irreflexive\<close>
theory TSBinary_Relations_Irreflexive
  imports
    HOTG.SBinary_Relations_Irreflexive
    Soft_Types.TBinary_Relations_Irreflexive
begin

overloading
  set_irreflexive_on_type \<equiv> "irreflexive_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_irreflexive_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> irreflexive_on (type_pred T)"
end

lemma set_irreflexive_on_type_eq_set_irreflexive_on_pred [simp]:
  "(irreflexive_on (T :: set type) :: set \<Rightarrow> bool) = irreflexive_on (type_pred T)"
  unfolding set_irreflexive_on_type_def by simp

lemma set_irreflexive_on_type_eq_set_irreflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "irreflexive_on (T :: set type) :: set \<Rightarrow> bool \<equiv> irreflexive_on P"
  using assms by simp

lemma set_irreflexive_on_type_iff_set_irreflexive_on_pred [iff]:
  "irreflexive_on (T :: set type) (R :: set) \<longleftrightarrow> irreflexive_on (type_pred T) R"
  by simp


end