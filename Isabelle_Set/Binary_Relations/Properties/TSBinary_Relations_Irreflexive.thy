\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Irreflexive\<close>
theory TSBinary_Relations_Irreflexive
  imports
    HOTG.HOTG_Binary_Relations_Irreflexive
    Soft_Types.Soft_Types_HOL_Base
begin

overloading
  set_irreflexive_on_type \<equiv> "irreflexive_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_irreflexive_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> irreflexive_on (of_type T)"
end

lemma set_irreflexive_on_type_eq_set_irreflexive_on_pred [simp]:
  "(irreflexive_on (T :: set type) :: set \<Rightarrow> bool) = irreflexive_on (of_type T)"
  unfolding set_irreflexive_on_type_def by simp

lemma set_irreflexive_on_type_eq_set_irreflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "irreflexive_on (T :: set type) :: set \<Rightarrow> bool \<equiv> irreflexive_on P"
  using assms by simp

lemma set_irreflexive_on_type_iff_set_irreflexive_on_pred [iff]:
  "irreflexive_on (T :: set type) (R :: set) \<longleftrightarrow> irreflexive_on (of_type T) R"
  by simp


end