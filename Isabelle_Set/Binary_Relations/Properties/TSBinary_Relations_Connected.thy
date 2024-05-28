\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Reflexive\<close>
theory TSBinary_Relations_Connected
  imports
    HOTG.HOTG_Binary_Relations_Connected
    Soft_Types.Soft_Types_HOL_Base
begin

overloading
  set_connected_on_type \<equiv> "connected_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_connected_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> connected_on (of_type T)"
end

lemma set_connected_on_type_eq_set_connected_on_pred [simp]:
  "(connected_on (T :: set type) :: set \<Rightarrow> bool) = connected_on (of_type T)"
  unfolding set_connected_on_type_def by simp

lemma set_connected_on_type_eq_set_connected_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "connected_on (T :: set type) :: set \<Rightarrow> bool \<equiv> connected_on P"
  using assms by simp

lemma set_connected_on_type_iff_set_connected_on_pred [iff]:
  "connected_on (T :: set type) (R :: set) \<longleftrightarrow> connected_on (of_type T) R"
  by simp


end