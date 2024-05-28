\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Injective\<close>
theory TSBinary_Relations_Injective
  imports
    HOTG.HOTG_Binary_Relations_Injective
    Soft_Types.Soft_Types_HOL_Base
begin

overloading
  set_rel_injective_on_type \<equiv> "rel_injective_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_rel_injective_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> rel_injective_on (of_type T)"
end

lemma set_rel_injective_on_type_eq_set_rel_injective_on_pred [simp]:
  "(rel_injective_on (T :: set type) :: set \<Rightarrow> bool) = rel_injective_on (of_type T)"
  unfolding set_rel_injective_on_type_def by simp

lemma set_rel_injective_on_type_eq_set_rel_injective_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "rel_injective_on (T :: set type) :: set \<Rightarrow> bool \<equiv> rel_injective_on P"
  using assms by simp

lemma set_rel_injective_on_type_iff_set_rel_injective_on_pred [iff]:
  "rel_injective_on (T :: set type) (R :: set) \<longleftrightarrow> rel_injective_on (of_type T) R"
  by simp


overloading
  set_rel_injective_at_type \<equiv> "rel_injective_at :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_rel_injective_at_type (T :: set type) :: set \<Rightarrow> bool \<equiv> rel_injective_at (of_type T)"
end

lemma set_rel_injective_at_type_eq_set_rel_injective_at_pred [simp]:
  "(rel_injective_at (T :: set type) :: set \<Rightarrow> bool) = rel_injective_at (of_type T)"
  unfolding set_rel_injective_at_type_def by simp

lemma set_rel_injective_at_type_eq_set_rel_injective_at_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "rel_injective_at (T :: set type) :: set \<Rightarrow> bool \<equiv> rel_injective_at P"
  using assms by simp

lemma set_rel_injective_at_type_iff_set_rel_injective_at_pred [iff]:
  "rel_injective_at (T :: set type) (R :: set) \<longleftrightarrow> rel_injective_at (of_type T) R"
  by simp


end