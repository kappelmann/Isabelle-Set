\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Surjective\<close>
theory TSBinary_Relations_Surjective
  imports
    HOTG.HOTG_Binary_Relations_Surjective
    Soft_Types.Soft_Types_HOL_Base
begin

overloading
  set_rel_surjective_at_type \<equiv> "rel_surjective_at :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_rel_surjective_at_type (T :: set type) :: set \<Rightarrow> bool \<equiv> rel_surjective_at (of_type T)"
end

lemma set_rel_surjective_at_type_eq_set_rel_surjective_at_pred [simp]:
  "(rel_surjective_at (T :: set type) :: set \<Rightarrow> bool) = rel_surjective_at (of_type T)"
  unfolding set_rel_surjective_at_type_def by simp

lemma set_rel_surjective_at_type_eq_set_rel_surjective_at_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "rel_surjective_at (T :: set type) :: set \<Rightarrow> bool \<equiv> rel_surjective_at P"
  using assms by simp

lemma set_rel_surjective_at_type_iff_set_rel_surjective_at_pred [iff]:
  "rel_surjective_at (T :: set type) (R :: set) \<longleftrightarrow> rel_surjective_at (of_type T) R"
  by simp


end