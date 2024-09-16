\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Well-Founded\<close>
theory TSBinary_Relations_Wellfounded
  imports
    HOTG.HOTG_Binary_Relations_Wellfounded
    Soft_Types.Soft_Types_HOL_Base
begin

overloading
  set_wellfounded_on_type \<equiv> "wellfounded_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_wellfounded_on_type (T :: set type) :: set \<Rightarrow> bool \<equiv> wellfounded_on (of_type T)"
end

lemma set_wellfounded_on_type_eq_set_wellfounded_on_pred [simp]:
  "(wellfounded_on (T :: set type) :: set \<Rightarrow> bool) = wellfounded_on (of_type T)"
  unfolding set_wellfounded_on_type_def by simp

lemma set_wellfounded_on_type_eq_set_wellfounded_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "wellfounded_on (T :: set type) :: set \<Rightarrow> bool \<equiv> wellfounded_on P"
  using assms by simp

lemma set_wellfounded_on_type_iff_set_wellfounded_on_pred [iff]:
  "wellfounded_on (T :: set type) (R :: set) \<longleftrightarrow> wellfounded_on (of_type T) R"
  by simp

end