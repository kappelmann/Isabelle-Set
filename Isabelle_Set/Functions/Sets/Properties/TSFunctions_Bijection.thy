\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Bijections\<close>
theory TSFunctions_Bijection
  imports
    HOTG.HOTG_Functions_Bijection
    Soft_Types.Soft_Types_HOL_Base
begin

definition "set_bijection_on_type (S :: set type) (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv>
  bijection_on (of_type S) (of_type T)"
adhoc_overloading bijection_on set_bijection_on_type

lemma set_bijection_on_type_eq_set_bijection_on_pred [simp]:
  "(bijection_on (S :: set type) (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool) =
    bijection_on (of_type S) (of_type T)"
  unfolding set_bijection_on_type_def by simp

lemma set_bijection_on_type_eq_set_bijection_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type S"
  and "Q \<equiv> of_type T"
  shows "bijection_on (S :: set type) (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> bijection_on P Q"
  using assms by simp

lemma set_bijection_on_type_iff_set_bijection_on_pred [iff]:
  "bijection_on (S :: set type) (T :: set type) (f :: set) (g :: set) \<longleftrightarrow>
    bijection_on (of_type S) (of_type T) f g"
  by simp


end