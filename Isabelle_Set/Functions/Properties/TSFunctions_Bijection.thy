\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Bijections\<close>
theory TSFunctions_Bijection
  imports
    HOTG.SFunctions_Bijection
    Soft_Types.TFunctions_Bijection
begin

overloading
  set_bijection_on_type \<equiv> "bijection_on :: set type \<Rightarrow> set type \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_bijection_on_type (S :: set type) (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv>
    bijection_on (type_pred S) (type_pred T)"
end

lemma set_bijection_on_type_eq_set_bijection_on_pred [simp]:
  "(bijection_on (S :: set type) (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool) =
    bijection_on (type_pred S) (type_pred T)"
  unfolding set_bijection_on_type_def by simp

lemma set_bijection_on_type_eq_set_bijection_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred S"
  and "Q \<equiv> type_pred T"
  shows "bijection_on (S :: set type) (T :: set type) :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> bijection_on P Q"
  using assms by simp

lemma set_bijection_on_type_iff_set_bijection_on_pred [iff]:
  "bijection_on (S :: set type) (T :: set type) (f :: set) (g :: set) \<longleftrightarrow>
    bijection_on (type_pred S) (type_pred T) f g"
  by simp


end