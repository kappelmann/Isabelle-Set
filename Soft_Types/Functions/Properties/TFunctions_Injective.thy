\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Injective\<close>
theory TFunctions_Injective
  imports
    Soft_Types.Soft_Types_HOL
    Transport.Functions_Injective
begin

overloading
  injective_on_type \<equiv> "injective_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "injective_on_type (T :: 'a type) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> injective_on (type_pred T)"
end

lemma injective_on_type_eq_injective_on_pred [simp]:
  "(injective_on (T :: 'a type) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) = injective_on (type_pred T)"
  unfolding injective_on_type_def by simp

lemma injective_on_type_eq_injective_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "injective_on (T :: 'a type) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> injective_on P"
  using assms by simp

lemma injective_on_type_iff_injective_on_pred [iff]:
  "injective_on (T :: 'a type) (f :: 'a \<Rightarrow> 'b) \<longleftrightarrow> injective_on (type_pred T) f"
  by simp


end