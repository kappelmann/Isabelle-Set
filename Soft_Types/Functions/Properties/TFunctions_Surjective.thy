\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Surjective\<close>
theory TFunctions_Surjective
  imports
    Soft_Types.Soft_Types_HOL
    Transport.Functions_Surjective
begin

overloading
  surjective_at_type \<equiv> "surjective_at :: 'b type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "surjective_at_type (T :: 'b type) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> surjective_at (of_type T)"
end

lemma surjective_at_type_eq_surjective_at_pred [simp]:
  "(surjective_at (T :: 'b type) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) = surjective_at (of_type T)"
  unfolding surjective_at_type_def by simp

lemma surjective_at_type_eq_surjective_at_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "surjective_at (T :: 'b type) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> surjective_at P"
  using assms by simp

lemma surjective_at_type_iff_surjective_at_pred [iff]:
  "surjective_at (T :: 'b type) (f :: 'a \<Rightarrow> 'b) \<longleftrightarrow> surjective_at (of_type T) f"
  by simp


end