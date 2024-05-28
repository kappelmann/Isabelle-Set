\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Inverse\<close>
theory TFunctions_Inverse
  imports
    Soft_Types.Soft_Types_HOL
    Transport.Functions_Inverse
begin

overloading
  inverse_on_type \<equiv> "inverse_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "inverse_on_type (T :: 'a type) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool \<equiv>
    inverse_on (of_type T)"
end

lemma inverse_on_type_eq_inverse_on_pred [simp]:
  "(inverse_on (T :: 'a type) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool) = inverse_on (of_type T)"
  unfolding inverse_on_type_def by simp

lemma inverse_on_type_eq_inverse_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "inverse_on (T :: 'a type) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool \<equiv> inverse_on P"
  using assms by simp

lemma inverse_on_type_iff_inverse_on_pred [iff]:
  "inverse_on (T :: 'a type) (f :: 'a \<Rightarrow> 'b) (g :: 'b \<Rightarrow> 'a) \<longleftrightarrow> inverse_on (of_type T) f g"
  by simp

end