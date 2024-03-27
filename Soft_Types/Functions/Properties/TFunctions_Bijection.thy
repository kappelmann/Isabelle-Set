\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Bijections\<close>
theory TFunctions_Bijection
  imports
    Soft_Types.Soft_Types_HOL
    Transport.Functions_Bijection
begin

overloading
  bijection_on_type \<equiv> "bijection_on :: 'a type \<Rightarrow> 'b type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "bijection_on_type (S :: 'a type) (T :: 'b type) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool \<equiv>
    bijection_on (type_pred S) (type_pred T)"
end

lemma bijection_on_type_eq_bijection_on_pred [simp]:
  "(bijection_on (S :: 'a type) (T :: 'b type) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool) =
    bijection_on (type_pred S) (type_pred T)"
  unfolding bijection_on_type_def by simp

lemma bijection_on_type_eq_bijection_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred S"
  and "Q \<equiv> type_pred T"
  shows "bijection_on (S :: 'a type) (T :: 'b type) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool \<equiv> bijection_on P Q"
  using assms by simp

lemma bijection_on_type_iff_bijection_on_pred [iff]:
  "bijection_on (S :: 'a type) (T :: 'b type) (f :: 'a \<Rightarrow> 'b) (g :: 'b \<Rightarrow> 'a) \<longleftrightarrow>
    bijection_on (type_pred S) (type_pred T) f g"
  by simp


end