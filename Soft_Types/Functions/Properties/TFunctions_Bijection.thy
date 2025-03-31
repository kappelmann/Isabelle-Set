\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Bijections\<close>
theory TFunctions_Bijection
  imports
    Soft_Types_HOL
    Transport.Functions_Bijection
begin

definition "bijection_on_type (A :: 'a type) (B :: 'b type) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool \<equiv>
  bijection_on (of_type A) (of_type B)"
adhoc_overloading bijection_on \<rightleftharpoons> bijection_on_type

lemma bijection_on_type_eq_bijection_on_pred [simp]:
  "bijection_on A B = bijection_on (of_type A) (of_type B)"
  unfolding bijection_on_type_def by simp

lemma bijection_on_type_eq_bijection_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type A"
  and "Q \<equiv> of_type B"
  shows "bijection_on A B \<equiv> bijection_on P Q"
  using assms by simp

lemma bijection_on_type_iff_bijection_on_pred [iff]:
  "bijection_on A B f g \<longleftrightarrow> bijection_on (of_type A) (of_type B) f g"
  by simp

end