\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Reflexive\<close>
theory TBinary_Relations_Reflexive
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Reflexive
begin

overloading
  reflexive_on_type \<equiv> "reflexive_on :: 'a type \<Rightarrow> ('a type \<Rightarrow> 'a type \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "reflexive_on_type (T :: 'a type) :: ('a type \<Rightarrow> 'a type \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    reflexive_on (type_pred T)"
end

lemma reflexive_on_type_eq_reflexive_on_pred [simp]:
  "(reflexive_on (T :: 'a type) :: ('a type \<Rightarrow> 'a type \<Rightarrow> bool) \<Rightarrow> bool) = reflexive_on (type_pred T)"
  unfolding reflexive_on_type_def by simp

lemma reflexive_on_type_eq_reflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "reflexive_on (T :: 'a type) :: ('a type \<Rightarrow> 'a type \<Rightarrow> bool) \<Rightarrow> bool \<equiv> reflexive_on P"
  using assms by simp

lemma reflexive_on_type_iff_reflexive_on_pred [iff]:
  "reflexive_on (T :: 'a type) (R :: 'a type \<Rightarrow> 'a type \<Rightarrow> bool) \<longleftrightarrow> reflexive_on (type_pred T) R"
  by simp


end