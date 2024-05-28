\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Reflexive\<close>
theory TBinary_Relations_Reflexive
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Reflexive
begin

overloading
  reflexive_on_type \<equiv> "reflexive_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "reflexive_on_type (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    reflexive_on (of_type T)"
end

lemma reflexive_on_type_eq_reflexive_on_pred [simp]:
  "(reflexive_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = reflexive_on (of_type T)"
  unfolding reflexive_on_type_def by simp

lemma reflexive_on_type_eq_reflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "reflexive_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> reflexive_on P"
  using assms by simp

lemma reflexive_on_type_iff_reflexive_on_pred [iff]:
  "reflexive_on (T :: 'a type) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> reflexive_on (of_type T) R"
  by simp


end