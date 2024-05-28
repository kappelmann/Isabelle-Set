\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Transitive\<close>
theory TBinary_Relations_Transitive
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Transitive
begin

overloading
  transitive_on_type \<equiv> "transitive_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "transitive_on_type (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    transitive_on (of_type T)"
end

lemma transitive_on_type_eq_transitive_on_pred [simp]:
  "(transitive_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = transitive_on (of_type T)"
  unfolding transitive_on_type_def by simp

lemma transitive_on_type_eq_transitive_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "transitive_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> transitive_on P"
  using assms by simp

lemma transitive_on_type_iff_transitive_on_pred [iff]:
  "transitive_on (T :: 'a type) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> transitive_on (of_type T) R"
  by simp

end