\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Symmetric\<close>
theory TBinary_Relations_Symmetric
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Symmetric
begin

overloading
  symmetric_on_type \<equiv> "symmetric_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "symmetric_on_type (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    symmetric_on (type_pred T)"
end

lemma symmetric_on_type_eq_symmetric_on_pred [simp]:
  "(symmetric_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = symmetric_on (type_pred T)"
  unfolding symmetric_on_type_def by simp

lemma symmetric_on_type_eq_symmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "symmetric_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> symmetric_on P"
  using assms by simp

lemma symmetric_on_type_iff_symmetric_on_pred [iff]:
  "symmetric_on (T :: 'a type) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> symmetric_on (type_pred T) R"
  by simp


end