\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Antisymmetric\<close>
theory TBinary_Relations_Antisymmetric
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Antisymmetric
begin

overloading
  antisymmetric_on_type \<equiv> "antisymmetric_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "antisymmetric_on_type (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    antisymmetric_on (type_pred T)"
end

lemma antisymmetric_on_type_eq_antisymmetric_on_pred [simp]:
  "(antisymmetric_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = antisymmetric_on (type_pred T)"
  unfolding antisymmetric_on_type_def by simp

lemma antisymmetric_on_type_eq_antisymmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "antisymmetric_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> antisymmetric_on P"
  using assms by simp

lemma antisymmetric_on_type_iff_antisymmetric_on_pred [iff]:
  "antisymmetric_on (T :: 'a type) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> antisymmetric_on (type_pred T) R"
  by simp


end