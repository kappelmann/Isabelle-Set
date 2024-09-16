\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Asymmetric\<close>
theory TBinary_Relations_Asymmetric
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Asymmetric
begin

overloading
  asymmetric_on_type \<equiv> "asymmetric_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "asymmetric_on_type (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    asymmetric_on (of_type T)"
end

lemma asymmetric_on_type_eq_asymmetric_on_pred [simp]:
  "(asymmetric_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = asymmetric_on (of_type T)"
  unfolding asymmetric_on_type_def by simp

lemma asymmetric_on_type_eq_asymmetric_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "asymmetric_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> asymmetric_on P"
  using assms by simp

lemma asymmetric_on_type_iff_asymmetric_on_pred [iff]:
  "asymmetric_on (T :: 'a type) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> asymmetric_on (of_type T) R"
  by simp


end