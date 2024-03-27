\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Left Total\<close>
theory TBinary_Relations_Left_Total
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Left_Total
begin

overloading
  left_total_on_type \<equiv> "left_total_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "left_total_on_type (T :: 'a type) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    left_total_on (type_pred T)"
end

lemma left_total_on_type_eq_left_total_on_pred [simp]:
  "(left_total_on (T :: 'a type) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = left_total_on (type_pred T)"
  unfolding left_total_on_type_def by simp

lemma left_total_on_type_eq_left_total_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "left_total_on (T :: 'a type) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> left_total_on P"
  using assms by simp

lemma left_total_on_type_iff_left_total_on_pred [iff]:
  "left_total_on (T :: 'a type) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> left_total_on (type_pred T) R"
  by simp


end