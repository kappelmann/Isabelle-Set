\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Injective\<close>
theory TBinary_Relations_Injective
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Injective
begin

overloading
  rel_injective_on_type \<equiv> "rel_injective_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_injective_on_type (T :: 'a type) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    rel_injective_on (type_pred T)"
end

lemma rel_injective_on_type_eq_rel_injective_on_pred [simp]:
  "(rel_injective_on (T :: 'a type) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = rel_injective_on (type_pred T)"
  unfolding rel_injective_on_type_def by simp

lemma rel_injective_on_type_eq_rel_injective_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "rel_injective_on (T :: 'a type) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_injective_on P"
  using assms by simp

lemma rel_injective_on_type_iff_rel_injective_on_pred [iff]:
  "rel_injective_on (T :: 'a type) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> rel_injective_on (type_pred T) R"
  by simp


overloading
  rel_injective_at_type \<equiv> "rel_injective_at :: 'a type \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_injective_at_type (T :: 'a type) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    rel_injective_at (type_pred T)"
end

lemma rel_injective_at_type_eq_rel_injective_at_pred [simp]:
  "(rel_injective_at (T :: 'a type) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = rel_injective_at (type_pred T)"
  unfolding rel_injective_at_type_def by simp

lemma rel_injective_at_type_eq_rel_injective_at_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "rel_injective_at (T :: 'a type) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_injective_at P"
  using assms by simp

lemma rel_injective_at_type_iff_rel_injective_at_pred [iff]:
  "rel_injective_at (T :: 'a type) (R :: 'b \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> rel_injective_at (type_pred T) R"
  by simp


end