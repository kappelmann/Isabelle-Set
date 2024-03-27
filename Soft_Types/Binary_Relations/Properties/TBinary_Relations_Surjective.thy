\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Surjective\<close>
theory TBinary_Relations_Surjective
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Surjective
begin

overloading
  rel_surjective_at_type \<equiv> "rel_surjective_at :: 'a type \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_surjective_at_type (T :: 'a type) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    rel_surjective_at (type_pred T)"
end

lemma rel_surjective_at_type_eq_rel_surjective_at_pred [simp]:
  "(rel_surjective_at (T :: 'a type) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = rel_surjective_at (type_pred T)"
  unfolding rel_surjective_at_type_def by simp

lemma rel_surjective_at_type_eq_rel_surjective_at_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "rel_surjective_at (T :: 'a type) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_surjective_at P"
  using assms by simp

lemma rel_surjective_at_type_iff_rel_surjective_at_pred [iff]:
  "rel_surjective_at (T :: 'a type) (R :: 'b \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> rel_surjective_at (type_pred T) R"
  by simp


end