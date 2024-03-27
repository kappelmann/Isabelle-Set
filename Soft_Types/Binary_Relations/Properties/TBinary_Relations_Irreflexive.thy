\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Irreflexive\<close>
theory TBinary_Relations_Irreflexive
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Irreflexive
begin

overloading
  irreflexive_on_type \<equiv> "irreflexive_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "irreflexive_on_type (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    irreflexive_on (type_pred T)"
end

lemma irreflexive_on_type_eq_irreflexive_on_pred [simp]:
  "(irreflexive_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = irreflexive_on (type_pred T)"
  unfolding irreflexive_on_type_def by simp

lemma irreflexive_on_type_eq_irreflexive_on_pred_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "irreflexive_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> irreflexive_on P"
  using assms by simp

lemma irreflexive_on_type_iff_irreflexive_on_pred [iff]:
  "irreflexive_on (T :: 'a type) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> irreflexive_on (type_pred T) R"
  by simp


end