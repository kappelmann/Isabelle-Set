\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Well-Founded\<close>
theory TBinary_Relations_Wellfounded
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Wellfounded
begin

overloading
  wellfounded_on_type \<equiv> "wellfounded_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "wellfounded_on_type (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    wellfounded_on (of_type T)"
end

lemma wellfounded_on_type_eq_wellfounded_on_pred [simp]:
  "(wellfounded_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = wellfounded_on (of_type T)"
  unfolding wellfounded_on_type_def by simp

lemma wellfounded_on_type_eq_wellfounded_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "wellfounded_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> wellfounded_on P"
  using assms by simp

lemma wellfounded_on_type_iff_wellfounded_on_pred [iff]:
  "wellfounded_on (T :: 'a type) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> wellfounded_on (of_type T) R"
  by simp

end