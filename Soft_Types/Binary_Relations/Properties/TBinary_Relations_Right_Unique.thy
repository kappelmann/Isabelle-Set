\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Right Unique\<close>
theory TBinary_Relations_Right_Unique
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Right_Unique
begin

overloading
  right_unique_on_type \<equiv> "right_unique_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "right_unique_on_type (T :: 'a type) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    right_unique_on (of_type T)"
end

lemma right_unique_on_type_eq_right_unique_on_pred [simp]:
  "(right_unique_on (T :: 'a type) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = right_unique_on (of_type T)"
  unfolding right_unique_on_type_def by simp

lemma right_unique_on_type_eq_right_unique_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "right_unique_on (T :: 'a type) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> right_unique_on P"
  using assms by simp

lemma right_unique_on_type_iff_right_unique_on_pred [iff]:
  "right_unique_on (T :: 'a type) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> right_unique_on (of_type T) R"
  by simp


overloading
  right_unique_at_type \<equiv> "right_unique_at :: 'a type \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "right_unique_at_type (T :: 'a type) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
    right_unique_at (of_type T)"
end

lemma right_unique_at_type_eq_right_unique_at_pred [simp]:
  "(right_unique_at (T :: 'a type) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = right_unique_at (of_type T)"
  unfolding right_unique_at_type_def by simp

lemma right_unique_at_type_eq_right_unique_at_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "right_unique_at (T :: 'a type) :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> right_unique_at P"
  using assms by simp

lemma right_unique_at_type_iff_right_unique_at_pred [iff]:
  "right_unique_at (T :: 'a type) (R :: 'b \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> right_unique_at (of_type T) R"
  by simp


end
