\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Connected\<close>
theory TBinary_Relations_Connected
  imports
    Soft_Types_HOL
    Transport.Binary_Relations_Connected
begin

overloading
  connected_on_type \<equiv> "connected_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "connected_on_type (T :: 'a type) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<equiv> connected_on (of_type T) R"
end

lemma connected_on_type_eq_connected_on_pred [simp]:
  "(connected_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = connected_on (of_type T)"
  unfolding connected_on_type_def by simp

lemma connected_on_type_eq_connected_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "connected_on (T :: 'a type) :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool \<equiv> connected_on P"
  using assms by simp

lemma connected_on_type_iff_connected_on_pred [iff]:
  "connected_on (T :: 'a type) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> connected_on (of_type T) R"
  by simp


end