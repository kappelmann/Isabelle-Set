\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Functions on Relations\<close>
theory TBinary_Relation_Functions
  imports
    Transport.Binary_Relation_Functions
    Soft_Types_HOL
begin

overloading
  rel_restrict_left_type \<equiv> "rel_restrict_left :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a type \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
  rel_restrict_right_type \<equiv> "rel_restrict_right :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b type \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
begin
  definition "rel_restrict_left_type (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (T :: 'a type) \<equiv>
    rel_restrict_left R (type_pred T)"
  definition "rel_restrict_right_type (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (T :: 'b type) \<equiv>
    rel_restrict_right R (type_pred T)"
end

lemma rel_restrict_left_type_eq_rel_restrict_left [simp]:
  "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>T :: 'a type\<^esub> = R\<restriction>\<^bsub>type_pred T\<^esub>"
  unfolding rel_restrict_left_type_def by simp

lemma rel_restrict_left_type_eq_rel_restrict_left_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>T :: 'a type\<^esub> \<equiv> R\<restriction>\<^bsub>P\<^esub>"
  using assms by simp

lemma rel_restrict_right_type_eq_rel_restrict_right [simp]:
  "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<upharpoonleft>\<^bsub>T :: 'b type\<^esub> = R\<upharpoonleft>\<^bsub>type_pred T\<^esub>"
  unfolding rel_restrict_right_type_def by simp

lemma rel_restrict_right_type_eq_rel_restrict_right_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  shows "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<upharpoonleft>\<^bsub>T :: 'b type\<^esub> \<equiv> R\<upharpoonleft>\<^bsub>P\<^esub>"
  using assms by simp


end
