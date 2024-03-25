\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Typed Binary Relations\<close>
theory TBinary_Relations
  imports
    Transport.Restricted_Equality
    HOTG.Axioms
    Soft_Types.Soft_Types_HOL
begin

overloading
  rel_restrict_left_set \<equiv> "restrict_left :: (set \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> 'b \<Rightarrow> bool"
  rel_restrict_left_type \<equiv> "restrict_left :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a type \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  rel_restrict_right_set \<equiv> "restrict_right :: ('a \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> 'a \<Rightarrow> set \<Rightarrow> bool"
  rel_restrict_right_type \<equiv> "restrict_right :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b type \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
begin
  definition "rel_restrict_left_set (R :: set \<Rightarrow> 'b \<Rightarrow> bool) (S :: set) \<equiv>
    restrict_left R (mem_of S)"
  definition "rel_restrict_left_type (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (T :: 'a type) \<equiv>
    restrict_left R (type_pred T)"
  definition "rel_restrict_right_set (R :: 'a \<Rightarrow> set \<Rightarrow> bool) (S :: set) \<equiv>
    restrict_right R (mem_of S)"
  definition "rel_restrict_right_type (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (T :: 'b type) \<equiv>
    restrict_right R (type_pred T)"
end

lemma rel_restrict_left_set_eq_restrict_left [simp]:
  "restrict_left (R :: set \<Rightarrow> 'b \<Rightarrow> bool) (S :: set) = restrict_left R (mem_of S)"
  unfolding rel_restrict_left_set_def by simp

lemma rel_restrict_left_type_eq_restrict_left [simp]:
  "restrict_left (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (T :: 'a type) = restrict_left R (type_pred T)"
  unfolding rel_restrict_left_type_def by simp

lemma rel_restrict_right_type_eq_restrict_right [simp]:
  "restrict_right (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (T :: 'b type) = restrict_right R (type_pred T)"
  unfolding rel_restrict_right_type_def by simp

lemma rel_restrict_right_set_eq_restrict_right [simp]:
  "restrict_right (R :: 'a \<Rightarrow> set \<Rightarrow> bool) (S :: set) = restrict_right R (mem_of S)"
  unfolding rel_restrict_right_set_def by simp


end