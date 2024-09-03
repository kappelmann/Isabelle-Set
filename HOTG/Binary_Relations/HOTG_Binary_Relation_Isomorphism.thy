theory HOTG_Binary_Relation_Isomorphism
  imports 
    Binary_Relation_Isomorphism 
    HOTG_Basics
begin

definition rel_isomorphism_on_set :: "set \<Rightarrow> set \<Rightarrow> 
  (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool" where 
"rel_isomorphism_on_set A B = rel_isomorphism_on (mem_of A) (mem_of B)"
adhoc_overloading rel_isomorphism_on rel_isomorphism_on_set

lemma rel_isomorphism_on_set_eq_rel_isomorphism_on_pred [simp]:
  "(rel_isomorphism_on (A :: set) (B :: set) 
      :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool) 
    = rel_isomorphism_on (mem_of A) (mem_of B)"
  unfolding rel_isomorphism_on_set_def by simp

lemma rel_isomorphism_on_set_eq_rel_isomorphism_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A" "Q \<equiv> mem_of B"
  shows "rel_isomorphism_on (A :: set) (B :: set) 
      :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool
    \<equiv> rel_isomorphism_on P Q"
  using assms by simp

lemma rel_isomorphism_on_set_iff_rel_isomorphism_on_pred [iff]:
  "rel_isomorphism_on A B 
      (R :: set \<Rightarrow> set \<Rightarrow> bool) (S :: set \<Rightarrow> set \<Rightarrow> bool) (\<phi> :: set \<Rightarrow> set) (\<psi> :: set \<Rightarrow> set) 
    \<longleftrightarrow> rel_isomorphism_on (mem_of A) (mem_of B) R S \<phi> \<psi>"
  by simp


definition rel_isomorphic_on_set :: 
  "set \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool" where 
"rel_isomorphic_on_set A B = rel_isomorphic_on (mem_of A) (mem_of B)"
adhoc_overloading rel_isomorphic_on rel_isomorphic_on_set

lemma rel_isomorphic_on_set_eq_rel_isomorphic_on_pred [simp]:
  "(rel_isomorphic_on (A :: set) (B :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) 
    = rel_isomorphic_on (mem_of A) (mem_of B)"
  unfolding rel_isomorphic_on_set_def by simp

lemma rel_isomorphic_on_set_eq_rel_isomorphic_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A" "Q \<equiv> mem_of B"
  shows "rel_isomorphic_on (A :: set) (B :: set) 
      :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool
    \<equiv> rel_isomorphic_on P Q"
  using assms by simp

lemma rel_isomorphic_on_set_iff_rel_isomorphic_on_pred [iff]:
  "rel_isomorphic_on A B (R :: set \<Rightarrow> set \<Rightarrow> bool) (S :: set \<Rightarrow> set \<Rightarrow> bool) 
    \<longleftrightarrow> rel_isomorphic_on (mem_of A) (mem_of B) R S"
  by simp

end