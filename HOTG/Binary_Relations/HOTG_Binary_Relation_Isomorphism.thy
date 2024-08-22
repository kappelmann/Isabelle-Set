theory HOTG_Binary_Relation_Isomorphism
  imports 
    Binary_Relation_Isomorphism 
    HOTG_Basics
begin

overloading
  rel_isomorphism_set \<equiv> "rel_isomorphism :: set \<Rightarrow> set \<Rightarrow> 
    (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
begin
  definition "rel_isomorphism_set (A :: set) (B :: set) 
    (R :: set \<Rightarrow> set \<Rightarrow> bool) (S :: set \<Rightarrow> set \<Rightarrow> bool) (\<phi> :: set \<Rightarrow> set) (\<psi> :: set \<Rightarrow> set) 
    \<equiv> rel_isomorphism (mem_of A) (mem_of B) R S \<phi> \<psi>"
end

lemma rel_isomorphism_set_eq_rel_isomorphism_pred [simp]:
  "(rel_isomorphism (A :: set) (B :: set) 
    :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool) 
  = rel_isomorphism (mem_of A) (mem_of B)"
  unfolding rel_isomorphism_set_def by simp

lemma rel_isomorphism_set_eq_rel_isomorphism_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A" "Q \<equiv> mem_of B"
  shows "rel_isomorphism (A :: set) (B :: set) 
      :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool
    \<equiv> rel_isomorphism P Q"
  using assms by simp

lemma rel_isomorphism_set_iff_rel_isomorphism_pred [iff]:
  "rel_isomorphism (A :: set) (B :: set) 
    (R :: set \<Rightarrow> set \<Rightarrow> bool) (S :: set \<Rightarrow> set \<Rightarrow> bool) (\<phi> :: set \<Rightarrow> set) (\<psi> :: set \<Rightarrow> set) 
  \<longleftrightarrow> rel_isomorphism (mem_of A) (mem_of B) R S \<phi> \<psi>"
  by simp

overloading
  rel_isomorphic_set \<equiv> 
    "rel_isomorphic :: set \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_isomorphic_set 
    (A :: set) (B :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) (S :: set \<Rightarrow> set \<Rightarrow> bool)
    \<equiv> rel_isomorphic (mem_of A) (mem_of B) R S"
end

lemma rel_isomorphic_set_eq_rel_isomorphic_pred [simp]:
  "(rel_isomorphic (A :: set) (B :: set) 
    :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) 
  = rel_isomorphic (mem_of A) (mem_of B)"
  unfolding rel_isomorphic_set_def by simp

lemma rel_isomorphic_set_eq_rel_isomorphic_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A" "Q \<equiv> mem_of B"
  shows "rel_isomorphic (A :: set) (B :: set) 
      :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool
    \<equiv> rel_isomorphic P Q"
  using assms by simp

lemma rel_isomorphic_set_iff_rel_isomorphic_pred [iff]:
  "rel_isomorphic (A :: set) (B :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) (S :: set \<Rightarrow> set \<Rightarrow> bool) 
  \<longleftrightarrow> rel_isomorphic (mem_of A) (mem_of B) R S"
  by simp

end