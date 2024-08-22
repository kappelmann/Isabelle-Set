theory HOTG_Binary_Relations_Wellorder
  imports 
    HOTG_Basics
    Binary_Relations_Wellorder
begin

overloading
  wellorder_on_set \<equiv> "wellorder_on :: set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "wellorder_on_set (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<equiv> wellorder_on (mem_of S) R"
end

lemma wellorder_on_set_eq_wellorder_on_pred [simp]:
  "(wellorder_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool) = wellorder_on (mem_of S)"
  unfolding wellorder_on_set_def by simp

lemma wellorder_on_set_eq_wellorder_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of S"
  shows "wellorder_on (S :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> wellorder_on P"
  using assms by simp

lemma wellorder_on_set_iff_wellorder_on_pred [iff]:
  "wellorder_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) \<longleftrightarrow> wellorder_on (mem_of S) R"
  by simp


overloading
  wfrec_on_set \<equiv> "wfrec_on :: set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> ((set \<Rightarrow> 'b) \<Rightarrow> set \<Rightarrow> 'b) \<Rightarrow> set \<Rightarrow> 'b"
begin
  definition "wfrec_on_set (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) (step :: ((set \<Rightarrow> 'b) \<Rightarrow> set \<Rightarrow> 'b))
    \<equiv> (wfrec_on (mem_of S) R step) :: set \<Rightarrow> 'b"
end

lemma wfrec_on_set_eq_wfrec_on_pred [simp]:
  "wfrec_on (S :: set) (R :: set \<Rightarrow> set \<Rightarrow> bool) (step :: (set \<Rightarrow> 'b) \<Rightarrow> set \<Rightarrow> 'b) 
    = (wfrec_on (mem_of S) R step :: set \<Rightarrow> 'b)"
  unfolding wfrec_on_set_def by auto

end