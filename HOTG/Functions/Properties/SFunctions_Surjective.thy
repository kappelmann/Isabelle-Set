\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Surjective\<close>
theory SFunctions_Surjective
  imports
    Transport.Functions_Surjective
    SBinary_Relations_Surjective
begin

overloading
  surjective_at_set \<equiv> "surjective_at :: set \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool"
  set_surjective_at_pred \<equiv> "surjective_at :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_surjective_at_set \<equiv> "surjective_at :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "surjective_at_set (A :: set) :: ('a \<Rightarrow> set) \<Rightarrow> bool \<equiv> surjective_at (mem_of A)"
  definition "set_surjective_at_pred :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool \<equiv> rel_surjective_at"
  definition "set_surjective_at_set :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> rel_surjective_at"
end

lemma surjective_at_set_eq_surjective_at_pred [simp]:
  "(surjective_at (A :: set) :: ('a \<Rightarrow> set) \<Rightarrow> bool) = surjective_at (mem_of A)"
  unfolding surjective_at_set_def by simp

lemma surjective_at_set_eq_surjective_at_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "surjective_at (A :: set) :: ('a \<Rightarrow> set) \<Rightarrow> bool \<equiv> surjective_at P"
  using assms by simp

lemma surjective_at_set_iff_surjective_at_pred [iff]:
  "surjective_at (A :: set) (f :: 'a \<Rightarrow> set) \<longleftrightarrow> surjective_at (mem_of A) f"
  by simp

lemma set_surjective_at_pred_eq_rel_surjective_at_pred [simp]:
  "(surjective_at :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool) = rel_surjective_at"
  unfolding set_surjective_at_pred_def by simp

lemma set_surjective_at_pred_eq_rel_surjective_at_pred_uhint [uhint]:
  "(surjective_at :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool) \<equiv> rel_surjective_at"
  by simp

lemma set_surjective_at_pred_iff_rel_surjective_at_pred [iff]:
  "surjective_at (P :: set \<Rightarrow> bool) (f :: set) \<longleftrightarrow> rel_surjective_at P f"
  by simp

lemma set_surjective_at_set_eq_rel_surjective_at_pred [simp]:
  "(surjective_at :: set \<Rightarrow> set \<Rightarrow> bool) = rel_surjective_at"
  unfolding set_surjective_at_set_def by simp

lemma set_surjective_at_set_eq_rel_surjective_at_pred_uhint [uhint]:
  "(surjective_at :: set \<Rightarrow> set \<Rightarrow> bool) \<equiv> rel_surjective_at"
  by simp

lemma set_surjective_at_set_iff_rel_surjective_at_pred [iff]:
  "surjective_at (A :: set) (f :: set) \<longleftrightarrow> rel_surjective_at A f"
  by simp

end