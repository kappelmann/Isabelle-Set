\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Injective\<close>
theory SFunctions_Injective
  imports
    SBinary_Relations_Injective
begin

overloading
  injective_on_set \<equiv> "injective_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> bool"
  set_injective_on_pred \<equiv> "injective_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool"
  set_injective_on_set \<equiv> "injective_on :: set \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "injective_on_set (A :: set) :: (set \<Rightarrow> 'a) \<Rightarrow> bool \<equiv> injective_on (mem_of A)"
  definition "set_injective_on_pred :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool \<equiv> rel_injective_on"
  definition "set_injective_on_set :: set \<Rightarrow> set \<Rightarrow> bool \<equiv> rel_injective_on"
end

lemma injective_on_set_eq_injective_on_pred [simp]:
  "(injective_on (A :: set) :: (set \<Rightarrow> 'a) \<Rightarrow> bool) = injective_on (mem_of A)"
  unfolding injective_on_set_def by simp

lemma injective_on_set_eq_injective_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "injective_on (A :: set) :: (set \<Rightarrow> 'a) \<Rightarrow> bool \<equiv> injective_on P"
  using assms by simp

lemma inverse_on_set_iff_injective_on_pred [iff]:
  "injective_on (A :: set) (f :: set \<Rightarrow> 'a) \<longleftrightarrow> injective_on (mem_of A) f"
  by simp

lemma set_injective_on_pred_eq_rel_injective_on_pred [simp]:
  "(injective_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool) = rel_injective_on"
  unfolding set_injective_on_pred_def by simp

lemma set_injective_on_pred_eq_rel_injective_on_pred_uhint [uhint]:
  "(injective_on :: (set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> bool) \<equiv> rel_injective_on"
  by simp

lemma set_injective_on_pred_iff_rel_injective_on_pred [iff]:
  "injective_on (P :: set \<Rightarrow> bool) (f :: set) \<longleftrightarrow> rel_injective_on P f"
  by simp

lemma set_injective_on_set_eq_rel_injective_on_set [simp]:
  "(injective_on :: set \<Rightarrow> set \<Rightarrow> bool) = rel_injective_on"
  unfolding set_injective_on_set_def by simp

lemma set_injective_on_set_eq_rel_injective_on_pred_uhint [uhint]:
  "(injective_on :: set \<Rightarrow> set \<Rightarrow> bool) \<equiv> rel_injective_on"
  by simp

lemma set_injective_on_set_iff_rel_injective_on_set [iff]:
  "injective_on (A :: set) (f :: set) \<longleftrightarrow> rel_injective_on A f"
  by simp

end