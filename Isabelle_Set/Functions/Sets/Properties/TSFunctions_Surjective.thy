\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Surjective\<close>
theory TSFunctions_Surjective
  imports
    HOTG.HOTG_Functions_Surjective
    TSBinary_Relations_Surjective
begin

overloading
  set_surjective_at_type \<equiv> "surjective_at :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_surjective_at_type :: set type \<Rightarrow> set \<Rightarrow> bool \<equiv> rel_surjective_at"
end

lemma set_surjective_at_type_eq_rel_surjective_at_type [simp]:
  "(surjective_at :: set type \<Rightarrow> set \<Rightarrow> bool) = rel_surjective_at"
  unfolding set_surjective_at_type_def by simp

lemma set_surjective_at_type_eq_rel_surjective_at_type_uhint [uhint]:
  "(surjective_at :: set type \<Rightarrow> set \<Rightarrow> bool) \<equiv> rel_surjective_at"
  by simp

lemma set_surjective_at_type_iff_rel_surjective_at_type [iff]:
  "surjective_at (T :: set type) (f :: set) \<longleftrightarrow> rel_surjective_at T f"
  by simp

end