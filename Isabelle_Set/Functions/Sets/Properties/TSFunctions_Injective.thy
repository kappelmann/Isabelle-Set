\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Injective\<close>
theory TSFunctions_Injective
  imports
    HOTG.HOTG_Functions_Injective
    TSBinary_Relations_Injective
begin

overloading
  set_injective_on_type \<equiv> "injective_on :: set type \<Rightarrow> set \<Rightarrow> bool"
begin
  definition "set_injective_on_type :: set type \<Rightarrow> set \<Rightarrow> bool \<equiv> rel_injective_on"
end

lemma set_injective_on_type_eq_rel_injective_on_type [simp]:
  "(injective_on :: set type \<Rightarrow> set \<Rightarrow> bool) = rel_injective_on"
  unfolding set_injective_on_type_def by simp

lemma set_injective_on_type_eq_rel_injective_on_type_uhint [uhint]:
  "(injective_on :: set type \<Rightarrow> set \<Rightarrow> bool) \<equiv> rel_injective_on"
  by simp

lemma set_injective_on_type_iff_rel_injective_on_type [iff]:
  "injective_on (T :: set type) (f :: set) \<longleftrightarrow> rel_injective_on T f"
  by simp


end