\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Typed Binary Relations\<close>
theory TBinary_Relations
  imports
    HOL_Basics.Restricted_Equality
    HOTG.Axioms
    Soft_Types.Soft_Types_HOL
begin

overloading
  eq_restrict_set \<equiv> "eq_restrict :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  eq_restrict_type \<equiv> "eq_restrict :: 'a type \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
  definition "eq_restrict_set (A :: set) \<equiv> ((=\<^bsub>mem_of A\<^esub>) :: set \<Rightarrow> _)"
  definition "eq_restrict_type (T :: 'a type) \<equiv> ((=\<^bsub>type_pred T\<^esub>) :: 'a \<Rightarrow> _)"
end

lemma eq_restrict_set_eq_eq_restrict_pred [simp]:
  "(eq_restrict :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool) A = (=\<^bsub>mem_of A\<^esub>)"
  unfolding eq_restrict_set_def by simp

lemma eq_restrict_set_iff_eq_restrict_pred [iff]:
  "(eq_restrict :: set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool) A x y \<longleftrightarrow> x =\<^bsub>mem_of A\<^esub> y"
  by simp

lemma eq_restrict_type_eq_eq_restrict_pred [simp]:
  "(eq_restrict :: 'a type \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) T = (=\<^bsub>type_pred T\<^esub>)"
  unfolding eq_restrict_type_def by simp

lemma eq_restrict_type_iff_eq_restrict_pred [iff]:
  "(eq_restrict :: 'a type \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) T x y \<longleftrightarrow> x =\<^bsub>type_pred T\<^esub> y"
  by simp


end