\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOTG_Functions_Restrict
  imports
    HOTG_Binary_Relation_Functions
    Transport.Functions_Restrict
begin

unbundle no_HOL_ascii_syntax

context
  includes fun_restrict_syntax no_rel_restrict_syntax
begin

definition "fun_restrict_set f A \<equiv> f\<restriction>\<^bsub>mem_of A\<^esub>"
adhoc_overloading fun_restrict fun_restrict_set

lemma fun_restrict_set_eq_fun_restrict_pred [simp]: "f\<restriction>\<^bsub>A\<^esub> = f\<restriction>\<^bsub>mem_of A\<^esub>"
  unfolding fun_restrict_set_def by simp

lemma fun_restrict_set_eq_fun_restrict_pred_uhint [uhint]:
  assumes "f \<equiv> f'"
  and "P \<equiv> mem_of A"
  shows "f\<restriction>\<^bsub>A\<^esub> = f'\<restriction>\<^bsub>P\<^esub>"
  using assms by simp

definition "set_fun_restrict_pred :: set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set \<equiv> rel_restrict_left"
adhoc_overloading fun_restrict set_fun_restrict_pred

lemma set_fun_restrict_pred_eq_rel_restrict_left [simp]:
  "(set_fun_restrict_pred :: set \<Rightarrow> (set \<Rightarrow> bool) \<Rightarrow> set) = rel_restrict_left"
  unfolding set_fun_restrict_pred_def by simp

lemma set_fun_restrict_pred_eq_rel_restrict_left_uhint [uhint]:
  assumes "f :: set \<equiv> f'"
  and "P :: set \<Rightarrow> bool \<equiv> P'"
  shows "f\<restriction>\<^bsub>P\<^esub> = rel_restrict_left f' P'"
  using assms by simp

definition "set_fun_restrict_set :: set \<Rightarrow> set \<Rightarrow> set \<equiv> rel_restrict_left"
adhoc_overloading fun_restrict set_fun_restrict_set

lemma set_fun_restrict_set_eq_rel_restrict_left [simp]:
  "(set_fun_restrict_set :: set \<Rightarrow> set \<Rightarrow> set) = rel_restrict_left"
  unfolding set_fun_restrict_set_def by simp

lemma set_fun_restrict_set_eq_rel_restrict_left_uhint [uhint]:
  assumes "f :: set \<equiv> f'"
  and "A :: set \<equiv> A'"
  shows "f\<restriction>\<^bsub>A\<^esub> = rel_restrict_left f' A'"
  using assms by simp

lemma repl_fun_restrict_set_eq_repl [simp]: "{f\<restriction>\<^bsub>A\<^esub> x | x \<in> A} = {f x | x \<in> A}"
  by simp

end


end