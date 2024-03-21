\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Functions_Restrict
  imports Basic Replacement
begin

paragraph \<open>Summary\<close>
text \<open>If the input \<open>x\<close> is within the restricted domain, then \<open>f x\<close> is returned; otherwise, 
returns \<open>undefined\<close>.\<close>

consts fun_restrict :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'b"

overloading
  fun_restrict_pred \<equiv> "fun_restrict :: ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b"
begin
  definition "fun_restrict_pred f P x \<equiv> if P x then f x else undefined"
end

bundle fun_restrict_syntax
begin
notation fun_restrict ("(_)\<restriction>(\<^bsub>_\<^esub>)" [1000])
end
bundle no_fun_restrict_syntax
begin
no_notation fun_restrict ("(_)\<restriction>(\<^bsub>_\<^esub>)" [1000])
end

context
  includes fun_restrict_syntax
begin

lemma fun_restrict_eq [simp]:
  assumes "P x"
  shows "fun_restrict f P x = f x"
  using assms unfolding fun_restrict_pred_def by auto

lemma fun_restrict_eq_if_not [simp]:
  assumes "\<not>(P x)"
  shows "fun_restrict f P x = undefined"
  using assms unfolding fun_restrict_pred_def by auto

end

overloading
  fun_restrict_set \<equiv> "fun_restrict :: (set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> 'a"
begin
  definition "fun_restrict_set f X \<equiv> fun_restrict f (mem_of X) :: set \<Rightarrow> 'a"
end

lemma fun_restrict_set_eq_fun_restrict [simp]:
  "fun_restrict (f :: set \<Rightarrow> 'a) X = fun_restrict f (mem_of X)"
  unfolding fun_restrict_set_def by auto

lemma repl_fun_restrict_eq_repl [simp]: "{fun_restrict f A x | x \<in> A} = {f x | x \<in> A}" 
  by simp 
 

end
