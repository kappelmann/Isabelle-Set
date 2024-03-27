\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Typed Functions\<close>
theory TFunctions_Base
  imports
    Soft_Types.Soft_Types_HOL
    Transport.Functions_Monotone
    Transport.Functions_Restrict
begin

subsection \<open>Restrictions\<close>

overloading
  fun_restrict_type \<equiv> "fun_restrict :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a type \<Rightarrow> 'a \<Rightarrow> 'b"
begin
  definition "(fun_restrict_type (f :: 'a \<Rightarrow> 'b) (T :: 'a type) :: 'a \<Rightarrow> 'b) \<equiv>
    fun_restrict f (type_pred T)"
end

lemma fun_restrict_set_eq_fun_restrict [simp]:
  "(fun_restrict (f :: 'a \<Rightarrow> 'b) (T :: 'a type) :: 'a \<Rightarrow> 'b) = fun_restrict f (type_pred T)"
  unfolding fun_restrict_type_def by auto

lemma fun_restrict_type_eq_fun_restrict_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  and "f \<equiv> g"
  shows "fun_restrict (f :: 'a \<Rightarrow> 'b) (T :: 'a type) :: 'a \<Rightarrow> 'b \<equiv> fun_restrict g P"
  using assms by simp

subsection \<open>Types and Monotonicity\<close>

lemma dep_mono_wrt_pred_type_pred_if_Dep_fun_type:
  assumes "f : (x : A) \<Rightarrow> B x"
  shows "([x \<Colon> type_pred A] \<Rrightarrow>\<^sub>m type_pred (B x)) f"
  using assms by (intro dep_mono_wrt_predI) auto

lemma Dep_fun_type_if_dep_mono_wrt_pred_type_pred:
  assumes "([x \<Colon> type_pred A] \<Rrightarrow>\<^sub>m type_pred (B x)) f"
  shows "f : (x : A) \<Rightarrow> B x"
  using assms by auto

corollary dep_mono_wrt_pred_type_pred_iff_Dep_fun_type:
  "([x \<Colon> type_pred A] \<Rrightarrow>\<^sub>m type_pred (B x)) f \<longleftrightarrow> f : (x : A) \<Rightarrow> B x"
  using dep_mono_wrt_pred_type_pred_if_Dep_fun_type Dep_fun_type_if_dep_mono_wrt_pred_type_pred
  by blast

soft_type_translation
  "([x \<Colon> type_pred A] \<Rrightarrow>\<^sub>m type_pred (B x)) f" \<rightleftharpoons> "f : (x : A) \<Rightarrow> B x"
  using dep_mono_wrt_pred_type_pred_iff_Dep_fun_type by auto


end