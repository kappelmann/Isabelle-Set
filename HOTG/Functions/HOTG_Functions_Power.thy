\<^marker>\<open>creator "Niklas Krofta"\<close>
theory HOTG_Functions_Power
  imports
    HOTG_Ordinals_Omega
begin

definition fun_pow :: "('a \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "fun_pow f = omega_rec id ((\<circ>) f)"

open_bundle hotg_fun_pow_syntax begin notation fun_pow ("(_)\<^bsup>(_)\<^esup>" [1000]) end

lemma fun_pow_zero_eq_id [simp]: "f\<^bsup>0\<^esup> = id"
  unfolding fun_pow_def omega_rec_zero by auto

lemma fun_pow_succ_eq_if_mem_omega [simp]:
  assumes "n \<in> \<omega>"
  shows "f\<^bsup>succ n\<^esup> x = f (f\<^bsup>n\<^esup> x)"
  unfolding fun_pow_def omega_rec_succ[OF assms] by simp

lemma fun_pow_one_eq_self [simp]: "f\<^bsup>1\<^esup> = f"
  by auto

end