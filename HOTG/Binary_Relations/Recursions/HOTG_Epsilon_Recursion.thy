\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
section \<open>Epsilon Recursion\<close>
theory HOTG_Epsilon_Recursion
  imports
    HOTG_Less_Than
    HOTG_Functions_Restrict
    Transport.Wellfounded_Transitive_Recursion
begin

unbundle no_HOL_order_syntax

context
  includes fun_restrict_syntax no_rel_restrict_syntax
begin

definition mem_rec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a" where
  "mem_rec step = wft_rec (<) (\<lambda>f X. step f\<restriction>\<^bsub>X\<^esub> X)"

corollary mem_rec_eq: "mem_rec step X = step (mem_rec step)\<restriction>\<^bsub>X\<^esub> X"
proof -
  have fun_rel_restrict_eq: "(fun_rel_restrict f (<) X)\<restriction>\<^bsub>X\<^esub> = f\<restriction>\<^bsub>X\<^esub>" for f
    using lt_if_mem by (auto simp: fun_restrict_eq_if)
  then have "mem_rec step X = step ((fun_rel_restrict (mem_rec step) (<) X)\<restriction>\<^bsub>X\<^esub>) X"
    using wellfounded_lt transitive_lt
    by (simp only: wf_rec_step_eq wft_rec_eq_wf_rec_stepI mem_rec_def)
  then show ?thesis unfolding fun_rel_restrict_eq by simp
qed

end


end