\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
section \<open>Transfinite Recursion\<close>
theory HOTG_Transfinite_Recursion
  imports
    HOTG_Less_Than
    HOTG_Functions_Restrict
    Transport.Wellfounded_Transitive_Recursion
begin

unbundle no_HOL_order_syntax

lemma wellfounded_lt: "wellfounded (<)"
  by (auto intro!: wellfoundedI elim: lt_minimal_set_witnessE)

context
  includes fun_restrict_syntax no_rel_restrict_syntax
begin

definition transfrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a" where
  "transfrec step = wftrec (<) (\<lambda>f X. step f\<restriction>\<^bsub>X\<^esub> X)"

corollary transfrec_eq: "transfrec step X = step (transfrec step)\<restriction>\<^bsub>X\<^esub> X"
proof -
  have fun_rel_restrict_eq: "(fun_rel_restrict f (<) X)\<restriction>\<^bsub>X\<^esub> = f\<restriction>\<^bsub>X\<^esub>" for f
    using lt_if_mem by (auto simp: fun_restrict_eq_if)
  then have "transfrec step X = step ((fun_rel_restrict (transfrec step) (<) X)\<restriction>\<^bsub>X\<^esub>) X"
    using wellfounded_lt transitive_lt
    by (simp_all only: wfrec_step_eq wftrec_eq_wfrec_stepI transfrec_def)
  then show ?thesis unfolding fun_rel_restrict_eq by simp
qed

end


end