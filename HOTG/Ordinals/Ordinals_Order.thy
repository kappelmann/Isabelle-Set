\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Order\<close>
theory Ordinals_Order
  imports
    Ordinals_Base
    SLess_Than
begin

unbundle
  no_HOL_groups_syntax
  no_HOL_order_syntax

lemma not_lt_zero [iff]: "\<not>(X < 0)"
  unfolding lt_iff_mem_trans_closure by auto

lemma zero_lt_if_ne_zero [iff]:
  assumes "X \<noteq> 0"
  shows "0 < X"
  using assms mem_trans_closed_mem_trans_closure
  by (intro lt_if_mem_trans_closure empty_mem_if_mem_trans_closedI) auto

lemma zero_le [iff]: "0 \<le> X" by (subst le_iff_lt_or_eq) auto

end
