\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Well-Founded Recursion\<close>
theory HOTG_Wellfounded_Recursion
  imports
    HOTG_Basics
    Transport.Wellfounded_Recursion
begin

definition "wf_rec_on_set (A :: set) :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> ((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a
  \<equiv> wf_rec_on (mem_of A)"
adhoc_overloading wf_rec_on wf_rec_on_set

lemma wf_rec_on_set_eq_wf_rec_on_pred [simp]: "wf_rec_on A = wf_rec_on (mem_of A)"
  unfolding wf_rec_on_set_def by auto

lemma wf_rec_on_set_eq_wf_rec_on_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "wf_rec_on A \<equiv> wf_rec_on (mem_of A)"
  using assms wf_rec_on_set_eq_wf_rec_on_pred by simp


end