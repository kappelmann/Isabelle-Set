\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Larry Paulson"\<close>
section \<open>Bounded Quantifiers\<close>
theory HOTG_Bounded_Quantifiers
  imports
    HOTG_Basics
    Transport.Bounded_Quantifiers
begin

definition "ball_set A \<equiv> \<forall>\<^bsub>mem_of A\<^esub>"
adhoc_overloading ball ball_set

lemma ball_set_eq_ball_pred [simp]: "\<forall>\<^bsub>A\<^esub> = \<forall>\<^bsub>mem_of A\<^esub>"
  unfolding ball_set_def by simp

lemma ball_set_eq_ball_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "\<forall>\<^bsub>A\<^esub> = \<forall>\<^bsub>P\<^esub>"
  using assms by simp

lemma ball_set_iff_ball_pred [iff]: "(\<forall>x : A. P x) \<longleftrightarrow> (\<forall>x : mem_of A. P x)"
  by simp

definition "bex_set A \<equiv> \<exists>\<^bsub>mem_of A\<^esub>"
adhoc_overloading bex bex_set

lemma bex_set_eq_bex_pred [simp]: "\<exists>\<^bsub>A\<^esub> = \<exists>\<^bsub>mem_of A\<^esub>"
  unfolding bex_set_def by simp

lemma bex_set_eq_bex_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "\<exists>\<^bsub>A\<^esub> = \<exists>\<^bsub>P\<^esub>"
  using assms by simp

lemma bex_set_iff_bex_pred [iff]: "(\<exists>x : A. Q x) \<longleftrightarrow> (\<exists>x : mem_of A. Q x)"
  by simp

definition "bex1_set A \<equiv> \<exists>!\<^bsub>mem_of A\<^esub>"
adhoc_overloading bex1 bex1_set

lemma bex1_set_eq_bex1_pred [simp]: "\<exists>!\<^bsub>A\<^esub> = \<exists>!\<^bsub>mem_of A\<^esub>"
  unfolding bex1_set_def by simp

lemma bex1_set_eq_bex1_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  shows "\<exists>!\<^bsub>A\<^esub> = \<exists>!\<^bsub>P\<^esub>"
  using assms by simp

lemma bex1_set_iff_bex1_pred [iff]: "(\<exists>!x : A. Q x) \<longleftrightarrow> (\<exists>!x : mem_of A. Q x)"
  by simp

end
