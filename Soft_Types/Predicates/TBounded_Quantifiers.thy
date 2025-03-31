\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Type-Bounded Quantifiers\<close>
theory TBounded_Quantifiers
  imports
    Transport.Bounded_Quantifiers
    Soft_Types_HOL_Base
begin

definition "ball_type T \<equiv> \<forall>\<^bsub>of_type T\<^esub>"
adhoc_overloading ball \<rightleftharpoons> ball_type

definition "bex_type T \<equiv> \<exists>\<^bsub>of_type T\<^esub>"
adhoc_overloading bex \<rightleftharpoons> bex_type

lemma ball_type_eq_ball [simp]: "\<forall>\<^bsub>T\<^esub> = \<forall>\<^bsub>of_type T\<^esub>"
  unfolding ball_type_def by simp

lemma ball_type_eq_ball_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "\<forall>\<^bsub>T\<^esub> = \<forall>\<^bsub>P\<^esub>"
  using assms by simp

lemma ball_type_iff_ball [iff]: "(\<forall>x : T. P x) \<longleftrightarrow> (\<forall>x : of_type T. P x)"
  by simp

lemma bex_type_eq_bex [simp]: "\<exists>\<^bsub>T\<^esub> = \<exists>\<^bsub>of_type T\<^esub>"
  unfolding bex_type_def by simp

lemma bex_type_eq_bex_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "\<exists>\<^bsub>T\<^esub> = \<exists>\<^bsub>P\<^esub>"
  using assms by simp

lemma bex_type_iff_bex [iff]: "(\<exists>x : T. P x) \<longleftrightarrow> (\<exists>x : of_type T. P x)"
  by simp

definition "bex1_type T \<equiv> \<exists>!\<^bsub>of_type T\<^esub>"
adhoc_overloading bex1 \<rightleftharpoons> bex1_type

lemma bex1_type_eq_bex1_pred [simp]: "\<exists>!\<^bsub>T\<^esub> = \<exists>!\<^bsub>of_type T\<^esub>"
  unfolding bex1_type_def by simp

lemma bex1_type_eq_bex1_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "\<exists>!\<^bsub>T\<^esub> = \<exists>!\<^bsub>P\<^esub>"
  using assms by simp

lemma bex1_type_iff_bex1_pred [iff]: "(\<exists>!x : T. P x) \<longleftrightarrow> (\<exists>!x : of_type T. P x)"
  by simp


end
