\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Lambda Abstractions\<close>
theory HOTG_Functions_Lambda
  imports
    HOTG_Clean_Functions
    HOTG_Functions_Monotone
    Transport.Binary_Relations_Function_Lambda
    ML_Unification.Unification_Attributes
begin

unbundle no_HOL_ascii_syntax

definition "rel_lambda_set A :: (set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a \<Rightarrow> bool \<equiv> rel_lambda (mem_of A)"
adhoc_overloading rel_lambda rel_lambda_set

lemma rel_lambda_set_eq_rel_lambda_pred [simp]: "rel_lambda_set A = rel_lambda_pred (mem_of A)"
  unfolding rel_lambda_set_def by simp

lemma rel_lambda_set_eq_rel_lambda_pred_uhint [uhint]:
  assumes "A' = mem_of A"
  shows "rel_lambda_set A \<equiv> rel_lambda_pred A'"
  using assms by simp

lemma rel_lambda_set_iff_rel_lambda_pred [iff]: "(\<lambda>x : A. f x) x y \<longleftrightarrow> (\<lambda>x : mem_of A. f x) x y"
  by (simp only: rel_lambda_set_eq_rel_lambda_pred)

definition "set_rel_lambda_set A f \<equiv> {\<langle>x, f x\<rangle> | x \<in> A}"
adhoc_overloading rel_lambda set_rel_lambda_set

lemma mk_pair_mem_rel_lambdaI [intro]:
  assumes "x \<in> A"
  and "f x = y"
  shows "\<langle>x, y\<rangle> \<in> (\<lambda>x : A. f x)"
  unfolding set_rel_lambda_set_def using assms by auto

lemma mk_pair_app_mem_rel_lambdaI:
  assumes "x \<in> A"
  shows "\<langle>x, f x\<rangle> \<in> (\<lambda>x : A. f x)"
  using assms by auto

lemma mem_rel_lambdaE [elim!]:
  assumes "p \<in> (\<lambda>x : A. f x)"
  obtains x y where "p = \<langle>x, f x\<rangle>" "x \<in> A"
  using assms unfolding set_rel_lambda_set_def by auto

lemma set_rel_lambda_cong [cong]:
  "\<lbrakk>\<And>x. x \<in> A \<longleftrightarrow> x \<in> A'; \<And>x. x \<in> A' \<Longrightarrow> f x = f' x\<rbrakk> \<Longrightarrow> ((\<lambda>x : A. f x) :: set) = \<lambda>x : A'. f' x"
  by (intro eqI) auto

lemma is_bin_rel_rel_lambda: "is_bin_rel (\<lambda>x : A. f x)" by auto

lemma rel_rel_lambda_eq_rel_lambda [simp, set_to_HOL_simp]: "rel (\<lambda>x : A. f x) = (\<lambda>x : A. f x)"
  by (intro ext) auto

context
  notes
    set_to_HOL_simp[simp, symmetric, simp del]
    is_bin_rel_rel_lambda[simp]
begin

lemma dom_rel_lambda_eq [simp]: "dom (\<lambda>x : A. f x) = A"
  by (urule in_dom_rel_lambda_eq)

lemma mem_of_codom_rel_lambda_eq_has_inverse_on [simp, set_to_HOL_simp]:
  "mem_of (codom (\<lambda>x : A. f x)) = has_inverse_on A f"
  by (urule in_codom_rel_lambda_eq_has_inverse_on)

lemma set_crel_dep_mono_wrt_pred_rel_lambda: "((x : (A :: set)) \<rightarrow>\<^sub>c {f x}) ((\<lambda>x : A. f x) :: set)"
  by (urule set_crel_dep_mono_wrt_predI, urule crel_dep_mono_wrt_pred_rel_lambda) simp

lemma set_rel_lambda_eval_eq [simp]:
  assumes "x \<in> A"
  shows "((\<lambda>x : A. f x) :: set)`x = f x"
  by (urule rel_lambda_eval_eq) (urule assms)

lemma app_eq_if_set_rel_lambda_eqI:
  assumes "((\<lambda>x : A. f x) :: set) = (\<lambda>x : A. g x)"
  assumes "x \<in> A"
  shows "f x = g x"
  using assms by (urule app_eq_if_rel_lambda_eqI)

lemma set_crel_dep_mono_wrt_bin_inter_rel_lambda_bin_inter_if_set_rel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow> B x) (R :: set)"
  shows "((x : A \<inter> A') \<rightarrow>\<^sub>c B x) ((\<lambda>x : A \<inter> A'. R`x) :: set)"
  using assms by (urule crel_dep_mono_wrt_pred_inf_rel_lambda_inf_if_rel_dep_mono_wrt_pred)

lemma set_crel_dep_mono_wrt_set_rel_lambda_if_subset_if_rel_dep_mono_wrt_set:
  assumes "((x : A) \<rightarrow> B x) (R :: set \<Rightarrow> _)"
  and "A' \<subseteq> A"
  shows "((x : A') \<rightarrow>\<^sub>c B x) ((\<lambda>x : A'. R`x) :: set)"
  using assms by (urule crel_dep_mono_wrt_pred_rel_lambda_if_le_if_rel_dep_mono_wrt_pred)

lemma set_rel_lambda_ext:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) (R :: set)"
  and "\<And>x. x \<in> A \<Longrightarrow> f x = R`x"
  shows "(\<lambda>x : A. f x) = R"
  supply is_bin_rel_if_set_crel_dep_mono_wrt_pred[uOF assms(1), simp]
  using assms by (urule rel_lambda_ext) simp_all

lemma set_rel_lambda_eval_eq_if_set_crel_dep_mono_wrt_set [simp]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) (R :: set)"
  shows "(\<lambda>x : A. R`x) = R"
  supply is_bin_rel_if_set_crel_dep_mono_wrt_pred[uOF assms, simp]
  using assms by (urule rel_lambda_eval_eq_if_crel_dep_mono_wrt_pred)

lemma rel_restrict_left_set_eq_rel_lambda_if_subset_if_rel_dep_mono_wrt_set:
  assumes "((x : A) \<rightarrow> B x) (R :: set)"
  and "A' \<subseteq> A"
  shows "R\<restriction>\<^bsub>A'\<^esub> = (\<lambda>x : A'. R`x)"
  using assms by (urule rel_restrict_left_eq_rel_lambda_if_le_if_rel_dep_mono_wrt_pred)

end

lemma mono_dep_mono_wrt_set_crel_dep_mono_wrt_set_rel_lambda:
  "(((x : A) \<Rightarrow> B x) \<Rightarrow> ((x : A) \<rightarrow>\<^sub>c B x :: set \<Rightarrow> bool)) (rel_lambda A :: (set \<Rightarrow> set) \<Rightarrow> set)"
  by (urule (rr) mono_wrt_predI set_crel_dep_mono_wrt_predI') auto

lemma set_rel_lambda_dep_pair_uncurry_eval_eqI [simp]:
  assumes "x \<in> A" "y \<in> B x"
  shows "((\<lambda>p : \<Sum>x : A. B x. uncurry f p) :: set)`\<langle>x, y\<rangle> = f x y"
  using assms by (intro eval_set_eq_if_right_unique_on_singletonI) auto

(*FIXME: corresponding input does not parse (cf. theorem output)*)
lemma set_rel_lambda_dep_pair_eq_rel_lambda_uncurry:
  "((\<lambda>p : \<Sum>x : A. B x. f p) :: set) = (\<lambda>p : \<Sum>x : A. B x. (\<lambda>\<langle>a, b\<rangle>. f \<langle>a, b\<rangle>) p)"
  by (rule set_rel_lambda_cong) auto

lemma mono_subset_rel_lambda: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) (\<lambda>(A :: set). \<lambda>x : A. f x)" by fast

end