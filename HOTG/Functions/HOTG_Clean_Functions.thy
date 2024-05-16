\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Clean Set Functions\<close>
theory HOTG_Clean_Functions
  imports
    HOTG_Functions_Base
    HOTG_Functions_Evaluation
    HOTG_Binary_Relation_Functions
    HOTG_Binary_Relations_Left_Total
    HOTG_Binary_Relations_Right_Unique
    Transport.Binary_Relations_Clean_Function
begin

unbundle no_HOL_ascii_syntax

definition "crel_dep_mono_wrt_set A B :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> (x : mem_of A) \<rightarrow>\<^sub>c mem_of (B x)"
adhoc_overloading crel_dep_mono_wrt crel_dep_mono_wrt_set
definition "crel_mono_wrt_set A B :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> (mem_of A) \<rightarrow>\<^sub>c mem_of B"
adhoc_overloading crel_mono_wrt crel_mono_wrt_set

lemma crel_dep_mono_wrt_set_eq_crel_dep_mono_wrt_pred [simp]:
  "((x : A) \<rightarrow>\<^sub>c B x) = ((x : mem_of A) \<rightarrow>\<^sub>c mem_of (B x))"
  unfolding crel_dep_mono_wrt_set_def by simp

lemma crel_dep_mono_wrt_set_eq_crel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "\<And>x. Q x \<equiv> mem_of (B x)"
  shows "((x : A) \<rightarrow>\<^sub>c B x) \<equiv> ((x : P) \<rightarrow>\<^sub>c Q x)"
  using assms by simp

lemma crel_dep_mono_wrt_set_iff_crel_dep_mono_wrt_pred [iff]:
  "((x : A) \<rightarrow>\<^sub>c B x) R \<longleftrightarrow> ((x : mem_of A) \<rightarrow>\<^sub>c mem_of (B x)) R"
  by simp

lemma crel_mono_wrt_set_eq_crel_mono_wrt_pred [simp]: "(A \<rightarrow>\<^sub>c B) = (mem_of A \<rightarrow>\<^sub>c mem_of B)"
  unfolding crel_mono_wrt_set_def by simp

lemma crel_mono_wrt_set_eq_crel_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "Q \<equiv> mem_of B"
  shows "(A \<rightarrow>\<^sub>c B) \<equiv> (P \<rightarrow>\<^sub>c Q)"
  using assms by simp

lemma crel_mono_wrt_set_iff_crel_mono_wrt_pred [iff]: "(A \<rightarrow>\<^sub>c B) R \<longleftrightarrow> (mem_of A \<rightarrow>\<^sub>c mem_of B) R"
  by simp

definition "set_crel_dep_mono_wrt_pred (A :: set \<Rightarrow> bool) (B :: set \<Rightarrow> set \<Rightarrow> bool) (R :: set) \<equiv>
  ((x : A) \<rightarrow>\<^sub>c B x) (rel R) \<and> is_bin_rel R"
adhoc_overloading crel_dep_mono_wrt set_crel_dep_mono_wrt_pred
definition "set_crel_mono_wrt_pred (A :: set \<Rightarrow> bool) (B :: set \<Rightarrow> bool) :: set \<Rightarrow> bool \<equiv> (_ : A) \<rightarrow>\<^sub>c B"
adhoc_overloading crel_mono_wrt set_crel_mono_wrt_pred

lemma set_crel_mono_wrt_pred_eq_set_crel_dep_mono_wrt_pred:
  "((A \<rightarrow>\<^sub>c B) :: set \<Rightarrow> bool) = ((_ : A) \<rightarrow>\<^sub>c B)"
  unfolding set_crel_mono_wrt_pred_def by simp

lemma set_crel_mono_wrt_pred_eq_set_crel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "A :: set \<Rightarrow> bool \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A \<rightarrow>\<^sub>c B :: set \<Rightarrow> bool \<equiv> (x : A') \<rightarrow>\<^sub>c B' x"
  using assms by (simp add: set_crel_mono_wrt_pred_eq_set_crel_dep_mono_wrt_pred)

lemma set_crel_mono_wrt_pred_iff_set_crel_dep_mono_wrt_pred:
  "(A \<rightarrow>\<^sub>c B) (R :: set) \<longleftrightarrow> ((_ : A) \<rightarrow>\<^sub>c B) R"
  unfolding set_crel_mono_wrt_pred_eq_set_crel_dep_mono_wrt_pred by simp

lemma set_crel_dep_mono_wrt_predI [intro]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) (rel R)"
  and "is_bin_rel R"
  shows "((x : A) \<rightarrow>\<^sub>c B x) R"
  using assms unfolding set_crel_dep_mono_wrt_pred_def by auto

lemma set_crel_dep_mono_wrt_predE:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  obtains "((x : A) \<rightarrow>\<^sub>c B x) (rel R)" "is_bin_rel R"
  using assms unfolding set_crel_dep_mono_wrt_pred_def by auto

lemma set_crel_dep_mono_wrt_predE' [elim]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  obtains "((x : A) \<rightarrow>\<^sub>c B x) (rel R)" "({\<Sum>}x : A. B x) R"
  using assms by (auto elim: set_crel_dep_mono_wrt_predE)

lemma set_crel_dep_mono_wrt_pred_eq_crel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "is_bin_rel R"
  and "A \<equiv> A'"
  and "\<And>x. B x \<equiv> B' x"
  and "R' \<equiv> rel R"
  shows "((x : A) \<rightarrow>\<^sub>c B x) R \<equiv> ((x : A') \<rightarrow>\<^sub>c B' x) R'"
  using assms by (intro eq_reflection) auto

lemma set_crel_dep_mono_wrt_pred_cong [cong]: "\<lbrakk>A = A'; \<And>x. A' x \<Longrightarrow> (B x :: set \<Rightarrow> bool) = B' x\<rbrakk> \<Longrightarrow>
  (((x : A) \<rightarrow>\<^sub>c B x) :: set \<Rightarrow> bool) = ((x : A') \<rightarrow>\<^sub>c B' x)"
  by (intro ext iffI set_crel_dep_mono_wrt_predI) auto

corollary is_bin_rel_if_set_crel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "is_bin_rel R"
  using assms by blast

lemma set_crel_dep_mono_wrt_predI':
  assumes "left_total_on A R"
  and "right_unique_on A R"
  and [uhint]: "({\<Sum>}x : A. B x) R"
  shows "((x : A) \<rightarrow>\<^sub>c B x) (R :: set)"
  supply is_bin_rel_if_set_dep_bin_rel[uhint]
  using assms by (urule crel_dep_mono_wrt_predI')

lemma set_crel_mono_wrt_predI [intro]:
  assumes "(A \<rightarrow>\<^sub>c B) (rel R)"
  and "is_bin_rel R"
  shows "(A \<rightarrow>\<^sub>c B) R"
  using assms by (urule set_crel_dep_mono_wrt_predI)

lemma set_crel_mono_wrt_predI':
  assumes "left_total_on A R"
  and "right_unique_on A R"
  and "(A {\<times>} B) R"
  shows "(A \<rightarrow>\<^sub>c B) (R :: set)"
  using assms by (urule set_crel_dep_mono_wrt_predI')

lemma set_crel_mono_wrt_predE:
  assumes "(A \<rightarrow>\<^sub>c B) R"
  obtains "(A \<rightarrow>\<^sub>c B) (rel R)" "is_bin_rel R"
  using assms by (urule (e) set_crel_dep_mono_wrt_predE)

lemma set_crel_mono_wrt_predE' [elim]:
  assumes "(A \<rightarrow>\<^sub>c B) R"
  obtains "(A \<rightarrow>\<^sub>c B) (rel R)" "(A {\<times>} B) R"
  using assms by (urule (e) set_crel_dep_mono_wrt_predE')

lemma set_crel_mono_wrt_pred_eq_crel_mono_wrt_pred_uhint [uhint]:
  assumes "is_bin_rel R"
  and "A \<equiv> A'"
  and "B \<equiv> B'"
  and "R' \<equiv> rel R"
  shows "(A \<rightarrow>\<^sub>c B) R \<equiv> (A' \<rightarrow>\<^sub>c B') R'"
  by (urule set_crel_dep_mono_wrt_pred_eq_crel_dep_mono_wrt_pred_uhint) (use assms in auto)

lemma eq_collect_mk_pair_eval_dom_if_set_crel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "R = {\<langle>x, R`x\<rangle> | x \<in> dom R}"
  using assms by (intro eqI) force+

context
  notes
    is_bin_rel_if_set_crel_dep_mono_wrt_pred[uhint]
    set_crel_mono_wrt_pred_eq_set_crel_dep_mono_wrt_pred_uhint[simp]
    set_to_HOL_simp[simp, symmetric, simp del]
begin

lemma mem_of_dom_eq_if_set_crel_dep_mono_wrt_pred [simp, set_to_HOL_simp]:
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "mem_of (dom R) = A"
  using assms by (urule in_dom_eq_if_crel_dep_mono_wrt_pred)

lemma mem_of_dom_eq_if_set_crel_mono_wrt_pred [simp, set_to_HOL_simp]:
  assumes [uhint]: "(A \<rightarrow>\<^sub>c B) R"
  shows "mem_of (dom R) = A"
  using assms by (urule in_dom_eq_if_crel_mono_wrt_pred)

lemma eq_if_mk_pair_mem_if_mk_pair_mem_if_set_crel_dep_mono_wrt_predI:
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "\<langle>x, y\<rangle> \<in> R" "\<langle>x, y'\<rangle> \<in> R"
  shows "y = y'"
  using assms by (urule eq_if_rel_if_rel_if_crel_dep_mono_wrt_predI)

lemma eval_eq_if_mk_pair_mem_if_set_crel_dep_mono_wrt_predI [simp]:
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "\<langle>x, y\<rangle> \<in> R"
  shows "R`x = y"
  using assms by (urule eval_eq_if_rel_if_crel_dep_mono_wrt_predI)

lemma set_crel_dep_mono_wrt_pred_relE:
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "\<langle>x, y\<rangle> \<in> R"
  obtains "A x" "B x y" "R`x = y"
  using assms by (urule (e) crel_dep_mono_wrt_pred_relE)

lemma set_crel_dep_mono_wrt_pred_relE':
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) R"
  obtains "\<And>x y. \<langle>x, y\<rangle> \<in> R \<Longrightarrow> A x \<and> B x y \<and> R`x = y"
  using assms by (urule (e) crel_dep_mono_wrt_pred_relE')

lemma rel_restrict_left_set_eq_self_if_set_crel_dep_mono_wrt_pred [simp]:
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) (R :: set)"
  shows "R\<restriction>\<^bsub>A\<^esub> = R"
  using assms by blast

lemma set_crel_dep_mono_wrt_pred_covariant_codom:
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) (R :: set)"
  and "\<And>x. A x \<Longrightarrow> B x (R`x) \<Longrightarrow> B' x (R`x)"
  shows "((x : A) \<rightarrow>\<^sub>c B' x) R"
  using assms by (urule crel_dep_mono_wrt_pred_covariant_codom) auto

lemma eval_eq_if_set_crel_dep_mono_wrt_pred_if_set_rel_dep_mono_wrt_predI:
  assumes [uhint]: "((x : A) \<rightarrow> B x) R" "((x : A') \<rightarrow>\<^sub>c B' x) R'"
  and "R \<subseteq> R'"
  and "A x"
  shows "R`x = R'`x"
proof -
  have [uhint]: "is_bin_rel R" by (rule is_bin_rel_if_subset_if_is_bin_rel) (use assms in auto)
  from assms show ?thesis by (urule eval_eq_if_crel_dep_mono_wrt_pred_if_rel_dep_mono_wrt_predI)
qed

lemma set_crel_dep_mono_wrt_pred_ext:
  fixes R R' :: set
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) R" "((x : A) \<rightarrow>\<^sub>c B' x) R'"
  and "\<And>x. A x \<Longrightarrow> R`x = R'`x"
  shows "R = R'"
  using assms by (urule crel_dep_mono_wrt_pred_ext)

lemma eq_if_subset_if_set_crel_dep_mono_wrt_pred_if_set_rel_dep_mono_wrt_pred:
  assumes [uhint]: "((x : A) \<rightarrow> B x) R" "((x : A) \<rightarrow>\<^sub>c B' x) R'"
  and "R \<subseteq> R'"
  shows "R = R'"
proof -
  have [simp]: "is_bin_rel R" by (rule is_bin_rel_if_subset_if_is_bin_rel) (use assms in auto)
  from assms show ?thesis by (urule eq_if_le_if_crel_dep_mono_wrt_pred_if_rel_dep_mono_wrt_pred)
qed

lemma set_crel_mono_wrt_pred_bottom_empty: "((\<bottom> :: set \<Rightarrow> bool) \<rightarrow>\<^sub>c A) {}"
  by (urule crel_mono_wrt_pred_bottom_bottom)

end

lemma set_crel_dep_mono_wrt_pred_bottom_iff_eq_empty [iff]:
  "((x : (\<bottom> :: set \<Rightarrow> bool)) \<rightarrow>\<^sub>c B x) R \<longleftrightarrow> R = {}"
  by auto

lemma mono_set_crel_dep_mono_wrt_pred_top_set_crel_dep_mono_wrt_pred_inf_rel_restrict_left:
  "(((x : A) \<rightarrow>\<^sub>c B x) \<Rightarrow> (A' : \<top>) \<Rightarrow> ((x : A \<sqinter> A') \<rightarrow>\<^sub>c B x :: set \<Rightarrow> bool)) rel_restrict_left"
  using mono_crel_dep_mono_wrt_pred_top_crel_dep_mono_wrt_pred_inf_rel_restrict_left
proof (intro mono_wrt_predI dep_mono_wrt_predI)
  fix R :: set and A' :: "set \<Rightarrow> bool" assume "((x : A) \<rightarrow>\<^sub>c B x) R" "\<top> A'"
  with mono_crel_dep_mono_wrt_pred_top_crel_dep_mono_wrt_pred_inf_rel_restrict_left
    have "((x : A \<sqinter> A') \<rightarrow>\<^sub>c B x) (rel R)\<restriction>\<^bsub>A'\<^esub>" by blast
  then show "((x : A \<sqinter> A') \<rightarrow>\<^sub>c B x) R\<restriction>\<^bsub>A'\<^esub>" by auto
qed

lemma mono_set_rel_dep_mono_wrt_pred_ge_set_crel_dep_mono_wrt_pred_rel_restrict_left:
  "(((x : A) \<rightarrow> B x) \<Rightarrow> (A' : (\<ge>) A) \<Rightarrow> ((x : A') \<rightarrow>\<^sub>c B x :: set \<Rightarrow> bool)) rel_restrict_left"
proof (intro mono_wrt_predI dep_mono_wrt_predI)
  fix R :: set and A' :: "set \<Rightarrow> bool" assume "((x : A) \<rightarrow> B x) R" "A' \<le> A"
  with mono_rel_dep_mono_wrt_pred_ge_crel_dep_mono_wrt_pred_rel_restrict_left
    have "((x : A') \<rightarrow>\<^sub>c B x) (rel R)\<restriction>\<^bsub>A'\<^esub>" by blast
  then show "((x : A') \<rightarrow>\<^sub>c B x) R\<restriction>\<^bsub>A'\<^esub>" by auto
qed

definition "set_crel_dep_mono_wrt_set A B :: set \<Rightarrow> bool \<equiv> ((x : mem_of A) \<rightarrow>\<^sub>c mem_of (B x))"
adhoc_overloading crel_dep_mono_wrt set_crel_dep_mono_wrt_set
definition "set_crel_mono_wrt_set A B :: set \<Rightarrow> bool \<equiv> (mem_of A \<rightarrow>\<^sub>c mem_of B)"
adhoc_overloading crel_mono_wrt set_crel_mono_wrt_set

lemma set_crel_dep_mono_wrt_set_eq_set_crel_dep_mono_wrt_pred [simp]:
  "(((x : A) \<rightarrow>\<^sub>c B x) :: set \<Rightarrow> bool) = ((x : mem_of A) \<rightarrow>\<^sub>c mem_of (B x))"
  unfolding set_crel_dep_mono_wrt_set_def by simp

lemma set_crel_dep_mono_wrt_set_eq_set_crel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "\<And>x. Q x \<equiv> mem_of (B x)"
  shows "((x : A) \<rightarrow>\<^sub>c B x) :: set \<Rightarrow> bool \<equiv> ((x : P) \<rightarrow>\<^sub>c Q x)"
  using assms by simp

lemma set_crel_dep_mono_wrt_set_iff_set_crel_dep_mono_wrt_pred [iff]:
  "((x : A) \<rightarrow>\<^sub>c B x) (R :: set) \<longleftrightarrow> ((x : mem_of A) \<rightarrow>\<^sub>c mem_of (B x)) R"
  by simp

lemma set_crel_mono_wrt_set_eq_set_crel_mono_wrt_pred [simp]:
  "((A \<rightarrow>\<^sub>c B) :: set \<Rightarrow> bool) = (mem_of A \<rightarrow>\<^sub>c mem_of B)"
  unfolding set_crel_mono_wrt_set_def by simp

lemma set_crel_mono_wrt_set_eq_set_crel_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "Q \<equiv> mem_of B"
  shows "(A \<rightarrow>\<^sub>c B) :: set \<Rightarrow> bool \<equiv> (P \<rightarrow>\<^sub>c Q)"
  using assms by simp

lemma set_crel_mono_wrt_set_iff_set_crel_mono_wrt_pred [iff]:
  "(A \<rightarrow>\<^sub>c B) (R :: set) \<longleftrightarrow> (mem_of A \<rightarrow>\<^sub>c mem_of B) R"
  by simp

lemma codom_subset_idx_union_if_set_crel_dep_mono_wrt_set [simp]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "codom R \<subseteq> (\<Union>x \<in> A. B x)"
  using assms by blast


subsubsection \<open>Set Function-Space\<close>

definition "set_set_crel_dep_mono_wrt_set A B \<equiv> {R \<in> powerset (\<Sum>x : A. B x) | ((x : A) \<rightarrow>\<^sub>c B x) R}"
adhoc_overloading crel_dep_mono_wrt set_set_crel_dep_mono_wrt_set
definition "set_set_crel_mono_wrt_set A B :: set \<equiv> (_ : A) \<rightarrow>\<^sub>c B"
adhoc_overloading crel_mono_wrt set_set_crel_mono_wrt_set

lemma set_set_crel_mono_wrt_set_eq_set_set_crel_dep_mono_wrt_set:
  "((A \<rightarrow>\<^sub>c B) :: set) = ((_ : A) \<rightarrow>\<^sub>c B)"
  unfolding set_set_crel_mono_wrt_set_def by auto

lemma set_set_crel_mono_wrt_set_eq_set_set_crel_dep_mono_wrt_set_uhint [uhint]:
  assumes "A :: set \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "A \<rightarrow>\<^sub>c B :: set \<equiv> (x : A') \<rightarrow>\<^sub>c B' x"
  using assms by (simp add: set_set_crel_mono_wrt_set_eq_set_set_crel_dep_mono_wrt_set)

lemma mem_crel_mono_wrt_set_iff_mem_crel_dep_mono_wrt_set: "R \<in> (A \<rightarrow>\<^sub>c B) \<longleftrightarrow> R \<in> ((_ : A) \<rightarrow>\<^sub>c B)"
  unfolding set_set_crel_mono_wrt_set_eq_set_set_crel_dep_mono_wrt_set by auto

lemma mem_crel_dep_mono_wrt_set_if_crel_dep_mono_wrt_set:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "R \<in> ((x : A) \<rightarrow>\<^sub>c B x)"
  using assms unfolding set_set_crel_dep_mono_wrt_set_def by auto

lemma crel_dep_mono_wrt_set_if_mem_crel_dep_mono_wrt_set:
  assumes "R \<in> ((x : A) \<rightarrow>\<^sub>c B x)"
  shows "((x : A) \<rightarrow>\<^sub>c B x) R"
  using assms unfolding set_set_crel_dep_mono_wrt_set_def by auto

lemma mem_of_crel_dep_mono_wrt_set_eq_crel_dep_mono_wrt_set [simp, set_to_HOL_simp]:
  "mem_of ((x : A) \<rightarrow>\<^sub>c B x) = ((x : A) \<rightarrow>\<^sub>c B x)"
  using mem_crel_dep_mono_wrt_set_if_crel_dep_mono_wrt_set
    crel_dep_mono_wrt_set_if_mem_crel_dep_mono_wrt_set
  by auto

corollary mem_of_crel_dep_mono_wrt_set_iff_crel_dep_mono_wrt_set [iff]:
  "R \<in> ((x : A) \<rightarrow>\<^sub>c B x) \<longleftrightarrow> ((x : A) \<rightarrow>\<^sub>c B x) R"
  by (simp flip: mem_of_iff)

lemma mem_crel_mono_wrt_set_if_crel_mono_wrt_set:
  assumes "(A \<rightarrow>\<^sub>c B) R"
  shows "R \<in> (A \<rightarrow>\<^sub>c B)"
  by (urule mem_crel_dep_mono_wrt_set_if_crel_dep_mono_wrt_set) (urule assms)

lemma crel_mono_wrt_set_if_mem_crel_mono_wrt_set:
  assumes "R \<in> (A \<rightarrow>\<^sub>c B)"
  shows "(A \<rightarrow>\<^sub>c B) R"
  using assms by (urule crel_dep_mono_wrt_set_if_mem_crel_dep_mono_wrt_set)

lemma mem_of_crel_mono_wrt_set_eq_crel_mono_wrt_set [simp, set_to_HOL_simp]:
  "mem_of (A \<rightarrow>\<^sub>c B) = (A \<rightarrow>\<^sub>c B)"
  by (urule mem_of_crel_dep_mono_wrt_set_eq_crel_dep_mono_wrt_set)

corollary mem_of_crel_mono_wrt_set_iff_crel_mono_wrt_set [iff]: "R \<in> (A \<rightarrow>\<^sub>c B) \<longleftrightarrow> (A \<rightarrow>\<^sub>c B) R"
  by (simp flip: mem_of_iff)

lemma crel_mono_wrt_set_eq_singleton_empty: "((x : {}) \<rightarrow>\<^sub>c B x) = {{}}"
  by (intro eqI') simp

lemma set_set_crel_dep_mono_wrt_set_covariant_codom:
  assumes "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> B' x"
  shows "((x : A) \<rightarrow>\<^sub>c B x) \<subseteq> ((x : A) \<rightarrow>\<^sub>c B' x)"
  by (urule subsetI, urule set_crel_dep_mono_wrt_pred_covariant_codom)
  (use assms in blast)+

(* lemma eq_if_mem_if_mem_agree_if_mem_dep_functions:
  assumes mem_dep_functions: "\<And>f. f \<in> F \<Longrightarrow> \<exists>B. f \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)"
  and "agree A F"
  and "f \<in> F"
  and "g \<in> F"
  shows "f = g"
  using assms
proof -
  have "\<And>f. f \<in> F \<Longrightarrow> \<exists>B. f \<subseteq> \<Sum>x \<in> A. (B x)" by (blast dest: mem_dep_functions)
  with assms show ?thesis by (intro eq_if_subset_dep_pairs_if_agree_set)
qed

lemma subset_if_agree_set_if_mem_dep_functions:
  assumes "f \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)"
  and "f \<in> F"
  and "agree A F"
  and "g \<in> F"
  shows "f \<subseteq> g"
  using assms
  by (elim mem_dep_functionsE subset_if_agree_set_if_subset_dep_pairs) auto

lemma agree_set_if_eval_eq_if_mem_dep_functions:
  assumes mem_dep_functions: "\<And>f. f \<in> F \<Longrightarrow> \<exists>B. f \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)"
  and "\<And>f g x. f \<in> F \<Longrightarrow> g \<in> F \<Longrightarrow> x \<in> A \<Longrightarrow> R`x = g`x"
  shows "agree A F"
proof (subst agree_set_set_iff_agree_set, rule agree_setI)
  fix x y f g presume hyps: "f \<in> F" "g \<in> F" "x \<in> A" and "\<langle>x, y\<rangle> \<in> R"
  then have "y = R`x" using mem_dep_functions by auto
  also have "... = g`x" by (fact assms(2)[OF hyps])
  finally have y_eq: "y = g`x" .
  from mem_dep_functions[OF \<open>g \<in> F\<close>] obtain B where "g \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)" by blast
  with y_eq pair_mem_iff_eval_eq_if_mem_dom_dep_function \<open>x \<in> A\<close> show "\<langle>x, y\<rangle> \<in> g" by blast
qed simp_all

lemma eq_if_agree_if_mem_dep_functions:
  assumes "f \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)" "g \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)"
  and "agree A {f, g}"
  shows "f = g"
  using assms
  by (intro eq_if_mem_if_mem_agree_if_mem_dep_functions[of "{f, g}"]) auto

lemma dep_functions_eval_eqI:
  assumes "f \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)"
  and "g \<in> (x \<in> A') \<rightarrow>\<^sub>cs (B' x)"
  and "f \<subseteq> g"
  and "x \<in> A \<inter> A'"
  shows "R`x = g`x"
  using assms by (auto dest: right_unique_onD)

lemma dep_functions_eq_if_subset:
  assumes f_mem: "f \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)"
  and g_mem: "g \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B' x)"
  and "f \<subseteq> g"
  shows "f = g"
proof (rule eqI)
  fix p assume "p \<in> g"
  with g_mem obtain x y where [simp]: "p = \<langle>x, y\<rangle>" "g`x = y" "x \<in> A" by auto
  with assms have [simp]: "R`x = g`x" by (intro dep_functions_eval_eqI) auto
  show "p \<in> f" using f_mem by (auto iff: pair_mem_iff_eval_eq_if_mem_dom_dep_function)
qed (use assms in auto)

lemma ex_dom_mem_dep_functions_iff:
  "(\<exists>A. f \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)) \<longleftrightarrow> f \<in> (x \<in> dom R) \<rightarrow>\<^sub>cs (B x)"
  by auto

lemma mem_dep_functions_empty_dom_iff_eq_empty [iff]:
  "(f \<in> (x \<in> {}) \<rightarrow>\<^sub>cs (B x)) \<longleftrightarrow> f = {}"
  by auto

lemma empty_mem_dep_functions: "{} \<in> (x \<in> {}) \<rightarrow>\<^sub>cs (B x)" by simp

lemma eq_singleton_if_mem_functions_singleton [simp]:
  "f \<in> {a} \<rightarrow>\<^sub>cs {b} \<Longrightarrow> f = {\<langle>a, b\<rangle>}"
  by force

lemma singleton_mem_functionsI [intro]: "y \<in> B \<Longrightarrow> {\<langle>x, y\<rangle>} \<in> {x} \<rightarrow>\<^sub>cs B"
  by fastforce

lemma mem_dep_functions_collectI:
  assumes "f \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)"
  and "\<And>x. x \<in> A \<Longrightarrow> P x (R`x)"
  shows "f \<in> (x \<in> A) \<rightarrow>\<^sub>cs {y \<in> B x | P x y}"
  by (rule mem_dep_functions_covariant_codom) (use assms in auto)

lemma mem_dep_functions_collectE:
  assumes "f \<in> (x \<in> A) \<rightarrow>\<^sub>cs {y \<in> B x | P x y}"
  obtains "f \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)" and "\<And>x. x \<in> A \<Longrightarrow> P x (R`x)"
proof
  from assms show "f \<in> (x \<in> A) \<rightarrow>\<^sub>cs (B x)"
    by (rule mem_dep_functions_covariant_codom_subset) auto
  fix x assume "x \<in> A"
  with assms show "P x (R`x)"
    by (auto dest: pair_eval_mem_if_mem_if_mem_dep_functions)
qed *)

end
