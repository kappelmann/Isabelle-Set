\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Binary Relations\<close>
theory HOTG_Binary_Relations_Base
  imports
    HOTG_Empty_Set
    HOTG_Pairs
    HOTG_Replacement_Predicates
    Transport.Dependent_Binary_Relations
begin

unbundle no HOL_ascii_syntax

definition "rel R x y \<equiv> \<langle>x, y\<rangle> \<in> R"

lemma rel_eq: "rel = (\<lambda>R x y. \<langle>x, y\<rangle> \<in> R)" unfolding rel_def by simp
lemma rel_iff [iff]: "rel R x y \<longleftrightarrow> \<langle>x, y\<rangle> \<in> R" unfolding rel_def by simp
declare rel_iff[symmetric, set_to_HOL_simp]

lemma rel_eq_pair_mem_uhint [uhint]:
  assumes "x \<equiv> x'"
  and "y \<equiv> y'"
  and "R \<equiv> R'"
  shows "rel R x y \<equiv> \<langle>x', y'\<rangle> \<in> R'"
  using assms by simp

lemma rel_empty_eq_bottom [simp,set_to_HOL_simp]: "rel {} = \<bottom>" by (intro ext) auto

lemma rel_collect_eq_rel_sup_curry [set_to_HOL_simp]: "rel {x \<in> A | P x} = rel A \<sqinter> curry P"
  by (intro ext) auto

lemma rel_bin_union_eq_rel_sup_rel_sup [set_to_HOL_simp]: "rel (A \<union> B) = rel A \<squnion> rel B"
  by force

lemma rel_bin_inter_eq_rel_inf_rel_inf [set_to_HOL_simp]: "rel (A \<inter> B) = rel A \<sqinter> rel B"
  by force

definition "is_bin_rel (R :: set) \<equiv> \<forall>p : R. is_pair p"

lemma is_bin_relI [intro]:
  assumes "\<And>p. p \<in> R \<Longrightarrow> is_pair p"
  shows "is_bin_rel R"
  using assms unfolding is_bin_rel_def by blast

lemma is_bin_relE:
  assumes "is_bin_rel R"
  obtains "\<And>p. p \<in> R \<Longrightarrow> is_pair p"
  using assms unfolding is_bin_rel_def by blast

lemma is_bin_relD [dest]:
  assumes "is_bin_rel R"
  and "p \<in> R"
  shows "is_pair p"
  using assms by (blast elim: is_bin_relE)

lemma is_bin_rel_empty [iff]: "is_bin_rel {}" by auto

lemma is_bin_rel_unionI [intro]:
  assumes "\<And>r. r \<in> R \<Longrightarrow> is_bin_rel r"
  shows "is_bin_rel (\<Union>R)"
  using assms by force

lemma is_bin_rel_bin_unionI [intro]:
  assumes "is_bin_rel A" "is_bin_rel B"
  shows "is_bin_rel (A \<union> B)"
  using assms by auto

lemma is_bin_rel_interI [intro]:
  assumes "\<And>r. r \<in> R \<Longrightarrow> is_bin_rel r"
  shows "is_bin_rel (\<Inter>R)"
  using assms by (intro is_bin_relI) blast

lemma is_bin_rel_bin_interI [intro]:
  assumes "is_bin_rel A" "is_bin_rel B"
  shows "is_bin_rel (A \<inter> B)"
  using assms by auto

lemma rel_le_rel_if_subset:
  assumes "R \<subseteq> R'"
  shows "rel R \<le> rel R'"
  using assms by (blast dest: fun_cong)

lemma subset_if_rel_le_rel_if_is_bin_rel:
  assumes "is_bin_rel R"
  and "rel R \<le> rel R'"
  shows "R \<subseteq> R'"
  using assms by blast

corollary subset_iff_rel_le_rel_if_is_bin_rel [simp, set_to_HOL_simp]:
  assumes "is_bin_rel R"
  shows "R \<subseteq> R' \<longleftrightarrow> rel R \<le> rel R'"
  using assms by (auto intro: rel_le_rel_if_subset subset_if_rel_le_rel_if_is_bin_rel)

corollary subset_iff_rel_le_rel_if_is_bin_rel_uhint [uhint]:
  assumes "is_bin_rel R"
  and "R \<equiv> S"
  and "R' \<equiv> S'"
  shows "R \<subseteq> R' \<equiv> rel S \<le> rel S'"
  using assms by simp

corollary mem_of_le_mem_of_iff_rel_le_rel_if_is_bin_rel [simp, set_to_HOL_simp]:
  assumes "is_bin_rel R"
  shows "mem_of R \<le> mem_of R' \<longleftrightarrow> rel R \<le> rel R'"
  supply set_to_HOL_simp[simp]
  using assms by (urule subset_iff_rel_le_rel_if_is_bin_rel)

corollary mem_of_le_mem_of_iff_rel_le_rel_if_is_bin_rel_uhint [uhint]:
  assumes "is_bin_rel R"
  and "R \<equiv> S"
  and "R' \<equiv> S'"
  shows "mem_of R \<le> mem_of R' \<equiv> rel S \<le> rel S'"
  using assms by simp

lemma eq_if_rel_eq_rel_if_is_bin_rel:
  assumes "is_bin_rel R" "is_bin_rel R'"
  and "rel R = rel R'"
  shows "R = R'"
  using assms by auto

corollary eq_iff_rel_eq_rel_if_is_bin_rel [simp, set_to_HOL_simp]:
  assumes "is_bin_rel R" "is_bin_rel R'"
  shows "R = R' \<longleftrightarrow> rel R = rel R'"
  using assms by (auto intro: eq_if_rel_eq_rel_if_is_bin_rel)

corollary eq_iff_rel_eq_rel_if_is_bin_rel_uhint [uhint]:
  assumes "is_bin_rel R" "is_bin_rel R'"
  and "R \<equiv> S"
  and "R' \<equiv> S'"
  shows "R = R' \<equiv> rel S = rel S'"
  using assms by simp

corollary mem_of_eq_mem_of_iff_rel_eq_rel_if_is_bin_rel [simp, set_to_HOL_simp]:
  assumes "is_bin_rel R" "is_bin_rel R'"
  shows "mem_of R = mem_of R' \<longleftrightarrow> rel R = rel R'"
  supply set_to_HOL_simp[simp]
  using assms by (urule eq_iff_rel_eq_rel_if_is_bin_rel)

corollary mem_of_eq_mem_of_iff_rel_eq_rel_if_is_bin_rel_uhint [uhint]:
  assumes "is_bin_rel R" "is_bin_rel R'"
  and "R \<equiv> S"
  and "R' \<equiv> S'"
  shows "mem_of R = mem_of R' \<equiv> rel S = rel S'"
  using assms by simp

corollary mem_of_eq_bottom_iff_rel_eq_bottom_if_is_bin_rel [simp]:
  assumes "is_bin_rel R"
  shows "mem_of R = \<bottom> \<longleftrightarrow> rel R = \<bottom>"
  supply set_to_HOL_simp[uhint]
  using assms by (urule mem_of_eq_mem_of_iff_rel_eq_rel_if_is_bin_rel) simp

corollary mem_of_eq_bottom_eq_rel_eq_bottom_if_is_bin_rel_uhint [uhint]:
  assumes "is_bin_rel R"
  and "R \<equiv> S"
  shows "mem_of R = \<bottom> \<equiv> rel S = \<bottom>"
  using assms by simp

lemma is_bin_rel_if_subset_if_is_bin_rel:
  assumes "is_bin_rel R"
  and "R' \<subseteq> R"
  shows "is_bin_rel R'"
  using assms by (intro is_bin_relI) blast

definition "dep_bin_rel_set A B :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> {\<Sum>}x : mem_of A. mem_of (B x)"
adhoc_overloading dep_bin_rel dep_bin_rel_set

lemma dep_bin_rel_set_eq_dep_bin_rel_pred [simp]: "({\<Sum>}x : A. B x) = {\<Sum>}x : mem_of A. mem_of (B x)"
  unfolding dep_bin_rel_set_def by simp

lemma dep_bin_rel_set_eq_dep_bin_rel_pred_uhint [uhint]:
  assumes "A' \<equiv> mem_of A"
  and "\<And>x. B' x \<equiv> mem_of (B x)"
  shows "{\<Sum>}x : A. B x \<equiv> {\<Sum>}x : A'. B' x"
  using assms by simp

lemma dep_bin_rel_set_iff_dep_bin_rel_pred [iff]:
  "({\<Sum>}x : A. B x) R \<longleftrightarrow> ({\<Sum>}x : mem_of A. mem_of (B x)) R"
  by simp

definition "bin_rel_set A B :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> mem_of A {\<times>} mem_of B"
adhoc_overloading bin_rel bin_rel_set

lemma bin_rel_set_eq_bin_rel_pred [simp]: "A {\<times>} B = mem_of A {\<times>} mem_of B"
  unfolding bin_rel_set_def by simp

lemma bin_rel_set_eq_bin_rel_pred_uhint [uhint]:
  assumes "A' \<equiv> mem_of A"
  and "B' \<equiv> mem_of B"
  shows "A {\<times>} B \<equiv> A' {\<times>} B'"
  using assms by simp

lemma bin_rel_set_iff_bin_rel_pred [iff]: "(A {\<times>} B) R \<longleftrightarrow> (mem_of A {\<times>} mem_of B) R"
  by simp

definition "set_dep_bin_rel_pred (A :: set \<Rightarrow> bool) (B :: set \<Rightarrow> set \<Rightarrow> bool) (R :: set) \<equiv>
  ({\<Sum>}x : A. B x) (rel R) \<and> is_bin_rel R"
adhoc_overloading dep_bin_rel set_dep_bin_rel_pred

definition "set_bin_rel_pred (A :: set \<Rightarrow> bool) (B :: set \<Rightarrow> bool) :: set \<Rightarrow> bool \<equiv> {\<Sum>}_ : A. B"
adhoc_overloading bin_rel set_bin_rel_pred

lemma set_bin_rel_pred_eq_set_dep_bin_rel_pred:
  "((A :: set \<Rightarrow> bool) {\<times>} B :: set \<Rightarrow> _) = {\<Sum>}_ : A. B"
  unfolding set_bin_rel_pred_def by simp

lemma set_bin_rel_pred_eq_set_dep_bin_rel_pred_uhint [uhint]:
  assumes "A :: set \<Rightarrow> bool \<equiv> A'"
  and "\<And>x. B :: set \<Rightarrow> bool \<equiv> B' x"
  shows "A {\<times>} B :: set \<Rightarrow> bool \<equiv> {\<Sum>}x : A'. B' x"
  using assms by (simp add: set_bin_rel_pred_eq_set_dep_bin_rel_pred)

lemma set_bin_rel_pred_iff_set_dep_bin_rel_pred:
  "((A :: set \<Rightarrow> bool) {\<times>} B) (R :: set) \<longleftrightarrow> ({\<Sum>}_ : A. B) R"
  unfolding set_bin_rel_pred_eq_set_dep_bin_rel_pred by simp

lemma set_dep_bin_relI [intro]:
  assumes "({\<Sum>}x : A. B x) (rel R)"
  and "is_bin_rel R"
  shows "({\<Sum>}x : A. B x) R"
  using assms unfolding set_dep_bin_rel_pred_def by auto

lemma set_dep_bin_relE [elim]:
  assumes "({\<Sum>}x : A. B x) R"
  obtains "({\<Sum>}x : A. B x) (rel R)" "is_bin_rel R"
  using assms unfolding set_dep_bin_rel_pred_def by auto

lemma set_dep_bin_rel_pred_eq_dep_bin_rel_pred_uhint [uhint]:
  assumes "is_bin_rel R"
  and "A \<equiv> A'"
  and "B \<equiv> B'"
  and "R' \<equiv> rel R"
  shows "({\<Sum>}x : A. B x) R \<equiv> ({\<Sum>}x : A'. B' x) R'"
  using assms by (intro eq_reflection) auto

lemma set_dep_bin_rel_cong [cong]: "\<lbrakk>A = A'; \<And>x. A' x \<Longrightarrow> (B x :: set \<Rightarrow> bool) = B' x\<rbrakk> \<Longrightarrow>
  (({\<Sum>}x : A. B x) :: set \<Rightarrow> bool) = {\<Sum>}x : A'. B' x"
  by (intro ext iffI set_dep_bin_relI dep_bin_relI) (auto 0 3)

corollary is_bin_rel_if_set_dep_bin_rel:
  assumes "({\<Sum>}x : A. B x) R"
  shows "is_bin_rel R"
  using assms by blast

lemma set_bin_relI [intro]:
  assumes "(A {\<times>} B) (rel R)"
  and "is_bin_rel R"
  shows "(A {\<times>} B) R"
  using assms by (urule set_dep_bin_relI)

lemma set_bin_relE [elim]:
  assumes "(A {\<times>} B) R"
  obtains "(A {\<times>} B) (rel R)" "is_bin_rel R"
  using assms by (urule (e) set_dep_bin_relE)

lemma set_bin_rel_pred_eq_bin_rel_pred_uhint [uhint]:
  assumes "is_bin_rel R"
  and "A \<equiv> A'"
  and "B \<equiv> B'"
  and "R' \<equiv> rel R"
  shows "(A {\<times>} B) R \<equiv> (A' {\<times>} B') R'"
  by (urule set_dep_bin_rel_pred_eq_dep_bin_rel_pred_uhint) (use assms in auto)

lemma le_set_dep_bin_rel_if_le_dom:
  assumes "A \<le> A'"
  shows "(({\<Sum>}x : A. B x) :: set \<Rightarrow> bool) \<le> ({\<Sum>}x : A'. B x)"
  using assms by (intro le_predI set_dep_bin_relI dep_bin_relI) blast+

lemma set_dep_bin_rel_covariant_codom:
  assumes "({\<Sum>}x : A. B x) R"
  and "\<And>x y. \<langle>x, y\<rangle> \<in> R \<Longrightarrow> A x \<Longrightarrow> B x y \<Longrightarrow> B' x y"
  shows "({\<Sum>}x : A. B' x) R"
  using assms by (intro set_dep_bin_relI) blast+

lemma mono_set_dep_bin_rel: "(((\<le>) :: (set \<Rightarrow> bool) \<Rightarrow> _) \<Rightarrow> (\<le>) \<Rrightarrow> (\<supseteq>) \<Rrightarrow> (\<le>)) dep_bin_rel"
  by (intro mono_wrt_relI Fun_Rel_relI set_dep_bin_relI le_boolI) (blast intro!: is_bin_relI)+

lemma mono_set_bin_rel: "(((\<le>) :: (set \<Rightarrow> bool) \<Rightarrow> _) \<Rightarrow> (\<le>) \<Rrightarrow> (\<supseteq>) \<Rrightarrow> (\<le>)) ({\<times>})"
  by (intro mono_wrt_relI Fun_Rel_relI set_bin_relI le_boolI) (blast intro!: is_bin_relI)+

lemma set_dep_bin_rel_bottom_dom_iff_eq_empty [iff]: "({\<Sum>}x : (\<bottom> :: set \<Rightarrow> bool). B x) R \<longleftrightarrow> R = {}"
  by (intro iffI) auto

lemma set_dep_bin_rel_bottom_codom_iff_eq_empty [iff]: "({\<Sum>}x : A. \<bottom>) R \<longleftrightarrow> R = {}"
  by (intro iffI) auto

lemma mono_set_dep_bin_rel_dep_bin_rel_rel: "(({\<Sum>}x : A. B x :: set \<Rightarrow> bool) \<Rightarrow> {\<Sum>}x : A. B x) rel"
  by auto

definition "set_dep_bin_rel_set (A :: set) (B :: set \<Rightarrow> set) :: set \<Rightarrow> bool \<equiv>
  {\<Sum>}x : mem_of A. mem_of (B x)"
adhoc_overloading dep_bin_rel set_dep_bin_rel_set

lemma set_dep_bin_rel_set_eq_set_dep_bin_rel_pred [simp]:
  "({\<Sum>}x : A. B x :: set \<Rightarrow> bool) = {\<Sum>}x : mem_of A. mem_of (B x)"
  unfolding set_dep_bin_rel_set_def by simp

lemma set_dep_bin_rel_set_eq_dep_bin_rel_pred_uhint [uhint]:
  assumes "A' \<equiv> mem_of A"
  and "\<And>x. B' x \<equiv> mem_of (B x)"
  shows "{\<Sum>}x : A. B x :: set \<Rightarrow> bool \<equiv> {\<Sum>}x : A'. B' x"
  using assms by simp

lemma set_dep_bin_rel_set_iff_set_dep_bin_rel_pred [iff]:
  "({\<Sum>}x : A. B x) (R :: set) \<longleftrightarrow> ({\<Sum>}x : mem_of A. mem_of (B x)) R"
  by simp

lemma subset_dep_pair_if_dep_bin_rel:
  assumes "({\<Sum>}x : A. B x) R"
  shows "R \<subseteq> \<Sum>x : A. B x"
  using assms by force

lemma dep_bin_rel_if_subset_dep_pair:
  assumes "R \<subseteq> \<Sum>x : A. B x"
  shows "({\<Sum>}x : A. B x) R"
  using assms by force

corollary supset_dep_pair_eq_dep_bin_rel [simp, set_to_HOL_simp]: "(\<supseteq>) (\<Sum>x : A. B x) = ({\<Sum>}x : A. B x)"
  using subset_dep_pair_if_dep_bin_rel dep_bin_rel_if_subset_dep_pair by (intro ext iffI) blast

corollary subset_dep_pair_iff_dep_bin_rel [iff]: "R \<subseteq> (\<Sum>x : A. B x) \<longleftrightarrow> ({\<Sum>}x : A. B x) R"
  by (fact supset_dep_pair_eq_dep_bin_rel[THEN fun_cong])

corollary subset_dep_pair_eq_dep_bin_rel_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B x \<equiv> B' x"
  and "R \<equiv> R'"
  shows "R \<subseteq> \<Sum>x : A. B x \<equiv> ({\<Sum>}x : A'. B' x) R'"
  using assms by simp

lemma set_dep_bin_rel_set_dep_pair: "({\<Sum>}x : A. B x) (\<Sum>x : A. B x :: set)" by blast

definition "set_bin_rel_set (A :: set) (B :: set) :: set \<Rightarrow> bool \<equiv> mem_of A {\<times>} mem_of B"
adhoc_overloading bin_rel set_bin_rel_set

lemma set_bin_rel_set_eq_set_bin_rel_pred [simp]: "(A {\<times>} B :: set \<Rightarrow> bool) = mem_of A {\<times>} mem_of B"
  unfolding set_bin_rel_set_def by simp

lemma set_bin_rel_set_eq_bin_rel_pred_uhint [uhint]:
  assumes "A' \<equiv> mem_of A"
  and "B' \<equiv> mem_of B"
  shows "A {\<times>} B :: set \<Rightarrow> bool \<equiv> A' {\<times>} B'"
  using assms by simp

lemma set_bin_rel_set_iff_set_bin_rel_pred [iff]:
  "(A {\<times>} B) (R :: set) \<longleftrightarrow> (mem_of A {\<times>} mem_of B) R"
  by simp

corollary subset_pair_if_bin_rel:
  assumes "(A {\<times>} B) R"
  shows "R \<subseteq> A \<times> B"
  supply set_bin_rel_pred_eq_set_dep_bin_rel_pred[simp]
  using assms by (urule subset_dep_pair_if_dep_bin_rel)

corollary bin_rel_if_subset_pair:
  assumes "R \<subseteq> A \<times> B"
  shows "(A {\<times>} B) R"
  using assms by (urule dep_bin_rel_if_subset_dep_pair)

corollary supset_pair_eq_bin_rel [simp, set_to_HOL_simp]: "(\<supseteq>) (A \<times> B) = (A {\<times>} B)"
  by (urule supset_dep_pair_eq_dep_bin_rel)

corollary subset_pair_eq_bin_rel_uhint [uhint]:
  assumes "A :: set \<equiv> A'"
  and "B \<equiv> B'"
  and "R \<equiv> R'"
  shows "R \<subseteq> A \<times> B \<equiv> (A' {\<times>} B') R'"
  using assms by (urule subset_dep_pair_eq_dep_bin_rel_uhint)

corollary subset_pair_iff_bin_rel [iff]: "R \<subseteq> (A \<times> B) \<longleftrightarrow> (A {\<times>} B) R"
  by (urule subset_dep_pair_iff_dep_bin_rel)

lemma set_bin_rel_set_pair: "(A {\<times>} B) (A \<times> B :: set)" by blast

lemma set_dep_bin_rel_fst_snd_if_is_bin_rel:
  assumes "is_bin_rel R"
  shows "({\<Sum>}x : {fst p | p \<in> R}. {y | p \<in> R, p = \<langle>x, y\<rangle>}) R"
  using assms by fastforce

corollary set_dep_bin_rel_set_if_is_bin_relE:
  assumes "is_bin_rel R"
  obtains A :: set and B where "({\<Sum>}x : A. B x) R"
  using set_dep_bin_rel_fst_snd_if_is_bin_rel[OF assms] by auto

corollary is_bin_rel_iff_ex_set_dep_bin_rel:
  "is_bin_rel R \<longleftrightarrow> (\<exists>(A :: set \<Rightarrow> bool) B. ({\<Sum>}x : A. B x) R)"
  by blast

corollary ex_set_dep_bin_rel_iff_ex_set_dep_bin_rel_set:
  "(\<exists>(P :: set \<Rightarrow> bool) B. ({\<Sum>}x : P. B x) (R :: set)) \<longleftrightarrow> (\<exists>(A :: set) B. ({\<Sum>}x : A. B x) R)"
proof (rule iffI; elim exE)
  fix P :: "set \<Rightarrow> bool" and B assume "({\<Sum>}x : P. B x) R"
  with set_dep_bin_rel_set_if_is_bin_relE obtain A' :: set and B' where "({\<Sum>}x : A'. B' x) R"
    by blast
  then show "\<exists>(A :: set) B. ({\<Sum>}x : A. B x) R" by auto
qed auto

lemma fst_set_bin_rel_snd_if_is_bin_rel:
  assumes "is_bin_rel R"
  shows "({fst p | p \<in> R} {\<times>} {snd p | p \<in> R}) R"
  using assms by fastforce

corollary set_bin_rel_set_if_is_bin_relE:
  assumes "is_bin_rel R"
  obtains A B :: set where "(A {\<times>} B) R"
  using assms fst_set_bin_rel_snd_if_is_bin_rel by blast

corollary is_bin_rel_iff_ex_set_dep_bin_rel_set: "is_bin_rel R \<longleftrightarrow> (\<exists>(A :: set) B. (A {\<times>} B) R)"
  by (intro iffI; elim exE set_bin_rel_set_if_is_bin_relE) auto


end