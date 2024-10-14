\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Set Functions\<close>
theory HOTG_Functions_Base
  imports
    HOTG_Functions_Evaluation
    Transport.Binary_Relations_Function_Base
begin

unbundle no HOL_ascii_syntax

definition "rel_dep_mono_wrt_set A B :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> (x : mem_of A) \<rightarrow> mem_of (B x)"
adhoc_overloading rel_dep_mono_wrt rel_dep_mono_wrt_set
definition "rel_mono_wrt_set A B :: (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> bool \<equiv> mem_of A \<rightarrow> mem_of B"
adhoc_overloading rel_mono_wrt rel_mono_wrt_set

lemma rel_dep_mono_wrt_set_eq_rel_dep_mono_wrt_pred [simp]:
  "((x : A) \<rightarrow> B x) = ((x : mem_of A) \<rightarrow> mem_of (B x))"
  unfolding rel_dep_mono_wrt_set_def by simp

lemma rel_dep_mono_wrt_set_eq_rel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "\<And>x. Q x \<equiv> mem_of (B x)"
  shows "((x : A) \<rightarrow> B x) \<equiv> ((x : P) \<rightarrow> Q x)"
  using assms by simp

lemma rel_dep_mono_wrt_set_iff_rel_dep_mono_wrt_pred [iff]:
  "((x : A) \<rightarrow> B x) R \<longleftrightarrow> ((x : mem_of A) \<rightarrow> mem_of (B x)) R"
  by simp

lemma rel_mono_wrt_set_eq_rel_mono_wrt_pred [simp]: "(A \<rightarrow> B) = (mem_of A \<rightarrow> mem_of B)"
  unfolding rel_mono_wrt_set_def by simp

lemma rel_mono_wrt_set_eq_rel_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "Q \<equiv> mem_of B"
  shows "(A \<rightarrow> B) \<equiv> (P \<rightarrow> Q)"
  using assms by simp

lemma rel_mono_wrt_set_iff_rel_mono_wrt_pred [iff]: "(A \<rightarrow> B) R \<longleftrightarrow> (mem_of A \<rightarrow> mem_of B) R"
  by simp

definition "set_rel_dep_mono_wrt_pred (A :: set \<Rightarrow> bool) (B :: set \<Rightarrow> set \<Rightarrow> bool) (R :: set) \<equiv>
  ((x : A) \<rightarrow> B x) (rel R)"
adhoc_overloading rel_dep_mono_wrt set_rel_dep_mono_wrt_pred
definition "set_rel_mono_wrt_pred (A :: set \<Rightarrow> bool) (B :: set \<Rightarrow> bool) (R :: set) \<equiv> (A \<rightarrow> B) (rel R)"
adhoc_overloading rel_mono_wrt set_rel_mono_wrt_pred

lemma set_rel_dep_mono_wrt_pred_iff_rel_dep_mono_wrt_pred [iff]:
  "((x : A) \<rightarrow> B x) R \<longleftrightarrow> ((x : A) \<rightarrow> B x) (rel R)"
  unfolding set_rel_dep_mono_wrt_pred_def by simp

lemma set_rel_dep_mono_wrt_pred_eq_rel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B x \<equiv> B' x"
  and "R' \<equiv> rel R"
  shows "((x : A) \<rightarrow> B x) R \<equiv> ((x : A') \<rightarrow> B' x) R'"
  using assms by simp

lemma set_rel_mono_wrt_pred_iff_rel_mono_wrt_pred [iff]: "(A \<rightarrow> B) R \<longleftrightarrow> (A \<rightarrow> B) (rel R)"
  unfolding set_rel_mono_wrt_pred_def by simp

lemma set_rel_mono_wrt_pred_eq_rel_mono_wrt_pred_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "B \<equiv> B'"
  and "R' \<equiv> rel R"
  shows "(A \<rightarrow> B) R \<equiv> (A' \<rightarrow> B') R'"
  using assms by simp

lemma set_rel_mono_wrt_pred_eq_set_rel_dep_mono_wrt_pred:
  "(A \<rightarrow> B :: set \<Rightarrow> bool) = ((_ : A) \<rightarrow> B)"
  by (intro ext) (urule refl)

lemma set_rel_mono_wrt_pred_eq_set_rel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "(A \<rightarrow> B :: set \<Rightarrow> bool) = ((_ : A) \<rightarrow> B)"
  using assms set_rel_mono_wrt_pred_eq_set_rel_dep_mono_wrt_pred by simp

definition "set_rel_dep_mono_wrt_set A B :: set \<Rightarrow> bool \<equiv> ((x : mem_of A) \<rightarrow> mem_of (B x))"
adhoc_overloading rel_dep_mono_wrt set_rel_dep_mono_wrt_set
definition "set_rel_mono_wrt_set A B :: set \<Rightarrow> bool \<equiv> (mem_of A \<rightarrow> mem_of B)"
adhoc_overloading rel_mono_wrt set_rel_mono_wrt_set

lemma set_rel_dep_mono_wrt_set_eq_set_rel_dep_mono_wrt_pred [simp]:
  "(((x : A) \<rightarrow> B x) :: set \<Rightarrow> bool) = ((x : mem_of A) \<rightarrow> mem_of (B x))"
  unfolding set_rel_dep_mono_wrt_set_def by simp

lemma set_rel_dep_mono_wrt_set_eq_set_rel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "\<And>x. Q x \<equiv> mem_of (B x)"
  shows "((x : A) \<rightarrow> B x) :: set \<Rightarrow> bool \<equiv> ((x : P) \<rightarrow> Q x)"
  using assms by simp

lemma set_rel_dep_mono_wrt_set_iff_set_rel_dep_mono_wrt_pred [iff]:
  "((x : A) \<rightarrow> B x) (R :: set) \<longleftrightarrow> ((x : mem_of A) \<rightarrow> mem_of (B x)) R"
  by simp

lemma set_rel_mono_wrt_set_eq_set_rel_mono_wrt_pred [simp]:
  "((A \<rightarrow> B) :: set \<Rightarrow> bool) = (mem_of A \<rightarrow> mem_of B)"
  unfolding set_rel_mono_wrt_set_def by simp

lemma set_rel_mono_wrt_set_eq_set_rel_mono_wrt_pred_uhint [uhint]:
  assumes "P \<equiv> mem_of A"
  and "Q \<equiv> mem_of B"
  shows "(A \<rightarrow> B) :: set \<Rightarrow> bool \<equiv> (P \<rightarrow> Q)"
  using assms by simp

lemma set_rel_mono_wrt_set_iff_set_rel_mono_wrt_pred [iff]:
  "(A \<rightarrow> B) (R :: set) \<longleftrightarrow> (mem_of A \<rightarrow> mem_of B) R"
  by simp

lemma mono_set_rel_dep_mono_wrt_pred_dep_mono_wrt_pred_eval_set:
  "(((x : (A :: set \<Rightarrow> bool)) \<rightarrow> B x) \<Rightarrow> (x : A) \<Rightarrow> B x) eval_set"
  by fastforce

lemma mono_set_rel_dep_mono_wrt_pred_top_set_rel_dep_mono_wrt_pred_inf_set_rel_restrict_left:
  "(((x : A) \<rightarrow> B x) \<Rightarrow> (A' : \<top>) \<Rightarrow> ((x : A \<sqinter> A') \<rightarrow> B x :: set \<Rightarrow> bool)) rel_restrict_left"
  by (urule (rr) dep_mono_wrt_predI rel_dep_mono_wrt_predI
    (*TODO: should be solved by some type-checking automation*)
    mono_right_unique_on_top_right_unique_on_inf_rel_restrict_left
      [THEN dep_mono_wrt_predD, THEN dep_mono_wrt_predD]
    mono_left_total_on_top_left_total_on_inf_rel_restrict_left
      [THEN dep_mono_wrt_predD, THEN dep_mono_wrt_predD])
  auto

definition "set_id A \<equiv> {\<langle>a, a\<rangle> | a \<in> A}"

lemma mk_pair_mem_idI [intro!]: "a \<in> A \<Longrightarrow> \<langle>a, a\<rangle> \<in> set_id A"
  unfolding set_id_def by auto

lemma mem_idE [elim!]:
  assumes "p \<in> set_id A"
  obtains a where "a \<in> A" "p = \<langle>a, a\<rangle>"
  using assms unfolding set_id_def by auto

lemma mono_subset_id: "((\<subseteq>) \<Rightarrow> (\<subseteq>)) set_id" by fast

lemma is_bin_rel_id [iff]: "is_bin_rel (set_id A)" by auto

lemma rel_id_eq_eq_restrict [simp, set_to_HOL_simp]: "rel (set_id A) = (=)\<restriction>\<^bsub>A\<^esub>"
  by auto

lemma set_id_eval_eq_if_mem [simp]:
  assumes "x \<in> A"
  shows "(set_id A)`x = x"
  using assms by simp

end