\<^marker>\<open>creator "Bohua Zhan"\<close>
\<^marker>\<open>contributor "Kevin Kappelmann"\<close>
section \<open>Set Proof Steps\<close>
theory Proof_Steps_Sets
imports
  Auto2_HOTG
  HOTG.Set_Difference
begin
paragraph \<open>Summary\<close>
text \<open>Setup for proof steps related to sets. Adapted from \<open>Auto2/HOL/Set_Thms.thy\<close>.\<close>

subsection \<open>Set\<close>

(*subsubsection \<open>Injective Functions\<close>

setup \<open>add_backward_prfstep @{thm injI}\<close>*)

subsubsection \<open>AC property of intersection and union\<close>

setup \<open>fold Auto2_HOTG_Extra_Setup.ACUtil.add_ac_data [
  {cfhead = @{cterm bin_inter}, unit = NONE,
    assoc_th = @{thm bin_inter_assoc}, comm_th = @{thm bin_inter_comm},
    unitl_th = Auto2_HOTG_UtilBase.true_th, unitr_th = Auto2_HOTG_UtilBase.true_th},

  {cfhead = @{cterm bin_union}, unit = SOME @{cterm emptyset},
   assoc_th = @{thm bin_union_assoc}, comm_th = @{thm bin_union_comm},
   unitl_th = @{thm empty_bin_union_eq}, unitr_th = @{thm bin_union_empty_eq}}]
\<close>

subsubsection \<open>Collection and bounded quantification\<close>

setup \<open>add_rewrite_rule @{thm Comprehension.mem_collect_iff}\<close>
lemma ball_singleton [rewrite]: "(\<forall>x \<in> {x}. P x) = P x" by auto

subsubsection \<open>Membership\<close>

setup \<open>add_rewrite_rule @{thm Finite_Sets.singleton_mem_iff_eq}\<close>
setup \<open>add_resolve_prfstep @{thm Basic.not_mem_emptyset}\<close>
lemma ne_if_not_mem_if_mem [forward]: "x \<in> s \<Longrightarrow> y \<notin> s \<Longrightarrow> x \<noteq> y" by auto
setup \<open>add_backward_prfstep @{thm Empty_Set.ex_mem_if_not_empty}\<close>
setup \<open>add_resolve_prfstep @{thm Axioms.mem_univ}\<close>

subsubsection \<open>Insert\<close>

setup \<open>add_backward_prfstep_cond (equiv_backward_th @{thm Unordered_Pairs.mem_insert_iff})
  [with_cond "?A \<noteq> {}"]\<close>
setup \<open>add_forward_prfstep_cond (equiv_forward_th @{thm Unordered_Pairs.mem_insert_iff})
  [with_score 500, with_cond "?A \<noteq> {}"]\<close>

setup \<open>add_forward_prfstep_cond (equiv_forward_th @{thm Unordered_Pairs.insert_subset_iff_mem_subset})
  [with_cond "?A \<noteq> {}"]\<close>
setup \<open>add_backward_prfstep_cond (equiv_backward_th @{thm Unordered_Pairs.insert_subset_iff_mem_subset})
  [with_score 500, with_cond "?A \<noteq> {}"]\<close>

subsubsection \<open>Extensionality\<close>

lemma set_eq_if_mem_iff [forward]: "\<forall>a. a \<in> S \<longleftrightarrow> a \<in> T \<Longrightarrow> S = T" using eqI' by simp
setup \<open>add_backward_prfstep_cond @{thm set_eq_if_mem_iff}
  [with_score 500, with_filt (order_filter "S" "T")]\<close>

(*lemma set_pair_ext [forward]: "\<forall>a b. \<langle>a, b\<rangle> \<in> S \<longleftrightarrow> \<langle>a, b\<rangle> \<in> T \<Longrightarrow> S = T" by auto*)

subsubsection \<open>Union\<close>

setup \<open>add_forward_prfstep_cond (equiv_forward_th @{thm Union_Intersection.mem_bin_union_iff})
  [with_score 500]\<close>
setup \<open>add_backward_prfstep (equiv_backward_th @{thm Union_Intersection.mem_bin_union_iff})\<close>

lemma bin_unionD1 [forward]: "c \<in> A \<union> B \<Longrightarrow> c \<notin> A \<Longrightarrow> c \<in> B" by auto
lemma bin_unionD2 [forward]: "c \<in> A \<union> B \<Longrightarrow> c \<notin> B \<Longrightarrow> c \<in> A" by auto
lemma bin_union_singleD1 [forward]: "c \<in> {a} \<union> B \<Longrightarrow> c \<noteq> a \<Longrightarrow> c \<in> B" by auto
lemma bin_union_singleD2 [forward]: "c \<in> A \<union> {b} \<Longrightarrow> c \<noteq> b \<Longrightarrow> c \<in> A" by auto
setup \<open>add_forward_prfstep_cond @{thm mem_bin_union_if_mem_left} [with_term "?A \<union> ?B"]\<close>
setup \<open>add_forward_prfstep_cond @{thm mem_bin_union_if_mem_right} [with_term "?A \<union> ?B"]\<close>
setup \<open>add_forward_prfstep_cond @{thm mem_singleton_bin_union} [with_term "{?a} \<union> ?B"]\<close>
setup \<open>add_forward_prfstep_cond @{thm mem_bin_union_singleton} [with_term "?A \<union> {?b}"]\<close>

setup \<open>add_rewrite_rule @{thm singleton_bin_union_absorb}\<close>
setup \<open>add_backward_prfstep @{thm singleton_bin_union_absorb}\<close>

subsubsection \<open>Intersection\<close>

setup \<open>add_forward_prfstep (equiv_forward_th @{thm mem_bin_inter_iff})\<close>
setup \<open>add_backward_prfstep_cond (equiv_backward_th @{thm mem_bin_inter_iff})
  [with_score 500]\<close>

setup \<open>add_rewrite_rule @{thm Union_Intersection.empty_bin_inter_eq_empty}\<close>
setup \<open>add_rewrite_rule @{thm Union_Intersection.bin_inter_empty_eq_empty}\<close>
setup \<open>add_rewrite_rule @{thm Union_Intersection.bin_inter_absorb}\<close>
lemma not_mem_if_mem_if_bin_inter_eq_empty [forward, backward2]:
  "A \<inter> B = {} \<Longrightarrow> p \<in> A \<Longrightarrow> p \<notin> B"
  by auto
lemma singleton_bin_inter_eq_empty_iff [rewrite]: "{x} \<inter> B = {} \<longleftrightarrow> x \<notin> B" by auto

subsubsection \<open>Subset\<close>

setup \<open>add_forward_prfstep @{thm subsetI}\<close>
setup \<open>add_backward_prfstep_cond @{thm subsetI} [with_score 500]\<close>

setup \<open>add_resolve_prfstep @{thm empty_subset}\<close>
setup \<open>add_forward_prfstep @{thm mem_if_mem_if_subset}\<close>
setup \<open>add_rewrite_rule @{thm singleton_subset_iff_mem}\<close>
setup \<open>add_resolve_prfstep @{thm subset_refl}\<close>
setup \<open>add_resolve_prfstep @{thm subset_bin_union_left}\<close>
setup \<open>add_resolve_prfstep @{thm subset_bin_union_right}\<close>
lemma subset_subset_if_bin_union_subset [forward]: "A \<union> B \<subseteq> C \<Longrightarrow> A \<subseteq> C \<and> B \<subseteq> C" by auto
setup \<open>add_backward1_prfstep @{thm bin_union_subset_if_subset_if_subset}\<close>
setup \<open>add_backward2_prfstep @{thm bin_union_subset_if_subset_if_subset}\<close>
setup \<open>add_backward_prfstep @{thm bin_union_subset_bin_union_if_subset}\<close>
setup \<open>add_backward_prfstep @{thm bin_union_subset_bin_union_if_subset'}\<close>

subsubsection \<open>Diff\<close>

setup \<open>add_forward_prfstep (equiv_forward_th @{thm mem_diff_iff})\<close>
setup \<open>add_backward_prfstep_cond (equiv_backward_th @{thm mem_diff_iff})
  [with_score 500]\<close>
setup \<open>add_rewrite_rule @{thm mem_diff_iff}\<close>

setup \<open>add_rewrite_rule @{thm diff_empty_eq}\<close>
setup \<open>add_rewrite_rule @{thm Set_Difference.bin_union_diff_eq_diff_left}\<close>
setup \<open>add_rewrite_rule @{thm Set_Difference.bin_union_diff_eq_diff_right}\<close>
lemma singleton_bin_union_diff_eq_if_ne [rewrite]: "a \<noteq> c \<Longrightarrow> {a} \<union> (B \<setminus> {c}) = {a} \<union> B \<setminus> {c}"
  by (rule subset_antisym) auto
setup \<open>add_forward_prfstep_cond @{thm Set_Difference.diff_subset} [with_term "?A \<setminus> ?B"]\<close>
lemma singleton_bin_union_diff_singleton_eq_if_not_mem [rewrite]:
  "x \<notin> B \<Longrightarrow> ({x} \<union> B) \<setminus> {x} = B"
  by (rule subset_antisym) auto
lemma bin_union_singleton_diff_singleton_eq_if_not_mem [rewrite]:
  "x \<notin> B \<Longrightarrow> (B \<union> {x}) \<setminus> {x} = B"
  by (rule subset_antisym) auto
(* lemma subset_sub1 [backward]: "x \<in> A \<Longrightarrow> A \<setminus> {x} \<subset> A" by auto *)
lemma ne_if_mem_diff_singleton [forward]: "x \<in> S \<setminus> {y} \<Longrightarrow> x \<noteq> y" by simp
lemma member_notin_contra: "x \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in> S \<setminus> {y}" by simp
setup \<open>add_forward_prfstep_cond @{thm member_notin_contra} [with_term "?S \<setminus> {?y}"]\<close>

(*subsubsection \<open>Results on finite sets\<close>

setup \<open>add_resolve_prfstep @{thm Finite_Set.finite.emptyI}\<close>
lemma set_finite_single [resolve]: "finite {x}" by simp
setup \<open>add_rewrite_rule @{thm Finite_Set.finite_Un}\<close>
lemma Max_ge' [forward]: "finite A \<Longrightarrow> x > Max A \<Longrightarrow> \<not>(x \<in> A)" using Max_ge leD by auto
setup \<open>add_backward_prfstep @{thm finite_image_set}\<close>
setup \<open>add_forward_prfstep @{thm finite_atLeastAtMost}\<close>
setup \<open>add_forward_prfstep @{thm rev_finite_subset}\<close>
setup \<open>add_backward1_prfstep @{thm rev_finite_subset}\<close>

subsubsection \<open>Cardinality\<close>

setup \<open>add_rewrite_rule @{thm card_empty}\<close>
lemma card_emptyD [rewrite]: "finite S \<Longrightarrow> card S = 0 \<Longrightarrow> S = {}" by simp
lemma card_minus1 [rewrite]: "x \<in> S \<Longrightarrow> card (S - {x}) = card S - 1" by (simp add: card_Diff_subset)
setup \<open>add_forward_prfstep @{thm finite_Diff}\<close>
setup \<open>add_resolve_prfstep @{thm card_mono}\<close>*)

(*subsubsection \<open>Image set\<close>

setup \<open>add_rewrite_rule @{thm Set.image_Un}\<close>
setup \<open>add_rewrite_rule @{thm image_set_diff}\<close>*)

(*subsection \<open>Multiset\<close>

subsubsection \<open>Basic properties\<close>

lemma mset_member_empty [resolve]: "\<not>p \<in># {#}" by simp
lemma mem_multiset_single [rewrite]: "x \<in># {#y#} \<longleftrightarrow> x = y" by simp
setup \<open>add_backward2_prfstep @{thm subset_mset.antisym}\<close>
setup \<open>add_resolve_prfstep @{thm Multiset.empty_le}\<close>
setup \<open>add_forward_prfstep @{thm mset_subsetD}\<close>

lemma multi_contain_add_self1 [resolve]: "A \<subset># {#x#} + A" by simp
lemma multi_contain_add_self2 [resolve]: "A \<subset># A + {#x#}" by simp
setup \<open>add_forward_prfstep_cond @{thm Multiset.multi_member_this} [with_term "{#?x#} + ?XS"]\<close>
lemma multi_member_this2: "x \<in># XS + {#x#}" by simp
setup \<open>add_forward_prfstep_cond @{thm multi_member_this2} [with_term "?XS + {#?x#}"]\<close>
setup \<open>add_backward_prfstep @{thm Multiset.subset_mset.add_left_mono}\<close>
setup \<open>add_backward_prfstep @{thm Multiset.subset_mset.add_right_mono}\<close>

subsubsection \<open>Case checking and induction\<close>

lemma multi_nonempty_split' [resolve]: "M \<noteq> {#} \<Longrightarrow> \<exists>M' m. M = M' + {#m#}"
  using multi_nonempty_split by auto

lemma multi_member_split' [backward]: "x \<in># M \<Longrightarrow> \<exists>M'. M = M' + {#x#}"
  by (metis insert_DiffM2)

setup \<open>add_strong_induct_rule @{thm full_multiset_induct}\<close>

subsubsection \<open>Results on mset\<close>

setup \<open>add_rewrite_rule @{thm set_mset_empty}\<close>
setup \<open>add_rewrite_rule @{thm set_mset_single}\<close>
setup \<open>add_rewrite_rule @{thm set_mset_union}\<close>

setup \<open>add_rewrite_rule @{thm image_mset_empty}\<close>
setup \<open>add_rewrite_rule @{thm image_mset_single}\<close>
setup \<open>add_rewrite_rule @{thm image_mset_union}\<close>

setup \<open>add_rewrite_rule @{thm prod_mset_empty}\<close>
setup \<open>add_rewrite_rule @{thm prod_mset_singleton}\<close>
setup \<open>add_rewrite_rule @{thm prod_mset_Un}\<close>

subsubsection \<open>Set interval\<close>

setup \<open>add_rewrite_rule @{thm Set_Interval.ord_class.lessThan_iff}\<close>
setup \<open>add_rewrite_rule @{thm Set_Interval.ord_class.atLeastAtMost_iff}\<close>*)

end
