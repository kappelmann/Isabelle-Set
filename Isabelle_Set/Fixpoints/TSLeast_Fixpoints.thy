\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Least Fixpoints Computation\<close>
theory TSLeast_Fixpoints
  imports TSMonotone_Operators
begin

unbundle no_HOL_ascii_syntax

subsubsection \<open>Knaster-Tarski Theorem\<close>

definition lfp :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "lfp D h \<equiv> \<Inter>{X \<in> powerset D | prefixpoint X h}"

lemma lfp_cong [cong]:
  assumes D_eq: "D = D'"
  assumes h_eq: "\<And>X. X \<subseteq> D' \<Longrightarrow> h X = h' X"
  shows "lfp D h = lfp D' h'"
proof -
  have "{x \<in> powerset D | h x \<subseteq> x} = {x \<in> powerset D' | h' x \<subseteq> x}"
    by (subst D_eq, rule collect_cong) (auto simp: h_eq)
  then show ?thesis by (simp add: lfp_def prefixpoint_def)
qed

lemma lfp_type [type]: "lfp \<Ztypecolon> (D : Set) \<Rightarrow> Monop D \<Rightarrow> Subset D"
  unfolding lfp_def by unfold_types (auto simp: of_type_type_eq_self)

(*Explicitly set the context for now. This can actually be inferred.*)
context
  fixes D h
  assumes h_type: "h \<Ztypecolon> Monop D"
begin

lemma lfp_subset [iff]: "lfp D h \<subseteq> D"
  unfolding lfp_def by (insert h_type, unfold_types) (auto simp: of_type_type_eq_self)

lemma lfp_subset_if_prefixpoint: "prefixpoint A h \<Longrightarrow> A \<subseteq> D \<Longrightarrow> lfp D h \<subseteq> A"
  unfolding lfp_def by auto

lemma subset_lfp_if_all_subset:
  "(\<And>X. X \<subseteq> D \<Longrightarrow> prefixpoint X h \<Longrightarrow> A \<subseteq> X) \<Longrightarrow> A \<subseteq> lfp D h"
  using Monop_prefixpoint[OF h_type] unfolding lfp_def by auto

lemma prefixpoint_lfp [iff]: "prefixpoint (lfp D h) h"
proof (rule prefixpointI, rule subset_lfp_if_all_subset)
  fix X assume "X \<subseteq> D" "prefixpoint X h"
  then have "lfp D h \<subseteq> X" by (intro lfp_subset_if_prefixpoint) auto
  have "h (lfp D h) \<subseteq> h X" by (rule Monop_app_subset_app_if_subset) auto
  with \<open>prefixpoint X h\<close> show "h (lfp D h) \<subseteq> X" by blast
qed

lemma postfixpoint_lfp [iff]: "postfixpoint (lfp D h) h"
proof (rule postfixpointI, rule lfp_subset_if_prefixpoint)
  have "h (lfp D h) \<subseteq> lfp D h" using prefixpoint_lfp by blast
  then have "h (h (lfp D h)) \<subseteq> h (lfp D h)"
    using Monop_app_subset_app_if_subset by auto
  then show "prefixpoint (h (lfp D h)) h" by blast
qed discharge_types

lemma fixpoint_lfp [iff]: "fixpoint (lfp D h) h"
  using fixpoint_iff_prefixpoint_and_postfixpoint by blast


subsubsection \<open>Induction Rules\<close>

lemma prefixpoint_collectI:
  assumes "\<And>x. x \<in> h {x \<in> lfp D h | P x} \<Longrightarrow> P x"
  shows "prefixpoint {x \<in> lfp D h | P x} h" (is "prefixpoint ?S h")
proof
  have "h ?S \<subseteq> h (lfp D h)"
    by (intro Monop_app_subset_app_if_subset[of h] collect_subset) simp
  moreover have "... = lfp D h"
    by (simp only: fixpoint_lfp[unfolded fixpoint_def])
  ultimately show "h ?S \<subseteq> ?S" using assms by auto
qed

lemma lfp_induct:
  assumes a_mem_lfp: "a \<in> lfp D h"
  assumes h_induct: "\<And>x. x \<in> h {x \<in> lfp D h | P x} \<Longrightarrow> P x"
  shows "P a"
proof -
  have "P \<Ztypecolon> Element D \<Rightarrow> Bool" by unfold_types
  have "lfp D h \<subseteq> {x \<in> lfp D h | P x}"
    by (rule lfp_subset_if_prefixpoint)
      (auto intro!: prefixpoint_collectI[OF h_induct])
  with a_mem_lfp show "P a" by auto
qed

end


end
