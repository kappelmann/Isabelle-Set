section \<open>Least and greatest fixed points; the Knaster-Tarski theorem\<close>

theory Fixed_Points
imports Set_Theory

begin

text \<open>
  Most of this material was ported from Isabelle/ZF.

  We try to make the definitions "more typed" by having a type of monotone operators over
  a set.

  Work in progress and field of experiments.
\<close>

subsection \<open>Monotone operators\<close>

definition monotone :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
  where "monotone D h \<equiv> (\<forall>W X. W \<subseteq> X \<longrightarrow> X \<subseteq> D \<longrightarrow> h W \<subseteq> h X)"


lemma monotone_type [type]: "monotone : (D : set) \<Rightarrow> (subset D \<Rightarrow> subset D) \<Rightarrow> bool"
  by auto

abbreviation "monop D \<equiv> monotone D \<cdot> (subset D \<Rightarrow> subset D)"

lemma monotoneI:
  assumes "\<And>W X. \<lbrakk>W \<subseteq> D; X \<subseteq> D; W \<subseteq> X\<rbrakk> \<Longrightarrow> h W \<subseteq> h X"
  shows "monotone D h"
  unfolding monotone_def
proof (intro allI impI)
  fix W X assume *: "W \<subseteq> X" "X \<subseteq> D"
  then have "W \<subseteq> D" by auto
  with * assms show "h W \<subseteq> h X" by auto
qed


lemma monopD1: "h : monop D \<Longrightarrow> h D \<subseteq> D"
  unfolding monotone_def by squash_types auto

lemma monopD2: "\<lbrakk> h : monop D;  X : subset D;  W \<subseteq> X \<rbrakk> \<Longrightarrow> h W \<subseteq> h X"
  unfolding monotone_def by squash_types

lemma monop_h_type [derive]: "h : monop D \<Longrightarrow> X : subset D \<Longrightarrow> h X : subset D"
  by squash_types

lemma monop_Un:
  assumes [type]: "h : monop D" "A : subset D" "B : subset D"
  shows "h A \<union> h B \<subseteq> h (A \<union> B)"
proof -
  have "h A \<subseteq> h (A \<union> B)" by (rule monopD2[of h], discharge_types) auto
  moreover have "h B \<subseteq> h (A \<union> B)" by (rule monopD2[of h], discharge_types) auto
  ultimately show ?thesis by auto
qed


subsection \<open>Proof of Knaster-Tarski theorem using least fixed points.\<close>

definition  lfp :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "lfp D h \<equiv> \<Inter>{X \<in> Pow D. h X \<subseteq> X}"

lemma lfp_type [type]:
  "lfp : (D : set) \<Rightarrow> monop D \<Rightarrow> subset D"
  unfolding lfp_def by squash_types auto

lemma lfp_subset:
  "h : monop D \<Longrightarrow> lfp D h \<subseteq> D"
  unfolding lfp_def by squash_types auto

(* Explicitly set the context for now. This can actually be inferred *)
context
  fixes D h
  assumes
    D_type [type]: "D : set" and
    h_type [type]: "h : monop D"
begin

lemma lfp_lowerbound: "A : subset D \<Longrightarrow> h A \<subseteq> A \<Longrightarrow> lfp D h \<subseteq> A"
  unfolding lfp_def by squash_types auto

lemma lfp_greatest: "(\<And>X. X : subset D \<Longrightarrow> h X \<subseteq> X \<Longrightarrow> A \<subseteq> X) \<Longrightarrow> A \<subseteq> lfp D h"
  using monopD1[OF h_type] unfolding lfp_def by squash_types auto

lemma lfp_unfold: "lfp D h = h (lfp D h)"
proof (rule extensionality)
  show 1: "h (lfp D h) \<subseteq> lfp D h"
  proof (rule lfp_greatest)
    fix A assume A_type [type]: "A : subset D" and "h A \<subseteq> A"
    then have *: "lfp D h \<subseteq> A" by (rule lfp_lowerbound)
    have "h (lfp D h) \<subseteq> h A"
      text \<open>
        @{method discharge_types} works here, but it prevents chaining in other facts.
        Ideally, @{method rule} would provide a hook that lets us discharge typing
        assumptions after the rule application.
      \<close>
      by (rule monopD2[of h], discharge_types) (fact *)
    with `h A \<subseteq> A` show "h (lfp D h) \<subseteq> A" by blast
  qed

  show "lfp D h \<subseteq> h (lfp D h)"
    by (intro lfp_lowerbound monopD2[of h] 1) discharge_types
qed


(* Definition form, to control unfolding *)
lemma def_lfp_unfold: "A \<equiv> lfp D h \<Longrightarrow> A = h A"
  by (simp, rule lfp_unfold)


subsection \<open>General induction rule for least fixed points\<close>

lemma Collect_is_pre_fixedpt:
  assumes "\<And>x. x \<in> h (Collect (lfp D h) P) \<Longrightarrow> P x"
  shows "h (Collect (lfp D h) P) \<subseteq> Collect (lfp D h) P"
proof -
  have "h (Collect (lfp D h) P) \<subseteq> h (lfp D h)"
    by (intro monopD2[of h] Collect_subset) discharge_types
  moreover have "... = lfp D h" by (simp only: lfp_unfold[symmetric])
  ultimately show ?thesis using assms by auto
qed

lemma induct:
  assumes hyp: "a \<in> lfp D h"
  assumes IH: "\<And>x. x \<in> h (Collect (lfp D h) P) \<Longrightarrow> P x"
  shows "P a"
proof -
  have "lfp D h \<subseteq> Collect (lfp D h) P"
  proof (rule lfp_lowerbound)
    from IH
    show "h (Collect (lfp D h) P) \<subseteq> Collect (lfp D h) P"
      by (rule Collect_is_pre_fixedpt)

    have P_type[type]: "P : element D \<Rightarrow> bool"
      by squash_types auto

    txt \<open>
      @{method discharge_types} should prove the following statement automatically, as it is just
      a consequence of @{thm Collect_type lfp_type D_type h_type P_type}.

      The use of @{method squash_types} below should be unnecessary. Every symbol has a type, so
      this should be solvable purely on the type level.
    \<close>
    show "Collect (lfp D h) P : subset D"
      (* apply discharge_types *)
      by (squash_types, rule subset_trans, rule Collect_subset, rule lfp_subset)
        discharge_types
  qed
  with hyp show "P a" by auto
qed

(* Definition form, to control unfolding *)
lemma def_induct:
  "\<lbrakk> A = lfp D h;  a \<in> A;  \<And>x. x \<in> h (Collect A P) \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> P a"
  by (rule induct, blast+)

lemma lfp_cong:
  assumes D: "D = D'"
  assumes h: "\<And>X. X \<subseteq> D' \<Longrightarrow> h X = h' X"
  shows "lfp D h = lfp D' h'"
proof -
  have "{x \<in> Pow D | h x \<subseteq> x} = {x \<in> Pow D' | h' x \<subseteq> x}"
    unfolding D
    by (rule Collect_cong) (auto simp: h)
  then show ?thesis by (simp add: lfp_def)
qed

end


end
