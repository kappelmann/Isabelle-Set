section \<open>Least fixed points and the Knaster-Tarski theorem for \<open>\<subseteq>\<close>\<close>

theory Monotone
imports Sets
begin

subsection \<open>Monotone Operators\<close>

definition monotone :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
  where "monotone D h \<equiv> (\<forall>W X. W \<subseteq> X \<longrightarrow> X \<subseteq> D \<longrightarrow> h W \<subseteq> h X)"

lemma monotone_type [type]:
  "monotone: (D: Set) \<Rightarrow> (Subset D \<Rightarrow> Subset D) \<Rightarrow> Bool"
  by unfold_types

abbreviation "Monop D \<equiv> monotone D \<sqdot> (Subset D \<Rightarrow> Subset D)"

lemma monotoneI:
  assumes "\<And>W X. \<lbrakk>W \<subseteq> D; X \<subseteq> D; W \<subseteq> X\<rbrakk> \<Longrightarrow> h W \<subseteq> h X"
  shows "monotone D h"
unfolding monotone_def
proof (intro allI impI)
  fix W X assume *: "W \<subseteq> X" "X \<subseteq> D"
  then have "W \<subseteq> D" by auto
  with * assms show "h W \<subseteq> h X" by auto
qed

lemma monop_Subset_closed: "h : Monop D \<Longrightarrow> h D \<subseteq> D"
  unfolding monotone_def by unfold_types auto

(* Elimination instead of destruction? *)
lemma MonopE: "\<lbrakk>h: Monop D; X \<subseteq> D; W \<subseteq> X\<rbrakk> \<Longrightarrow> h W \<subseteq> h X"
  unfolding monotone_def by unfold_types

lemma [derive]: "h : Monop D \<Longrightarrow> X : Subset D \<Longrightarrow> h X : Subset D"
  by unfold_types

lemma [derive]: "(\<lambda>L. L): Monop D"
  by unfold_types (auto simp: monotone_def)

lemma [derive]: "x: Subset D \<Longrightarrow> (\<lambda>L. x): Monop D"
  by unfold_types (auto simp: monotone_def)

lemma Monop_union_subset:
  assumes "h: Monop D" "A \<subseteq> D" "B \<subseteq> D"
  shows "h A \<union> h B \<subseteq> h (A \<union> B)"
proof -
  have "h A \<subseteq> h (A \<union> B)"
    by (rule MonopE, discharge_types) auto
  moreover have "h B \<subseteq> h (A \<union> B)"
    by (rule MonopE, discharge_types) auto
  ultimately show ?thesis by auto
qed

lemma MonopI:
  assumes 1: "\<And>x. x \<subseteq> D \<Longrightarrow> h x \<subseteq> D"
  assumes 2: "\<And>W X. W \<subseteq> D \<Longrightarrow> X \<subseteq> D \<Longrightarrow> W \<subseteq> X \<Longrightarrow> h W \<subseteq> h X"
  shows "h: Monop D"
  apply unfold_types
  apply (auto intro!: 1 monotoneI)
  using 2 by blast

lemma Monop_unionI [derive]:
  assumes "A: Monop D" "B: Monop D"
  shows "(\<lambda>x. A x \<union> B x): Monop D"
proof (rule MonopI)
  fix W X assume "W \<subseteq> D" "X \<subseteq> D"
  show "A X \<union> B X \<subseteq> D" by auto

  assume "W \<subseteq> X"
  have "A W \<subseteq> A X" by (rule MonopE) auto
  moreover have "B W \<subseteq> B X" by (rule MonopE) auto
  ultimately show "A W \<union> B W \<subseteq> A X \<union> B X" by auto
qed

lemma Monop_replacementI:
  assumes "A: Monop D"
  assumes "\<And>x y. x: Subset D \<Longrightarrow> y: Element (A x) \<Longrightarrow> f y: Element D"
  shows "(\<lambda>x. repl (A x) f): Monop D"
  apply (insert assms)
  apply (rule MonopI)
   apply unfold_types[1]
  apply (auto dest: MonopE)
  done


subsection \<open>The Knaster-Tarski theorem\<close>

definition lfp :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "lfp D h \<equiv> \<Inter>{X \<in> powerset D. h X \<subseteq> X}"

lemma lfp_type [type]:
  "lfp: (D: Set) \<Rightarrow> Monop D \<Rightarrow> Subset D"
  unfolding lfp_def by unfold_types auto

lemma lfp_subset:
  "h: Monop D \<Longrightarrow> lfp D h \<subseteq> D"
  unfolding lfp_def by unfold_types auto

(*Explicitly set the context for now. This can actually be inferred.*)
context
  fixes D h
  assumes h_type: "h: Monop D"
begin

lemma lfp_lowerbound: "h A \<subseteq> A \<Longrightarrow> A \<subseteq> D \<Longrightarrow> lfp D h \<subseteq> A"
  unfolding lfp_def by auto

lemma lfp_greatest: "(\<And>X. X \<subseteq> D \<Longrightarrow> h X \<subseteq> X \<Longrightarrow> A \<subseteq> X) \<Longrightarrow> A \<subseteq> lfp D h"
  using monop_Subset_closed[OF h_type] unfolding lfp_def by auto

lemma lfp_unfold: "lfp D h = h (lfp D h)"
proof (rule extensionality)
  show *: "h (lfp D h) \<subseteq> lfp D h"
  proof (rule lfp_greatest)
    fix A assume "A \<subseteq> D" 
    assume "h A \<subseteq> A"
    hence "lfp D h \<subseteq> A" by (rule lfp_lowerbound) auto
    have "h (lfp D h) \<subseteq> h A"
      by (rule MonopE) auto
    with \<open>h A \<subseteq> A\<close> show "h (lfp D h) \<subseteq> A" by blast
  qed
  show "lfp D h \<subseteq> h (lfp D h)"
    by (intro lfp_lowerbound MonopE[of h] *) (auto simp only: subset_self)
qed

(*Definition form, to control unfolding*)
lemma def_lfp_unfold: "A = lfp D h \<Longrightarrow> A = h A"
  by simp (rule lfp_unfold)


subsection \<open>General induction rule for least fixed points\<close>

lemma collect_is_prefixed_point:
  assumes "\<And>x. x \<in> h (collect (lfp D h) P) \<Longrightarrow> P x"
  shows "h (collect (lfp D h) P) \<subseteq> collect (lfp D h) P"
proof -
  have "h (collect (lfp D h) P) \<subseteq> h (lfp D h)"
    by (intro MonopE[of h] collect_subset) simp
  moreover have "... = lfp D h" by (simp only: lfp_unfold[symmetric])
  ultimately show ?thesis using assms by auto
qed

lemma lfp_induct:
  assumes hyp: "a \<in> lfp D h"
  assumes IH: "\<And>x. x \<in> h (collect (lfp D h) P) \<Longrightarrow> P x"
  shows "P a"
proof -
  have "P : Element D \<Rightarrow> Bool" by unfold_types
  have "lfp D h \<subseteq> collect (lfp D h) P"
  proof (rule lfp_lowerbound)
    from IH
    show "h (collect (lfp D h) P) \<subseteq> collect (lfp D h) P"
      by (rule collect_is_prefixed_point)
  qed discharge_types
  with hyp show "P a" by auto
qed

(*Definition form, to control unfolding*)
lemma def_lfp_induct:
  "\<lbrakk>A = lfp D h;  a \<in> A;  \<And>x. x \<in> h (collect A P) \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P a"
  by (rule lfp_induct, blast+)

lemma lfp_cong:
  assumes D: "D = D'"
  assumes h: "\<And>X. X \<subseteq> D' \<Longrightarrow> h X = h' X"
  shows "lfp D h = lfp D' h'"
proof -
  have "{x \<in> powerset D | h x \<subseteq> x} = {x \<in> powerset D' | h' x \<subseteq> x}"
    unfolding D
    by (rule collect_cong) (auto simp: h)
  then show ?thesis by (simp add: lfp_def)
qed

end


end
