section \<open>Power set lattices\<close>

text \<open>
  Power set lattices, least and greatest fixed points, and the Knaster-Tarski theorem
  for \<open>\<subseteq>\<close>.
\<close>

theory Set_Lattice
imports Set_Theory

begin

subsection \<open>Monotone operators\<close>

definition monotone :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
  where "monotone D h \<equiv> (\<forall>W X. W \<subseteq> X \<longrightarrow> X \<subseteq> D \<longrightarrow> h W \<subseteq> h X)"

lemma monotone_type [type]: "monotone : (D : set) \<Rightarrow> (subset D \<Rightarrow> subset D) \<Rightarrow> bool"
  by auto

abbreviation "monop D \<equiv> monotone D \<sqdot> (subset D \<Rightarrow> subset D)"

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

(* Josh: Elimination instead of destruction? *)
lemma monopD2: "\<lbrakk> h : monop D;  X : subset D;  W \<subseteq> X \<rbrakk> \<Longrightarrow> h W \<subseteq> h X"
  unfolding monotone_def by squash_types

lemma monop_app_type [derive]: "h : monop D \<Longrightarrow> X : subset D \<Longrightarrow> h X : subset D"
  by squash_types

lemma monop_union_subset:
  assumes [type]: "h : monop D" "A : subset D" "B : subset D"
  shows "h A \<union> h B \<subseteq> h (A \<union> B)"
proof -
  have "h A \<subseteq> h (A \<union> B)"
    by (rule monopD2[of h], discharge_types) auto
  moreover have "h B \<subseteq> h (A \<union> B)" by (rule monopD2[of h], discharge_types) auto
  ultimately show ?thesis by auto
qed

lemma id_monop [derive]: "(\<lambda>L. L) : monop D"
  by squash_types (auto simp: monotone_def)

lemma constant_monop [derive]: "x : subset D \<Longrightarrow> (\<lambda>L. x) : monop D"
  by squash_types (auto simp: monotone_def)

lemma monopI:
  assumes 1: "\<And>x. x : subset D \<Longrightarrow> h x : subset D"
  assumes 2: "\<And>W X. W : subset D \<Longrightarrow> X : subset D \<Longrightarrow> W \<subseteq> X \<Longrightarrow> h W \<subseteq> h X"
  shows "h : monop D"
  apply (rule adjI, rule monotoneI)
   apply (fact 2[unfolded subset_type_iff])
  apply (rule Pi_typeI, fact 1)
  done

lemma monop_unionI [derive]:
  assumes [type]: "A : monop D" "B : monop D"
  shows "(\<lambda>x. A x \<union> B x) : monop D"
proof (rule monopI, discharge_types)
  fix W X assume [type]: "W : subset D" "X : subset D"
  assume "W \<subseteq> X"

  have "A W \<subseteq> A X"
    by (rule monopD2[of A], discharge_types) (fact `W \<subseteq> X`)
  moreover have "B W \<subseteq> B X"
    by (rule monopD2[of B], discharge_types) (fact `W \<subseteq> X`)
  ultimately
  show "A W \<union> B W \<subseteq> A X \<union> B X"
    by auto
qed

lemma monop_replacementI:
  assumes "A : monop D"
  assumes "\<And>x y. x : subset D \<Longrightarrow> y : element (A x) \<Longrightarrow> f y : element D"
  shows "(\<lambda>x. Repl (A x) f) : monop D"
  using assms
  apply -        
  apply (rule monopI)
   apply squash_types[1]
  apply (auto dest: monopD2)
  done


subsection \<open>The Knaster-Tarski theorem\<close>

definition lfp :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
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
        @{method discharge_types} works here, but it prevents chaining-in other facts.
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
lemma def_lfp_unfold: "A = lfp D h \<Longrightarrow> A = h A"
  by simp (rule lfp_unfold)


subsection \<open>General induction rule for least fixed points\<close>

lemma collect_is_prefixed_point:
  assumes "\<And>x. x \<in> h (collect (lfp D h) P) \<Longrightarrow> P x"
  shows "h (collect (lfp D h) P) \<subseteq> collect (lfp D h) P"
proof -
  have "h (collect (lfp D h) P) \<subseteq> h (lfp D h)"
    by (intro monopD2[of h] collect_subset) discharge_types
  moreover have "... = lfp D h" by (simp only: lfp_unfold[symmetric])
  ultimately show ?thesis using assms by auto
qed

lemma lfp_induct:
  assumes hyp: "a \<in> lfp D h"
  assumes IH: "\<And>x. x \<in> h (collect (lfp D h) P) \<Longrightarrow> P x"
  shows "P a"
proof -
  have [type]: "P : element D \<Rightarrow> bool" by squash_types auto

  have "lfp D h \<subseteq> collect (lfp D h) P"
  proof (rule lfp_lowerbound)
    from IH
    show "h (collect (lfp D h) P) \<subseteq> collect (lfp D h) P"
      by (rule collect_is_prefixed_point)
  qed discharge_types
  with hyp show "P a" by auto
qed

(* Definition form, to control unfolding *)
lemma def_lfp_induct:
  "\<lbrakk> A = lfp D h;  a \<in> A;  \<And>x. x \<in> h (collect A P) \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> P a"
  by (rule lfp_induct, blast+)

lemma lfp_cong:
  assumes D: "D = D'"
  assumes h: "\<And>X. X \<subseteq> D' \<Longrightarrow> h X = h' X"
  shows "lfp D h = lfp D' h'"
proof -
  have "{x \<in> Pow D | h x \<subseteq> x} = {x \<in> Pow D' | h' x \<subseteq> x}"
    unfolding D
    by (rule collect_cong) (auto simp: h)
  then show ?thesis by (simp add: lfp_def)
qed

end


end