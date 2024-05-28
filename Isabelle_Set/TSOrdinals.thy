\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Ordinals\<close>
theory TSOrdinals
  imports
    TSLeast_Fixpoints
    HOTG.HOTG_Ordinals
    HOTG.HOTG_Less_Than
    HOTG.HOTG_Universes
begin

(*TODO: this file should be superseeded by HOTG_Ordinals but some lemmas are still only proven here*)

unbundle no_HOL_ascii_syntax no_HOL_groups_syntax no_HOL_order_syntax

text \<open>The class of ordinal numbers is defined abstractly, as the \<in>-transitive sets
whose members are also \<in>-transitive.\<close>

definition [typedef]: "Ord \<equiv> type ordinal"

lemma of_type_Ord_eq_ordingal [type_to_HOL_simp]: "of_type Ord = ordinal"
  unfolding Ord_def type_to_HOL_simp by simp

soft_type_translation
  "ordinal x" \<rightleftharpoons> "x \<Ztypecolon> Ord"
  unfolding Ord_def type_to_HOL_simp by simp

context
  notes type_to_HOL_simp[simp, symmetric, simp del] [[urule chained = fact]]
begin

lemma OrdI:
  assumes "mem_trans_closed X"
  and "\<And>x. x \<in> X \<Longrightarrow> mem_trans_closed x"
  shows "X \<Ztypecolon> Ord"
  using assms by (urule ordinal_if_mem_trans_closedI)

lemma Ord_mem_trans_closedE:
  assumes "X \<Ztypecolon> Ord"
  obtains "mem_trans_closed X" "\<And>x. x \<in> X \<Longrightarrow> mem_trans_closed x"
  using assms by (urule (e) ordinal_mem_trans_closedE)

text \<open>Basic properties of ordinals:\<close>

lemma Ord_if_mem_Ord [elim]: "x \<Ztypecolon> Ord \<Longrightarrow> y \<in> x \<Longrightarrow> y \<Ztypecolon> Ord"
  by (urule ordinal_if_mem_if_ordinal) simp

lemma subset_if_mem_Ord [elim]: "x \<Ztypecolon> Ord \<Longrightarrow> y \<in> x \<Longrightarrow> y \<subseteq> x"
  by (urule subset_if_mem_if_ordinal) simp

lemma Subset_if_Element_Ord [derive]:
  "x \<Ztypecolon> Ord \<Longrightarrow> y \<Ztypecolon> Element x \<Longrightarrow> y \<Ztypecolon> Subset x"
  by (urule subset_if_mem_if_ordinal) simp_all

(*Adapted from a proof by Chad Brown*)
lemma Ord_eq_if_not_mem_if_not_mem:
  "X \<Ztypecolon> Ord \<Longrightarrow> Y \<Ztypecolon> Ord \<Longrightarrow> X \<notin> Y \<Longrightarrow> Y \<notin> X \<Longrightarrow> X = Y"
proof (induction X Y rule: mem_double_induct)
  fix X Y
  assume
    ord: "X \<Ztypecolon> Ord" "Y \<Ztypecolon> Ord" and
    IH1: "\<And>x. x \<in> X \<Longrightarrow> x \<Ztypecolon> Ord \<Longrightarrow> Y \<Ztypecolon> Ord \<Longrightarrow> x \<notin> Y \<Longrightarrow> Y \<notin> x \<Longrightarrow> x = Y" and
    IH2: "\<And>y. y \<in> Y \<Longrightarrow> X \<Ztypecolon> Ord \<Longrightarrow> y \<Ztypecolon> Ord \<Longrightarrow> X \<notin> y \<Longrightarrow> y \<notin> X \<Longrightarrow> X = y" and
    not_mem: "X \<notin> Y" "Y \<notin> X"
  show "X = Y"
  proof (rule eqI)
    fix x assume "x \<in> X"
    with \<open>X \<Ztypecolon> Ord\<close> have "x \<subseteq> X" "x \<Ztypecolon> Ord" by fastforce+
    with not_mem ord IH1 \<open>x \<in> X\<close> show "x \<in> Y" by blast
  next
    fix y assume "y \<in> Y"
    with \<open>Y \<Ztypecolon> Ord\<close>  have "y \<subseteq> Y" "y \<Ztypecolon> Ord" by fastforce+
    with not_mem ord IH2 \<open>y \<in> Y\<close> show "y \<in> X" by blast
  qed
qed

lemma Ord_trichotomy:
  assumes "X \<Ztypecolon> Ord" "Y \<Ztypecolon> Ord"
  obtains (lt) "X < Y" | (eq) "X = Y" | (gt) "Y < X"
proof -
  from assms have "mem_trans_closure X = X" "mem_trans_closure Y = Y"
    by (auto simp: meaning_of_type typedef elim: ordinal_mem_trans_closedE)
  then show ?thesis using Ord_eq_if_not_mem_if_not_mem sorry
qed

lemma zero_Ord [type]: "0 \<Ztypecolon> Ord"
  by (urule ordinal_zero)

end

lemma succ_type [type]: "succ \<Ztypecolon> Ord \<Rightarrow> Ord"
  by unfold_types auto

lemma univ_closed_succ [intro!]: "x \<in> univ X \<Longrightarrow> succ x \<in> univ X"
  unfolding succ_def by auto

subsection \<open>The Smallest Infinite Ordinal \<omega>\<close>

definition "omega_op X = insert 0 {succ x | x \<in> X}"

lemma omega_op_Monop [type]: "omega_op \<Ztypecolon> Monop (univ {})"
  unfolding omega_op_def by (rule MonopI) auto

definition "omega \<equiv> lfp (univ {}) omega_op"

bundle isa_set_omega_syntax begin notation omega ("\<omega>") end
bundle no_isa_set_omega_syntax begin no_notation omega ("\<omega>") end
unbundle isa_set_omega_syntax

lemma fixpoint_omega [iff]: "fixpoint \<omega> omega_op"
  unfolding omega_def by auto

lemma zero_mem_omega [iff]: "0 \<in> \<omega>"
  by (subst fixpoint_omega[unfolded fixpoint_def omega_op_def, symmetric])
  auto

lemma succ_mem_omega_if_mem [intro!]: "n \<in> \<omega> \<Longrightarrow> succ n \<in> \<omega>"
  by (subst fixpoint_omega[unfolded fixpoint_def omega_op_def, symmetric])
    auto

lemma omega_induct [case_names empty succ, induct set: omega]:
  assumes "n \<in> \<omega>"
  and "P {}"
  and "\<And>n. \<lbrakk>n \<in> \<omega>; P n\<rbrakk> \<Longrightarrow> P (succ n)"
  shows "P n"
  using \<open>n \<in> \<omega>\<close>[unfolded omega_def]
  by (rule lfp_induct[OF omega_op_Monop])
    (auto intro: assms(2-3) simp: omega_op_def omega_def elim!: mem_insertE)

lemma mem_omegaE:
  assumes "n \<in> \<omega>"
  obtains (empty) "n = {}" | (succ) m where "m \<in> \<omega>" "n = succ m"
  using assms omega_induct[where ?P="\<lambda>m. n = m \<longrightarrow> _"] by blast

lemma mem_trans_closed_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> mem_trans_closed n"
  by (induction n rule: omega_induct) (auto simp: mem_trans_closed_def succ_eq_insert_self)

lemma eq_empty_or_empty_mem_if_mem_omegaE:
  assumes "n \<in> \<omega>"
  obtains (eq_empty) "n = {}" | (empty_mem) "{} \<in> n"
  using assms by (auto intro: empty_mem_if_mem_trans_closedI dest: mem_trans_closed_if_mem_omega)

lemma empty_mem_succ_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> {} \<in> succ n"
  by (rule eq_empty_or_empty_mem_if_mem_omegaE) auto

lemma mem_trans_closed_omega [iff]: "mem_trans_closed \<omega>"
  apply (rule mem_trans_closedI)
  subgoal for n by (induction n rule: omega_induct) (auto simp: succ_eq_insert_self)
  done

lemma omega_Ord [type]: "\<omega> \<Ztypecolon> Ord"
  by (rule OrdI) (auto elim: mem_trans_closed_if_mem_omega)

lemma Ord_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> n \<Ztypecolon> Ord"
  by (fact Ord_if_mem_Ord[OF omega_Ord])

lemma mem_trans_if_mem_omega: "\<lbrakk>n \<in> \<omega>; k \<in> m; m \<in> n\<rbrakk> \<Longrightarrow> k \<in> n"
  using mem_trans_closed_if_mem_omega[unfolded mem_trans_closed_def] by auto

lemma mem_if_succ_mem_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> succ m \<in> n \<Longrightarrow> m \<in> n"
  using mem_trans_if_mem_omega[of n m "succ m"] succ_eq_insert_self by auto

lemma subset_omega_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> n \<subseteq> \<omega>"
  using mem_trans_closed_omega[unfolded mem_trans_closed_def] by blast

lemma mem_omega_if_mem_if_mem_omega: "x \<in> \<omega> \<Longrightarrow> y \<in> x \<Longrightarrow> y \<in> \<omega>"
  using subset_omega_if_mem_omega by auto

lemma succ_mem_succ_if_mem_if_mem_omega:
  "\<lbrakk>n \<in> \<omega>; m \<in> n\<rbrakk> \<Longrightarrow> succ m \<in> succ n"
  by (induction n rule: omega_induct) (use succ_eq_insert_self in auto)

lemma mem_if_succ_mem_succ_if_mem_omega:
  assumes "n \<in> \<omega>" and succ_m_mem: "succ m \<in> succ n"
  shows "m \<in> n"
proof -
  have "mem_trans_closed (succ n)" by (rule mem_trans_closed_if_mem_omega) auto
  from mem_trans_closedD[OF this] have "succ m \<subseteq> succ n" by auto
  then have "m \<in> (n \<union> {n})" using succ_eq_insert_self by auto
  with succ_m_mem show "m \<in> n" by auto
qed

lemma succ_mem_succ_iff_mem_if_mem_omega [iff]:
  "n \<in> \<omega> \<Longrightarrow> succ m \<in> succ n \<longleftrightarrow> m \<in> n"
  using succ_mem_succ_if_mem_if_mem_omega mem_if_succ_mem_succ_if_mem_omega
  by blast


end
