section\<open>Ordinals\<close>
theory Ordinals
  imports Least_Fixpoint
begin

text \<open>The class of ordinal numbers is defined abstractly, as the \<in>-transitive sets
whose members are also \<in>-transitive.\<close>

definition [typedef]: "Ord \<equiv> type (\<lambda>x. mem_trans x \<and> (\<forall>y \<in> x. mem_trans y))"

lemma OrdI: "mem_trans X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> mem_trans x) \<Longrightarrow> X : Ord"
  by unfold_types auto

text \<open>Basic properties of ordinals:\<close>

lemma Ord_if_mem_Ord [elim]: "x : Ord \<Longrightarrow> y \<in> x \<Longrightarrow> y : Ord"
  by unfold_types (unfold mem_trans_def, auto 5 0)

lemma mem_trans_if_Ord: "x : Ord \<Longrightarrow> mem_trans x"
  by unfold_types

lemma subset_if_mem_Ord [elim]: "x : Ord \<Longrightarrow> y \<in> x \<Longrightarrow> y \<subseteq> x"
  by unfold_types (fastforce simp: mem_trans_def)

lemma Subset_if_Element_Ord [derive]:
  "x : Ord \<Longrightarrow> y : Element x \<Longrightarrow> y : Subset x"
  (*TODO: should be discharged by the type checker*)
  by (intro SubsetI, drule ElementD) (fact subset_if_mem_Ord)

(*Adapted from a proof by Chad Brown*)
lemma Ord_eq_if_not_mem_if_not_mem:
  "X : Ord \<Longrightarrow> Y : Ord \<Longrightarrow> X \<notin> Y \<Longrightarrow> Y \<notin> X \<Longrightarrow> X = Y"
proof (induction X Y rule: mem_double_induct)
  fix X Y
  assume
    ord: "X : Ord" "Y: Ord" and
    IH1: "\<And>x. x \<in> X \<Longrightarrow> x : Ord \<Longrightarrow> Y : Ord \<Longrightarrow> x \<notin> Y \<Longrightarrow> Y \<notin> x \<Longrightarrow> x = Y" and
    IH2: "\<And>y. y \<in> Y \<Longrightarrow> X : Ord \<Longrightarrow> y : Ord \<Longrightarrow> X \<notin> y \<Longrightarrow> y \<notin> X \<Longrightarrow> X = y" and
    not_mem: "X \<notin> Y" "Y \<notin> X"
  show "X = Y"
  proof (rule eqI)
    fix x assume "x \<in> X"
    with \<open>X : Ord\<close> have "x \<subseteq> X" "x : Ord" by auto
    with not_mem ord IH1 \<open>x \<in> X\<close> show "x \<in> Y" by blast
  next
    fix y assume "y \<in> Y"
    with \<open>Y : Ord\<close>  have "y \<subseteq> Y" "y: Ord" by auto
    with not_mem ord IH2 \<open>y \<in> Y\<close> show "y \<in> X" by blast
  qed
qed

lemma Ord_trichotomy:
  assumes "X : Ord" "Y : Ord"
  obtains (lt) "X \<in> Y" | (eq) "X = Y" | (gt) "Y \<in> X"
  using assms Ord_eq_if_not_mem_if_not_mem by auto

lemma emptyset_Ord [type]: "{} : Ord"
  by unfold_types auto


subsection \<open>Successor ordinals\<close>

definition succ where "succ x \<equiv> x \<union> {x}"

lemma succ_type [type]: "succ : Ord \<Rightarrow> Ord"
  unfolding succ_def by unfold_types (unfold mem_trans_def, auto 5 0)

lemma mem_succE [elim]:
  assumes "x \<in> succ y"
  obtains "x \<in> y" | "x = y"
  using assms unfolding succ_def by auto

text \<open>Simp rules\<close>

lemma succ_empty_eq [simp, intro!]: "succ {} = {{}}"
  unfolding succ_def by simp

lemma succ_succ_empty_eq [simp, intro!]: "succ (succ {}) = {{}, {{}}}"
  unfolding succ_def by auto

lemma succ_ne_self [simp, intro!]: "succ x \<noteq> x"
  unfolding succ_def by auto

lemma succ_ne_empty [simp, intro!]: "succ x \<noteq> {}"
  unfolding succ_def by auto

lemma mem_succ_self [simp, intro!]: "x \<in> succ x"
  unfolding succ_def by auto

text \<open>Injectivity\<close>

lemma succ_inj [dest]: "succ x = succ y \<Longrightarrow> x = y"
proof (rule ccontr)
  assume succ_eq: "succ x = succ y" and neq: "x \<noteq> y"
  have "x \<in> succ x" and "y \<in> succ y" by auto
  then have "x \<in> succ y" and "y \<in> succ x" by (auto simp only: succ_eq)
  with neq have "x \<in> y" and "y \<in> x" by auto
  then show False using mem_asym by blast
qed

lemma succ_ne_if_ne [intro!]: "x \<noteq> y \<Longrightarrow> succ x \<noteq> succ y"
  by auto

lemma mem_succ_if_mem [intro]: "x \<in> y \<Longrightarrow> x \<in> succ y"
  unfolding succ_def by auto

lemma univ_closed_succ [intro!]: "x \<in> univ X \<Longrightarrow> succ x \<in> univ X"
  unfolding succ_def by auto


subsection \<open>The Smallest Infinite Ordinal \<omega>\<close>

definition "omega_op X = {{}} \<union> {succ x | x \<in> X}"

lemma omega_op_Monop [type]: "omega_op : Monop V"
  unfolding omega_op_def by (rule MonopI) auto

definition "omega \<equiv> lfp V omega_op"

bundle isa_set_omega_syntax begin notation omega ("\<omega>") end
bundle no_isa_set_omega_syntax begin no_notation omega ("\<omega>") end
unbundle isa_set_omega_syntax

lemma fixpoint_omega [simp, intro!]: "fixpoint \<omega> omega_op"
  unfolding omega_def by auto

lemma empty_mem_omega [simp, intro!]: "{} \<in> \<omega>"
  by (subst fixpoint_omega[unfolded fixpoint_def omega_op_def, symmetric])
    simp

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
    (auto intro: assms(2-3) simp only: omega_op_def omega_def)

lemma mem_omegaE:
  assumes "n \<in> \<omega>"
  obtains (empty) "n = {}" | (succ) m where "m \<in> \<omega>" "n = succ m"
  using assms omega_induct[where ?P="\<lambda>m. n = m \<longrightarrow> _"] by blast

lemma eq_empty_or_empty_mem_if_mem_omegaE:
  assumes "n \<in> \<omega>"
  obtains (eq_empty) "n = {}" | (empty_mem) "{} \<in> n"
  using assms by (induction n rule: omega_induct) auto

lemma empty_mem_succ_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> {} \<in> succ n"
  by (rule eq_empty_or_empty_mem_if_mem_omegaE) auto

lemma mem_trans_omega [simp, intro!]: "mem_trans \<omega>"
  by (rule mem_transI, rule omega_induct) auto

lemma mem_trans_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> mem_trans n"
  by (induction n rule: omega_induct) (auto simp: mem_trans_def)

lemma omega_Ord [type]: "\<omega> : Ord"
  by (rule OrdI) (auto elim: mem_trans_if_mem_omega)

lemma Ord_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> n : Ord"
  by (fact Ord_if_mem_Ord[OF omega_Ord])

lemma mem_trans_if_mem_omega' [trans]: "\<lbrakk>n \<in> \<omega>; k \<in> m; m \<in> n\<rbrakk> \<Longrightarrow> k \<in> n"
  using mem_trans_if_mem_omega[unfolded mem_trans_def] by auto

lemma mem_if_succ_mem_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> succ m \<in> n \<Longrightarrow> m \<in> n"
  using mem_trans_if_mem_omega'[of n m "succ m"] by auto

lemma subset_omega_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> n \<subseteq> \<omega>"
  using mem_trans_omega[unfolded mem_trans_def] by blast

lemma mem_omega_if_mem_if_mem_omega: "x \<in> \<omega> \<Longrightarrow> y \<in> x \<Longrightarrow> y \<in> \<omega>"
  using subset_omega_if_mem_omega by auto

lemma succ_mem_succ_if_mem_if_mem_omega:
  "\<lbrakk>n \<in> \<omega>; m \<in> n\<rbrakk> \<Longrightarrow> succ m \<in> succ n"
  by (induction n rule: omega_induct) auto

lemma mem_if_succ_mem_succ_if_mem_omega:
  assumes "n \<in> \<omega>" and succ_m_mem: "succ m \<in> succ n"
  shows "m \<in> n"
proof -
  have "mem_trans (succ n)" by (rule mem_trans_if_mem_omega) auto
  from mem_transE[OF this] have "succ m \<subseteq> succ n" by auto
  then have "m \<in> (n \<union> {n})" by auto
  with succ_m_mem show "m \<in> n" by auto
qed

lemma succ_mem_succ_iff_mem_if_mem_omega [iff]:
  "n \<in> \<omega> \<Longrightarrow> succ m \<in> succ n \<longleftrightarrow> m \<in> n"
  using succ_mem_succ_if_mem_if_mem_omega mem_if_succ_mem_succ_if_mem_omega
  by blast


end
