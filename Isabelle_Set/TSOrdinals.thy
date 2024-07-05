\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Ordinals\<close>
theory TSOrdinals
  imports
    HOTG.HOTG_Ordinals_Omega
    TSBasics
begin

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
  using assms by (auto elim: lt_eq_lt_if_ordinalE)

lemma zero_Ord [type]: "0 \<Ztypecolon> Ord"
  by (urule ordinal_zero)

end

lemma succ_type [type]: "succ \<Ztypecolon> Ord \<Rightarrow> Ord"
  by unfold_types auto

lemma omega_Ord [type]: "\<omega> \<Ztypecolon> Ord"
  using ordinal_omega by auto

lemma Ord_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> n \<Ztypecolon> Ord"
  using ordinal_if_mem_omega by unfold_types

end
