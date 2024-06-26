\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Ordinals\<close>
theory HOTG_Ordinals_Base
  imports
    HOTG_Binary_Relations_Connected
    HOTG_Foundation
    Transport.HOL_Syntax_Bundles_Groups
begin

paragraph \<open>Summary\<close>
text \<open>Translation of ordinals from \<^url>\<open>https://www.isa-afp.org/entries/ZFC_in_HOL.html\<close>.
We define ordinals and limit ordinals. Two ordinal inductions are proven.

We use the Von Neumann encoding of numbers. The Von Neumann numbers are defined inductively.
The Von Neumann number \<open>0\<close> is defined to be the empty set,
and there are no smaller Von Neumann numbers. The Von Neumann number \<open>n\<close> is then the set of
all Von Neumann numbers less than \<open>n\<close>. Further details can be found in
\<^url>\<open>https://planetmath.org/vonneumanninteger\<close>.\<close>

subsection \<open>Ordinals\<close>

text \<open>We follow the definition from \<^cite>\<open>ZFC_in_HOL_AFP\<close>,
 \<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_in_HOL.thy#L601\<close>.\<close>

definition "ordinal X \<equiv> mem_trans_closed X \<and> (\<forall>x : X. mem_trans_closed x)"

lemma ordinal_mem_trans_closedE:
  assumes "ordinal X"
  obtains "mem_trans_closed X" "\<And>x. x \<in> X \<Longrightarrow> mem_trans_closed x"
  using assms unfolding ordinal_def by auto

lemma ordinal_if_mem_trans_closedI:
  assumes "mem_trans_closed X"
  and "\<And>x. x \<in> X \<Longrightarrow> mem_trans_closed x"
  shows "ordinal X"
  using assms unfolding ordinal_def by auto

definition "succ X \<equiv> insert X X"

lemma succ_eq_insert_self: "succ X = insert X X" by (simp add: succ_def)

lemma succ_ne_self [iff]: "succ x \<noteq> x"
  using succ_eq_insert_self by auto

abbreviation "set_zero \<equiv> {}"
abbreviation "set_one \<equiv> succ set_zero"
abbreviation "set_two \<equiv> succ set_one"

bundle hotg_set_zero_syntax begin notation set_zero ("0") end
bundle no_hotg_set_zero_syntax begin no_notation set_zero ("0") end

bundle hotg_set_one_syntax begin notation set_one ("1") end
bundle no_hotg_set_one_syntax begin no_notation set_one ("1") end

bundle hotg_set_two_syntax begin notation set_two ("2") end
bundle no_hotg_set_two_syntax begin no_notation set_two ("2") end

unbundle
  hotg_set_zero_syntax
  hotg_set_one_syntax
  hotg_set_two_syntax
  no_HOL_ascii_syntax
  no_HOL_groups_syntax

context
  notes ordinal_mem_trans_closedE[elim!] ordinal_if_mem_trans_closedI[intro!]
    mem_trans_closedI[intro!]
begin

lemma ordinal_succI [intro]:
  assumes "ordinal x"
  shows "ordinal (succ x)"
  using assms by (auto simp: succ_eq_insert_self)

lemma ordinal_zero [iff]: "ordinal 0" by auto
lemma ordinal_one [iff]: "ordinal 1" by (intro ordinal_succI) auto
lemma ordinal_two [iff]: "ordinal 2" by (intro ordinal_succI) auto

lemma succ_ne_zero [iff]: "succ x \<noteq> 0"
  using succ_eq_insert_self by auto

text \<open>Injectivity\<close>

lemma mem_succE:
  assumes "x \<in> succ y"
  obtains "x \<in> y" | "x = y"
  using assms succ_eq_insert_self by auto

lemma succ_inj [dest]: "succ x = succ y \<Longrightarrow> x = y"
proof (rule ccontr)
  assume succ_eq: "succ x = succ y" and neq: "x \<noteq> y"
  have "x \<in> succ x" and "y \<in> succ y" using succ_eq_insert_self by auto
  then have "x \<in> succ y" and "y \<in> succ x" by (auto simp only: succ_eq)
  with neq have "x \<in> y" and "y \<in> x" by (auto elim: mem_succE)
  then show False using not_mem_if_mem by blast
qed

lemma succ_ne_if_ne [intro!]: "x \<noteq> y \<Longrightarrow> succ x \<noteq> succ y"
  by auto

lemma ordinal_unionI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> ordinal x"
  shows "ordinal (\<Union>X)"
  using assms by blast

lemma ordinal_interI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> ordinal x"
  shows "ordinal (\<Inter>X)"
  using assms by blast

lemma ordinal_bin_unionI:
  assumes "ordinal X"
  and "ordinal Y"
  shows "ordinal (X \<union> Y)"
  by (urule ordinal_unionI[of "{X, Y}"]) (use assms in blast)

lemma ordinal_bin_interI:
  assumes "ordinal X"
  and "ordinal Y"
  shows "ordinal (X \<inter> Y)"
  by (urule ordinal_interI[of "{X, Y}"]) (use assms in blast)

lemma subset_if_mem_if_ordinal: "ordinal X \<Longrightarrow> Y \<in> X \<Longrightarrow> Y \<subseteq> X" by auto

lemma mem_trans_if_ordinal: "\<lbrakk>ordinal X; Y \<in> Z; Z \<in> X\<rbrakk>  \<Longrightarrow> Y \<in> X" by auto

lemma ordinal_if_mem_if_ordinal: "\<lbrakk>ordinal X; Y \<in> X\<rbrakk>  \<Longrightarrow> ordinal Y"
  by blast

lemma union_succ_eq_self_if_mem_trans_closed [simp]: "mem_trans_closed X \<Longrightarrow> \<Union>(succ X) = X"
  by (auto simp: succ_eq_insert_self)

lemma union_succ_eq_self_if_ordinal [simp]: "ordinal \<beta> \<Longrightarrow> \<Union>(succ \<beta>) = \<beta>"
  using union_succ_eq_self_if_mem_trans_closed by auto

text\<open>Membership ordinal induction:\<close>

lemma ordinal_mem_induct [consumes 1, case_names step]:
  assumes "ordinal X"
  and "\<And>X. \<lbrakk>ordinal X; \<And>x. x \<in> X \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P X"
  shows "P X"
  using assms ordinal_if_mem_if_ordinal
  by (induction X rule: mem_induction) auto


subsection \<open>Limit Ordinals\<close>

text \<open>We follow the definition from \<^cite>\<open>ZFC_in_HOL_AFP\<close>,
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_in_HOL.thy#L939\<close>.
A limit ordinal \<open>X\<close> is an ordinal number greater than \<open>0\<close> that is not a successor ordinal.
Further details can be found in \<^url>\<open>https://en.wikipedia.org/wiki/Limit_ordinal\<close>.\<close>

definition "limit_ordinal X \<equiv> ordinal X \<and> 0 \<in> X \<and> (\<forall>x : X. succ x \<in> X)"

lemma limit_ordinalI:
  assumes "ordinal X"
  and "0 \<in> X"
  and "\<And>x. x \<in> X \<Longrightarrow> succ x \<in> X"
  shows "limit_ordinal X"
  using assms unfolding limit_ordinal_def by auto

lemma limit_ordinalE:
  assumes "limit_ordinal X"
  obtains "ordinal X" "0 \<in> X" "\<And>x. x \<in> X \<Longrightarrow> succ x \<in> X"
  using assms unfolding limit_ordinal_def by auto

lemma union_eq_self_if_limit_ordinal:
  assumes limit: "limit_ordinal X"
  shows "\<Union>X = X"
proof
  fix x assume "x \<in> \<Union>X"
  then show "x \<in> X" using limit_ordinalE limit by blast
next
  fix x assume "x \<in> X"
  then have "succ x \<in> X" using limit_ordinalE limit by auto
  moreover have "x \<in> succ x" using succ_eq_insert_self by auto
  ultimately show "x \<in> \<Union>X" by blast
qed

lemma mem_or_eq_or_mem_if_ordinal_if_ordinal: "ordinal X \<Longrightarrow> ordinal Y \<Longrightarrow> X \<in> Y \<or> X = Y \<or> Y \<in> X"
proof (induction X arbitrary: Y rule: ordinal_mem_induct)
  case step_X: (step X)
  show ?case using \<open>ordinal Y\<close>
  proof (induction Y rule: ordinal_mem_induct)
    case step_Y: (step Y)
    consider "X = Y" | (x) x where "x \<in> X" "x \<notin> Y" | (y) y where "y \<in> Y" "y \<notin> X" by blast
    then show ?case
    proof cases
      case x
      have "Y = x \<or> Y \<in> x" using step_X.IH[OF \<open>x \<in> X\<close> \<open>ordinal Y\<close>] \<open>x \<notin> Y\<close> by auto
      then show ?thesis using mem_trans_if_ordinal \<open>ordinal X\<close> \<open>x \<in> X\<close> by auto
    next
      case y
      have "X = y \<or> X \<in> y" using step_Y.IH \<open>y \<in> Y\<close> \<open>y \<notin> X\<close> by auto
      then show ?thesis using mem_trans_if_ordinal \<open>ordinal Y\<close> \<open>y \<in> Y\<close> by auto
    qed auto
  qed
qed

lemma mem_eq_mem_if_ordinalE:
  assumes "ordinal X" "ordinal Y"
  obtains "X \<in> Y" | "X = Y" | "Y \<in> X"
  using mem_or_eq_or_mem_if_ordinal_if_ordinal assms by (auto del: ordinal_mem_trans_closedE)

lemma connected_on_ordinal_mem: "connected_on ordinal (\<in>)"
  by (auto elim: mem_eq_mem_if_ordinalE del: ordinal_mem_trans_closedE)

lemma ordinal_cases [cases type: set]:
  assumes ordinal: "ordinal k"
  obtains (zero) "k = 0" | (succ) l where "ordinal l" "succ l = k" | (limit) "limit_ordinal k"
proof (cases "limit_ordinal k")
  case not_limit: False
  then show ?thesis
  proof (cases "0 \<in> k")
    case True
    then obtain l where hl: "l \<in> k \<and> succ l \<notin> k" using not_limit ordinal
      by (fast intro!: limit_ordinalI)
    have succ_subset: "succ l \<subseteq> k" using mem_succE mem_trans_if_ordinal[OF ordinal] hl by blast
    from hl have "ordinal (succ l)" using ordinal ordinal_succI ordinal_if_mem_if_ordinal by auto
    from mem_or_eq_or_mem_if_ordinal_if_ordinal[OF this ordinal] have "succ l = k"
      using hl succ_subset by auto
    moreover have "ordinal l" using ordinal_if_mem_if_ordinal ordinal hl by blast
    ultimately show ?thesis using succ by auto
  next
    case False
    then have "k = 0" using mem_or_eq_or_mem_if_ordinal_if_ordinal[OF ordinal] by blast
    then show ?thesis using zero by blast
  qed
qed

text\<open>Standard ordinal induction:\<close>

lemma ordinal_induct [consumes 1, case_names zero succ limit, induct type: set]:
  assumes "ordinal X"
  and "P 0"
  and P_succ: "\<And>X. \<lbrakk>ordinal X; P X\<rbrakk> \<Longrightarrow> P (succ X)"
  and P_limit: "\<And>X. \<lbrakk>limit_ordinal X; \<And>x. x \<in> X \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P (\<Union>X)"
  shows "P X"
using \<open>ordinal X\<close>
proof (induction X rule: ordinal_mem_induct)
  case (step X)
  then show ?case
  proof (cases rule: ordinal_cases)
    case zero
    with \<open>P 0\<close> show ?thesis by simp
  next
    case (succ l)
    from succ step succ_eq_insert_self have "P (succ l)" by (intro P_succ) auto
    with succ show ?thesis by simp
  next
    case limit
    then have "P (\<Union>X)" using P_limit step.IH by auto
    then show ?thesis using union_eq_self_if_limit_ordinal limit by auto
  qed
qed

end

end
