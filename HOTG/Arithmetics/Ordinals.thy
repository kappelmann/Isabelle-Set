\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Ordinals\<close>
theory Ordinals
  imports
    Mem_Transitive_Closed
    SAddition
    Less_Than
begin

unbundle no_HOL_groups_syntax

paragraph \<open>Summary\<close>
text \<open>Translation of ordinals from \<^url>\<open>https://www.isa-afp.org/entries/ZFC_in_HOL.html\<close>.
We give the definition of ordinals and limit ordinals. In addition,
two ordinal inductions are proven.

And we use the Von Neumann encoding of natural numbers. The Von Neumann numbers
are defined inductively. The Von Neumann number \<open>0\<close> is defined to be the empty set, 
and there are no smaller Von Neumann numbers. The Von Neumann number \<open>N\<close> is then the set of 
all Von Neumann numbers less than \<open>N\<close>. Further details can be found in
\<^url>\<open>https://planetmath.org/vonneumanninteger\<close>.\<close>

paragraph \<open>Ordinals\<close>

text \<open>We follow the definition from \<^cite>\<open>ZFC_in_HOL_AFP\<close>,
 \<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_in_HOL.thy#L601\<close>.\<close>

definition "ordinal X \<equiv> mem_trans_closed X \<and> (\<forall>x \<in> X. mem_trans_closed x)"

lemma ordinal_mem_trans_closedE:
  assumes "ordinal X"
  obtains "mem_trans_closed X" "\<And>x. x \<in> X \<Longrightarrow> mem_trans_closed x"
  using assms unfolding ordinal_def by auto

lemma ordinal_if_mem_trans_closedI:
  assumes "mem_trans_closed X"
  and "\<And>x. x \<in> X \<Longrightarrow> mem_trans_closed x"
  shows "ordinal X"
  using assms unfolding ordinal_def by auto

context
  notes ordinal_mem_trans_closedE[elim!] ordinal_if_mem_trans_closedI[intro!]
begin

lemma ordinal_zero [iff]: "ordinal 0" by auto

lemma ordinal_one [iff]: "ordinal 1" by auto

lemma ordinal_succI [intro]:
  assumes "ordinal x"
  shows "ordinal (succ x)"
  using assms by (auto simp flip: insert_self_eq_add_one simp: succ_eq_add_one)

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
  using assms by blast

lemma ordinal_bin_interI:
  assumes "ordinal X"
  and "ordinal Y"
  shows "ordinal (X \<inter> Y)"
  using assms by blast

lemma subset_if_mem_if_ordinal: "ordinal X \<Longrightarrow> Y \<in> X \<Longrightarrow> Y \<subseteq> X" by auto

lemma mem_trans_if_ordinal: "\<lbrakk>ordinal X; Y \<in> Z; Z \<in> X\<rbrakk>  \<Longrightarrow> Y \<in> X" by auto

lemma ordinal_if_mem_if_ordinal: "\<lbrakk>ordinal X; Y \<in> X\<rbrakk>  \<Longrightarrow> ordinal Y"
  by blast

lemma union_succ_eq_self_if_ordinal [simp]: "ordinal \<beta> \<Longrightarrow> \<Union>(succ \<beta>) = \<beta>" by auto

text\<open>Membership ordinal induction:\<close>

lemma ordinal_mem_induct [consumes 1, case_names step]:
  assumes "ordinal X"
  and "\<And>X. \<lbrakk>ordinal X; \<And>x. x \<in> X \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P X"
  shows "P X"
  using assms ordinal_if_mem_if_ordinal
  by (induction X rule: mem_induction) auto


paragraph \<open>Limit Ordinals\<close>

text \<open>We follow the definition from \<^cite>\<open>ZFC_in_HOL_AFP\<close>,
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_in_HOL.thy#L939\<close>.
A limit ordinal \<open>X\<close> is an ordinal number greater than \<open>0\<close> that is not a successor ordinal.
Further details can be found in \<^url>\<open>https://en.wikipedia.org/wiki/Limit_ordinal\<close>.\<close>

definition "limit X \<equiv> ordinal X \<and> 0 \<in> X \<and> (\<forall>x \<in> X. succ x \<in> X)"

lemma limitI:
  assumes "ordinal X"
  and "0 \<in> X"
  and "\<And>x. x \<in> X \<Longrightarrow> succ x \<in> X"
  shows "limit X"
  using assms unfolding limit_def by auto

lemma limitE:
  assumes "limit X"
  obtains "ordinal X" "0 \<in> X" "\<And>x. x \<in> X \<Longrightarrow> succ x \<in> X"
  using assms unfolding limit_def by auto

text\<open>For the second induction theorem, some lemmas are left unproven.\<close>

lemma Limit_eq_Sup_self: "limit X \<Longrightarrow> \<Union>X = X"
  sorry

lemma ordinal_cases [cases type: set, case_names 0 succ limit]:
  assumes "ordinal k"
  obtains "k = 0" | l where "ordinal l" "succ l = k" | "limit k"
  sorry

lemma elts_succ [simp]: "{xx | xx \<in> (succ x)} = insert x {xx | xx \<in> x}"
  by (simp add: succ_eq_insert)

lemma image_ident: "image id Y = Y"
  by auto

text\<open>Standard ordinal induction:\<close>

lemma ordinal_induct [consumes 1, case_names zero succ limit, induct type: set]:
  assumes a: "ordinal X"
  and P: "P 0" "\<And>X. \<lbrakk>ordinal X; P X\<rbrakk> \<Longrightarrow> P (succ X)"
    "\<And>X. \<lbrakk>limit X; \<And>x. x \<in> X \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P (\<Union>X)"
  shows "P X"
using a
proof (induction X rule: ordinal_mem_induct)
  case (step X)
  then show ?case
  proof (cases rule: ordinal_cases)
    case 0
    with P(1) show ?thesis by simp
  next
    case (succ l)
    from succ step succ_eq_insert have "P (succ l)" by (intro P(2)) auto
    with succ show ?thesis by simp
  next
    case limit
text\<open>Missing proof see 
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_in_HOL.thy#L991\<close>.\<close>
    then show ?thesis sorry
  qed
qed

end

end
