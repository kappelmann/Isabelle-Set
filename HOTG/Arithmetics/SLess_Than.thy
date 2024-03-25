\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Less-Than and Less-Than or Equal Orders\<close>
theory SLess_Than
  imports
    Mem_Transitive_Closure
    Transport.HOL_Syntax_Bundles_Orders
begin

paragraph \<open>Summary\<close>
text \<open>We define less and less-than or equal on sets and show that the latter is a partial order.\<close>

subsection \<open>Less-Than Order\<close>

text \<open>We follow the definition by Kirby \<^cite>\<open>kirby_set_arithemtics\<close>.\<close>

text \<open>A set \<open>X\<close> is smaller than a set \<open>Y\<close> if \<open>X\<close> is contained in the transitive closure of \<open>Y\<close>.\<close>

definition "lt X Y \<equiv> X \<in> mem_trans_closure Y"

bundle hotg_lt_syntax begin notation lt (infix "<" 50) end
bundle no_hotg_lt_syntax begin no_notation lt (infix "<" 50) end
unbundle
  hotg_lt_syntax
  no_HOL_order_syntax

lemma lt_iff_mem_trans_closure: "X < Y \<longleftrightarrow> X \<in> mem_trans_closure Y"
  unfolding lt_def by simp

lemma lt_if_mem_trans_closure:
  assumes "X \<in> mem_trans_closure Y"
  shows "X < Y"
  using assms unfolding lt_iff_mem_trans_closure by simp

corollary lt_if_mem:
  assumes "X \<in> Y"
  shows "X < Y"
  using assms subset_mem_trans_closure_self lt_if_mem_trans_closure by auto

lemma mem_trans_closure_if_lt:
  assumes "X < Y"
  shows "X \<in> mem_trans_closure Y"
  using assms unfolding lt_iff_mem_trans_closure by simp

lemma lt_if_lt_if_mem [trans]:
  assumes "x \<in> X"
  and "X < Y"
  shows "x < Y"
  using assms mem_trans_closed_mem_trans_closure unfolding lt_iff_mem_trans_closure by auto

lemma lt_trans [trans]:
  assumes "X < Y"
  and "Y < Z"
  shows "X < Z"
  using assms unfolding lt_iff_mem_trans_closure by (rule mem_mem_trans_closure_trans)

corollary transitive_lt: "transitive (<)"
  using lt_trans by blast

text \<open>The lemma demonstrates the anti-reflexivity of less.\<close>

lemma not_lt_self [iff]: "\<not>(X < X)"
  unfolding lt_iff_mem_trans_closure by auto

subsection \<open>Less-Than or Equal Order\<close>

definition "le X Y \<equiv> X < Y \<or> X = Y"

bundle hotg_le_syntax begin notation le (infix "\<le>" 60) end
bundle no_hotg_le_syntax begin no_notation le (infix "\<le>" 60) end
unbundle hotg_le_syntax

lemma le_if_lt:
  assumes "X < Y"
  shows "X \<le> Y"
  using assms unfolding le_def by auto

lemma le_self [iff]: "X \<le> X" unfolding le_def by simp

lemma leE:
  assumes "X \<le> Y"
  obtains (lt) "X < Y" | (eq) "X = Y"
  using assms unfolding le_def by auto

corollary le_iff_lt_or_eq: "X \<le> Y \<longleftrightarrow> X < Y \<or> X = Y"
  using le_if_lt leE by blast

lemma le_trans [trans]:
  assumes "X \<le> Y"
  and "Y \<le> Z"
  shows "X \<le> Z"
  using assms lt_trans unfolding le_iff_lt_or_eq by auto

corollary reflexive_le: "reflexive (\<le>)" by auto

corollary transitive_le: "transitive (\<le>)"
  using le_trans by blast

corollary preorder_le: "preorder (\<le>)"
  using reflexive_le transitive_le by blast

lemma lt_mem_leE:
  assumes "X < Y"
  obtains y where "y \<in> Y" "X \<le> y"
  using assms unfolding le_iff_lt_or_eq lt_iff_mem_trans_closure by auto

lemma lt_if_mem_if_le [trans]:
  assumes "X \<le> Y"
  and "Y \<in> Z"
  shows "X < Z"
  using assms mem_trans_closure_eq_bin_union_idx_union[of Z]
  unfolding le_iff_lt_or_eq lt_iff_mem_trans_closure
  by auto

corollary lt_iff_bex_le: "X < Y \<longleftrightarrow> (\<exists>y \<in> Y. X \<le> y)"
  by (auto elim: lt_mem_leE intro: lt_if_mem_if_le)

lemma lt_if_lt_if_le [trans]:
  assumes "X \<le> Y"
  and "Y < Z"
  shows "X < Z"
  using assms mem_trans_closure_eq_bin_union_idx_union[of Z] mem_mem_trans_closure_trans
  unfolding le_iff_lt_or_eq lt_iff_mem_trans_closure
  by blast

lemma lt_if_le_if_lt [trans]:
  assumes "X < Y"
  and "Y \<le> Z"
  shows "X < Z"
  using assms mem_trans_closure_eq_bin_union_idx_union[of Z] mem_mem_trans_closure_trans
  unfolding le_iff_lt_or_eq lt_iff_mem_trans_closure
  by blast

lemma not_le_if_lt: "X < Y \<Longrightarrow> \<not>(Y \<le> X)"
  using lt_trans le_iff_lt_or_eq by auto

lemma not_lt_if_le: "X \<le> Y \<Longrightarrow> \<not>(Y < X)"
  using not_le_if_lt by auto

lemma antisymmetric_le: "antisymmetric (\<le>)"
  unfolding le_iff_lt_or_eq using lt_trans by auto

corollary partial_order_le: "partial_order (\<le>)"
  using preorder_le antisymmetric_le by blast

text\<open>These next lemmas show some relationships between @{term "(<)"}, @{term "(\<le>)"} and
@{term "(=)"}.\<close>

lemma ne_if_lt:
  assumes "X < Y"
  shows "X \<noteq> Y"
  using assms by auto

lemma lt_if_ne_if_le:
  assumes "X \<le> Y"
  and "X \<noteq> Y"
  shows "X < Y"
  using assms unfolding le_iff_lt_or_eq by auto

corollary lt_iff_le_and_ne: "X < Y \<longleftrightarrow> X \<le> Y \<and> X \<noteq> Y"
  using le_if_lt ne_if_lt lt_if_ne_if_le by blast

lemma le_if_eq: "X = Y \<Longrightarrow> X \<le> Y"
  by simp

lemma not_lt_iff_not_le_or_eq: "\<not>(X < Y) \<longleftrightarrow> \<not>(X \<le> Y) \<or> X = Y"
  unfolding le_iff_lt_or_eq by auto

text \<open>The following sets up automation for goals involving the @{term "(\<le>)"}
and @{term "(<)"} relations.\<close>

local_setup \<open>
  HOL_Order_Tac.declare_order {
    ops = {eq = @{term \<open>(=) :: set \<Rightarrow> set \<Rightarrow> bool\<close>}, le = @{term \<open>(\<le>)\<close>}, lt = @{term \<open>(<)\<close>}},
    thms = {trans = @{thm le_trans}, refl = @{thm le_self}, eqD1 = @{thm le_if_eq},
      eqD2 = @{thm le_if_eq[OF sym]}, antisym = @{thm antisymmetricD[OF antisymmetric_le]},
      contr = @{thm notE}},
    conv_thms = {less_le = @{thm eq_reflection[OF lt_iff_le_and_ne]},
      nless_le = @{thm eq_reflection[OF not_lt_iff_not_le_or_eq]}}
  }
\<close>

end
