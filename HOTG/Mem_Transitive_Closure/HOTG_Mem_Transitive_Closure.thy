\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transitive Closure With Respect To Membership\<close>
theory HOTG_Mem_Transitive_Closure
  imports
    HOTG_Foundation
    HOTG_Mem_Transitive_Closed_Base
    Transport.Binary_Relations_Least
begin

paragraph \<open>Summary\<close>
text \<open>The transitive closure of a set @{term "X ::set"} is the set that contains as its members
all sets that are transitively contained in @{term "X ::set"}.
In particular, each such set is transitively closed.

We follow the approach from \<^cite>\<open>ZFC_in_HOL_AFP\<close>.\<close>

definition "mem_trans_closure X = least_wrt_rel (\<subseteq>) ((\<subseteq>) X \<sqinter> mem_trans_closed)"

lemma is_least_wrt_rel_mem_trans_closed_if_mem_is_least_wrt_rel_mem_trans_closed:
  assumes trans_closure_elems:
    "\<And>x. x \<in> X \<Longrightarrow> is_least_wrt_rel (\<subseteq>) ((\<subseteq>) x \<sqinter> mem_trans_closed) (mem_trans_closure x)"
  defines "T \<equiv> X \<union> (\<Union>x \<in> X. mem_trans_closure x)"
  shows "is_least_wrt_rel (\<subseteq>) ((\<subseteq>) X \<sqinter> mem_trans_closed) T"
proof (intro is_least_wrt_rel_if_antisymmetric_onI is_minimal_wrt_relI inf1I)
  show "mem_trans_closed T"
  proof (intro mem_trans_closedI)
    fix z assume "z \<in> T"
    then consider (mem) "z \<in> X" | (step) x where "x \<in> X" "z \<in> mem_trans_closure x"
      using T_def by auto
    then show "z \<subseteq> T"
    proof cases
      case mem
      then have "z \<subseteq> mem_trans_closure z" using trans_closure_elems by auto
      then show ?thesis using \<open>z \<in> X\<close> T_def by auto
    next
      case step
      then have "z \<subseteq> mem_trans_closure x"
        using trans_closure_elems mem_trans_closedD by (blast elim!: is_least_wrt_relE)
      then show ?thesis using \<open>x \<in> X\<close> T_def by auto
    qed
  qed
next show "X \<subseteq> T" unfolding T_def by auto
next
  fix Y presume hY: "mem_trans_closed Y" "X \<subseteq> Y"
  show "T \<subseteq> Y"
  proof
    fix z assume "z \<in> T"
    then consider (mem) "z \<in> X" | (trans) x where "x \<in> X" "z \<in> mem_trans_closure x" using T_def by auto
    then show "z \<in> Y"
    proof cases
      case mem
      then show ?thesis using \<open>X \<subseteq> Y\<close> by auto
    next
      case trans
      then have "mem_trans_closure x \<subseteq> Y"
        using trans_closure_elems hY by (blast elim!: is_least_wrt_relE)
      then show ?thesis using trans by auto
    qed
  qed
qed auto

theorem is_least_wrt_rel_mem_trans_closure:
  "is_least_wrt_rel (\<subseteq>) ((\<subseteq>) X \<sqinter> mem_trans_closed) (mem_trans_closure X)"
proof (induction X rule: mem_induction)
  case (mem X)
  then show ?case by (subst mem_trans_closure_def, subst least_wrt_rel_eqI)
    (rule is_least_wrt_rel_mem_trans_closed_if_mem_is_least_wrt_rel_mem_trans_closed)
qed

corollary mem_trans_closure_eq_bin_union_idx_union:
  "mem_trans_closure X = X \<union> (\<Union>x \<in> X. mem_trans_closure x)"
  using is_least_wrt_rel_mem_trans_closure by (subst mem_trans_closure_def, subst least_wrt_rel_eqI)
  (auto intro: is_least_wrt_rel_mem_trans_closed_if_mem_is_least_wrt_rel_mem_trans_closed)

corollary subset_mem_trans_closure_self: "X \<subseteq> mem_trans_closure X"
  using mem_trans_closure_eq_bin_union_idx_union by blast

corollary mem_mem_trans_closure_if_mem: "X \<in> Y \<Longrightarrow> X \<in> mem_trans_closure Y"
  using subset_mem_trans_closure_self by blast

corollary mem_mem_trans_closure_if_mem_idx_union:
  assumes "X \<in> (\<Union>x \<in> Y. mem_trans_closure x)"
  shows "X \<in> mem_trans_closure Y"
  using assms by (subst mem_trans_closure_eq_bin_union_idx_union) auto

lemma mem_mem_trans_closureE [elim]:
  assumes "X \<in> mem_trans_closure Y"
  obtains (mem) "X \<in> Y" | (mem_trans_closure) y where "y \<in> Y" "X \<in> mem_trans_closure y"
  using assms by (subst (asm) mem_trans_closure_eq_bin_union_idx_union) auto

lemma mem_mem_trans_closure_iff_mem_or_mem:
  "X \<in> mem_trans_closure Y \<longleftrightarrow> X \<in> Y \<or> (X \<in> (\<Union>y \<in> Y. mem_trans_closure y))"
  by (subst mem_trans_closure_eq_bin_union_idx_union) auto

lemma mem_trans_closure_empty_eq_empty [simp]: "mem_trans_closure {} = {}"
  by (simp add: mem_trans_closure_eq_bin_union_idx_union[where ?X="{}"])

lemma mem_trans_closure_eq_empty_iff_eq_empty [iff]: "mem_trans_closure X = {} \<longleftrightarrow> X = {}"
  using subset_mem_trans_closure_self by auto

lemma mem_trans_closed_mem_trans_closure: "mem_trans_closed (mem_trans_closure X)"
  using is_least_wrt_rel_mem_trans_closure by auto

lemma not_mem_mem_trans_closure_self [iff]: "X \<notin> mem_trans_closure X"
proof
  assume "X \<in> mem_trans_closure X"
  then show False
  proof (cases rule: mem_mem_trans_closureE)
    case (mem_trans_closure x)
    with mem_trans_closed_mem_trans_closure show ?thesis by (induction X arbitrary: x) blast
  qed auto
qed

lemma mem_trans_closure_le_if_le_if_mem_trans_closed:
  "mem_trans_closed X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> mem_trans_closure Y \<subseteq> X"
  using is_least_wrt_rel_mem_trans_closure by blast

lemma mem_trans_closure_subset_mem_trans_closure_if_subset:
  assumes "Y \<subseteq> X"
  shows "mem_trans_closure Y \<subseteq> mem_trans_closure X"
  using assms subset_mem_trans_closure_self mem_trans_closed_mem_trans_closure
  by (intro mem_trans_closure_le_if_le_if_mem_trans_closed) auto

lemma mem_trans_closure_eq_self_if_mem_trans_closed [simp]:
  assumes "mem_trans_closed X"
  shows "mem_trans_closure X = X"
  using assms
  by (intro eq_if_subset_if_subset mem_trans_closure_le_if_le_if_mem_trans_closed subset_mem_trans_closure_self)
  auto

lemma mem_mem_trans_closure_if_mem_if_mem_mem_trans_closure:
  assumes "X \<in> mem_trans_closure Y"
  and "Y \<in> Z"
  shows "X \<in> mem_trans_closure Z"
  using assms by (auto iff: mem_mem_trans_closure_iff_mem_or_mem[of X Z])

text\<open>The next lemma demonstrates a transitivity property.\<close>

lemma mem_mem_trans_closure_trans:
  assumes "X \<in> mem_trans_closure Y"
  and "Y \<in> mem_trans_closure Z"
  shows "X \<in> mem_trans_closure Z"
using assms
proof (induction Z)
  case (mem Z)
  show ?case
  proof (cases "Z = {}")
    case False
    with mem obtain z where "z \<in> Z" "X \<in> mem_trans_closure z" by auto
    with mem show ?thesis using mem_mem_trans_closure_if_mem_if_mem_mem_trans_closure by auto
  qed (use mem in simp)
qed


end
