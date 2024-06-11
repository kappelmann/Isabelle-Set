\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transitive Closure With Respect To Membership\<close>
theory HOTG_Mem_Transitive_Closure
  imports
    HOTG_Foundation
    HOTG_Mem_Transitive_Closed
begin

paragraph \<open>Summary\<close>
text \<open>The transitive closure of a set @{term "X ::set"} is the set that contains as its members
all sets that are transitively contained in @{term "X ::set"}.
In particular, each such set is transitively closed.

We follow the approach from \<^cite>\<open>ZFC_in_HOL_AFP\<close>,
\<^url>\<open>https://foss.heptapod.net/isa-afp/afp-devel/-/blob/06458dfa40c7b4aaaeb855a37ae77993cb4c8c18/thys/ZFC_in_HOL/ZFC_Cardinals.thy#L410\<close>.\<close>

definition "is_mem_trans_closure_of X T 
  \<longleftrightarrow> (mem_trans_closed T \<and> X \<subseteq> T \<and> (\<forall>Y : mem_trans_closed. X \<subseteq> Y \<longrightarrow> T \<subseteq> Y))"

definition "mem_trans_closure X = (THE T. is_mem_trans_closure_of X T)"

lemma is_mem_trans_closure_ofI:
  assumes "mem_trans_closed T" "X \<subseteq> T" "\<And>Y. mem_trans_closed Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> T \<subseteq> Y"
  shows "is_mem_trans_closure_of X T"
  using assms unfolding is_mem_trans_closure_of_def by blast

lemma is_mem_trans_closure_ofE:
  assumes "is_mem_trans_closure_of X T"
  shows "mem_trans_closed T" "X \<subseteq> T" "\<And>Y. mem_trans_closed Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> T \<subseteq> Y"
  using assms unfolding is_mem_trans_closure_of_def by auto

lemma eq_mem_trans_closure_if_is_mem_trans_closure_of:
  assumes "is_mem_trans_closure_of X T"
  shows "T = mem_trans_closure X"
proof -
  have "T = \<TT>" if "is_mem_trans_closure_of X \<TT>" for \<TT>
    using assms that by (force elim: is_mem_trans_closure_ofE)
  then have "\<exists>!T. is_mem_trans_closure_of X T" using assms by blast
  from the1_equality[OF this] show ?thesis using assms mem_trans_closure_def by auto
qed

corollary is_mem_trans_closure_of_mem_trans_closure_if_is_mem_trans_closure_of:
  assumes "is_mem_trans_closure_of X T"
  shows "is_mem_trans_closure_of X (mem_trans_closure X)"
  using assms eq_mem_trans_closure_if_is_mem_trans_closure_of by blast

lemma has_mem_trans_closure_if_elements_have:
  assumes trans_closure_elems: "\<And>x. x \<in> X \<Longrightarrow> is_mem_trans_closure_of x (mem_trans_closure x)"
  defines "T \<equiv> X \<union> (\<Union>x \<in> X. mem_trans_closure x)"
  shows "is_mem_trans_closure_of X T"
proof (intro is_mem_trans_closure_ofI)
  show "mem_trans_closed T"
  proof (intro mem_trans_closedI)
    fix z assume "z \<in> T"
    then consider (mem) "z \<in> X" | (trans) x where "x \<in> X" "z \<in> mem_trans_closure x" using T_def by auto
    then show "z \<subseteq> T"
    proof cases
      case mem
      then have "z \<subseteq> mem_trans_closure z"
        using trans_closure_elems is_mem_trans_closure_ofE mem_trans_closedD by auto
      then show ?thesis using \<open>z \<in> X\<close> T_def by auto
    next
      case trans
      then have "z \<subseteq> mem_trans_closure x" 
        using trans_closure_elems is_mem_trans_closure_ofE mem_trans_closedD by auto
      then show ?thesis using \<open>x \<in> X\<close> T_def by auto
    qed
  qed
next
  show "X \<subseteq> T" using T_def by auto
next
  fix Y assume hY: "mem_trans_closed Y" "X \<subseteq> Y"
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
        using trans_closure_elems is_mem_trans_closure_ofE hY by blast
      then show ?thesis using trans by auto
    qed
  qed
qed

theorem is_mem_trans_closure_of_mem_trans_closure: 
  shows "is_mem_trans_closure_of X (mem_trans_closure X)"
proof (induction X rule: mem_induction)
  case (mem X)
  then show ?case using has_mem_trans_closure_if_elements_have
    using is_mem_trans_closure_of_mem_trans_closure_if_is_mem_trans_closure_of by blast
qed

corollary mem_trans_closure_eq_bin_union_idx_union:
  "mem_trans_closure X = X \<union> (\<Union>x \<in> X. mem_trans_closure x)"
  using has_mem_trans_closure_if_elements_have is_mem_trans_closure_of_mem_trans_closure
  using eq_mem_trans_closure_if_is_mem_trans_closure_of[symmetric] by auto

corollary subset_mem_trans_closure_self: "X \<subseteq> mem_trans_closure X"
  using is_mem_trans_closure_of_mem_trans_closure is_mem_trans_closure_ofE by auto

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
  using is_mem_trans_closure_of_mem_trans_closure is_mem_trans_closure_ofE by auto

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
  using is_mem_trans_closure_of_mem_trans_closure is_mem_trans_closure_ofE(3) by blast

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
