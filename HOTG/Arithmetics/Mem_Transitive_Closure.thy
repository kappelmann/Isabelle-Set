\<^marker>\<open>creator "Linghan Fang"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transitive Closure With Respect To Membership\<close>
theory Mem_Transitive_Closure
  imports
    Foundation
    Transfinite_Recursion
begin

definition "mem_trans_closure \<equiv> transrec (\<lambda>f X. X \<union> (\<Union>x \<in> X. f x))"

lemma mem_trans_closure_eq_bin_union_idx_union:
  "mem_trans_closure X = X \<union> (\<Union>x \<in> X. mem_trans_closure x)"
  by (simp add: mem_trans_closure_def transrec_eq[where ?X=X])

corollary subset_mem_trans_closure_self: "X \<subseteq> mem_trans_closure X"
  by (auto simp: mem_trans_closure_eq_bin_union_idx_union[where ?X= X])

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
  "X \<in> mem_trans_closure Y \<longleftrightarrow>  X \<in> Y \<or> (X \<in> (\<Union>y \<in> Y. mem_trans_closure y))"
  by (subst mem_trans_closure_eq_bin_union_idx_union) auto

lemma mem_trans_closure_empty_eq_empty [simp]: "mem_trans_closure {} = {}"
  by (simp add: mem_trans_closure_eq_bin_union_idx_union[where ?X="{}"])

lemma mem_trans_closure_eq_empty_iff_eq_empty [iff]: "mem_trans_closure X = {} \<longleftrightarrow> X = {}"
  using subset_mem_trans_closure_self by auto

lemma mem_trans_closed_mem_trans_closure: "mem_trans_closed (mem_trans_closure X)"
proof (induction X)
  case (mem X)
  show ?case
  proof (rule mem_trans_closedI')
    fix x y assume "x \<in> mem_trans_closure X" "y \<in> x"
    then show "y \<in> mem_trans_closure X"
    proof (cases rule: mem_mem_trans_closureE)
      case mem
      have "y \<in> mem_trans_closure x" using \<open>y \<in> x\<close> subset_mem_trans_closure_self by blast
      with mem show ?thesis by (subst mem_trans_closure_eq_bin_union_idx_union) blast
    next
      case mem_trans_closure
      with \<open>y \<in> x\<close> mem.IH show ?thesis by (subst mem_trans_closure_eq_bin_union_idx_union) blast
    qed
  qed
qed

lemma not_mem_trans_closure_self [iff]: "X \<notin> mem_trans_closure X"
proof
  assume "X \<in> mem_trans_closure X"
  then show False
  proof (cases rule: mem_mem_trans_closureE)
    case (mem_trans_closure x)
    with mem_trans_closed_mem_trans_closure show ?thesis by (induction X arbitrary: x) blast
  qed auto
qed

lemma mem_trans_closure_le_if_le_if_mem_trans_closed:
  "\<lbrakk>mem_trans_closed X;  Y \<le> X\<rbrakk> \<Longrightarrow> mem_trans_closure Y \<le> X"
proof (induction Y)
  case (mem Y)
  show ?case
  proof (cases "Y = {}")
    case False
    with mem have "(\<Union>y \<in> Y. mem_trans_closure y) \<le> X" by auto
    with mem.prems show ?thesis by (simp add: mem_trans_closure_eq_bin_union_idx_union[of Y])
  qed auto
qed

lemma mem_mem_trans_closure_mem_trans:
  assumes "X \<in> mem_trans_closure Y"
  and "Y \<in> Z"
shows "X \<in> mem_trans_closure Z"
  using assms by (auto simp:mem_mem_trans_closure_iff_mem_or_mem[of X Z])

(*TODO Fang: prove this*)
theorem mem_mem_trans_closure_trans:
  assumes "X \<in> mem_trans_closure Y"
  and "Y \<in> mem_trans_closure Z"
shows "X \<in> mem_trans_closure Z"
proof (induction Z)
  case (mem Z)
  then have sub:"\<forall>x \<in> Z. X \<in> mem_trans_closure x" using mem by auto
  show ?case 
  proof(cases"Z = {}")
    case True
    then show ?thesis sorry
  next
    case False
    then obtain zz where "zz \<in> Z" "X \<in> mem_trans_closure zz" using sub by auto
    then show ?thesis 
      using assms mem_mem_trans_closure_mem_trans sub by auto
  qed
qed

end
