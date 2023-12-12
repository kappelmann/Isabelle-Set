theory Mem_Transitive_Closure
  imports
    Transport.Functions_Injective
    Functions_Restrict
    Foundation
    Union_Intersection
begin

(*TODO Kevin: rename to binary_relation_restrict*)
unbundle no_restrict_syntax
unbundle no_HOL_ascii_syntax

overloading
  fun_restrict_set \<equiv> "fun_restrict :: (set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> 'a"
begin
  definition "fun_restrict_set f X \<equiv> f\<restriction>\<^bsub>mem_of X\<^esub> :: set \<Rightarrow> 'a"
end

lemma fun_restrict_set_eq_fun_restrict [simp]: "(f :: set \<Rightarrow> 'a)\<restriction>\<^bsub>X\<^esub> = f\<restriction>\<^bsub>mem_of X\<^esub>"
  unfolding fun_restrict_set_def by auto

axiomatization transrec :: "((set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a"
  where transrec_eq: "transrec f X = f ((transrec f)\<restriction>\<^bsub>X\<^esub>) X"

paragraph \<open>Transitive Closure\<close>

definition "image f A \<equiv> {f x | x \<in> A}"

lemma image_eq_repl [simp]: "image f A = repl A f"
  unfolding image_def by simp

lemma repl_fun_restrict_eq_repl [simp]: "{f\<restriction>\<^bsub>A\<^esub> x | x \<in> A} = {f x | x \<in> A}"
  by simp

lemma injective_image_if_injective:
  assumes "injective f"
  shows "injective (image f)"
  by (intro injectiveI eqI) (use assms in \<open>auto dest: injectiveD\<close>)

lemma injective_if_injective_image:
  assumes "injective (image f)"
  shows "injective f"
proof (rule injectiveI)
  fix X Y assume "f X = f Y"
  then have "image f {X} = image f {Y}" by simp
  with assms show "X = Y" by (blast dest: injectiveD)
qed

corollary injective_image_iff_injective [iff]: "injective (image f) \<longleftrightarrow> injective f"
  using injective_image_if_injective injective_if_injective_image by blast


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

lemma mem_eq_mem_trans_closure:
"X \<in> mem_trans_closure Y \<longleftrightarrow>  X \<in> Y \<or> (X\<in> (\<Union>y \<in> Y. mem_trans_closure y))"
  by (subst mem_trans_closure_eq_bin_union_idx_union) auto

lemma mem_trans_closure_empty_eq_empty [simp]: "mem_trans_closure {} = {}"
  by (simp add: mem_trans_closure_eq_bin_union_idx_union[where ?X="{}"])

lemma mem_trans_closed_mem_trans_closure: "mem_trans_closed (mem_trans_closure X)"
proof (induction X)
  case (mem X)
  show ?case
  proof (rule mem_trans_closedI')
    fix x y assume "x \<in> mem_trans_closure X" "y \<in> x"
    then show "y \<in> mem_trans_closure X"
    proof (cases rule: mem_mem_trans_closureE)
      case mem
      moreover have "y \<in> mem_trans_closure x" using \<open>y \<in> x\<close> subset_mem_trans_closure_self by blast
      ultimately show ?thesis by (subst mem_trans_closure_eq_bin_union_idx_union) blast
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

(*TODO Fang: prove this*)
lemma mem_mem_trans_closure_trans:
  assumes "X \<in> mem_trans_closure Y"
  and "Y \<in> mem_trans_closure Z"
shows "X \<in> mem_trans_closure Z"
proof (rule ccontr)
  assume con:"X \<notin> mem_trans_closure Z"
  then show False 
  proof -
    have "X \<notin> Z \<and> (X\<notin> (\<Union>z \<in> Z. mem_trans_closure z))"
      using con by (auto simp: mem_eq_mem_trans_closure)
    with assms(1) have "Y \<notin> Z"
      by auto
    with assms(2) have "Y\<in> (\<Union>z \<in> Z. mem_trans_closure z)"
      by (auto simp: mem_eq_mem_trans_closure)
    then obtain yy where "yy \<in> Z" "Y \<in> mem_trans_closure yy" by blast
    then have "yy \<in> mem_trans_closure Z" 
      by (simp add: mem_mem_trans_closure_if_mem)
    then have "Y \<notin> mem_trans_closure Z"
      sorry
    with assms show False by simp
  qed
qed


end
