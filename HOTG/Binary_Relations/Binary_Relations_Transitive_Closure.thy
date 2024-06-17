\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
subsection \<open>Transitive Closure\<close>
theory Binary_Relations_Transitive_Closure
  imports
    HOTG_Ordinals_Base
    HOTG_Binary_Relations_Pow
begin

unbundle no_HOL_order_syntax

(*TODO: could already be defined differently without sets in HOL_Basics library*)
definition "trans_closure R x y \<equiv> (\<exists>n. rel_pow R n x y)"

lemma trans_closureI [intro]:
  assumes "rel_pow R n x y"
  shows "trans_closure R x y"
  using assms unfolding trans_closure_def by auto

lemma trans_closureE [elim]:
  assumes "trans_closure R x y"
  obtains n where "rel_pow R n x y"
  using assms unfolding trans_closure_def by auto

lemma transitive_trans_closure: "transitive (trans_closure R)"
proof -
  have "trans_closure R x z" if "trans_closure R x y" "rel_pow R n y z" for n x y z using that
  proof (induction n arbitrary: y z rule: mem_induction)
    case (mem n)
    consider "R y z" | m u where "m \<in> n" "rel_pow R m y u" "R u z"
      using \<open>rel_pow R n y z\<close> by (blast elim: rel_powE)
    then show ?case
    proof cases
      case 1
      from \<open>trans_closure R x y\<close> obtain k where "rel_pow R k x y" by auto
      from \<open>R y z\<close> have "rel_pow R (succ k) x z"
        using rel_pow_iff[of R] \<open>rel_pow R k x y\<close> succ_eq_insert_self by blast
      then show ?thesis by blast
    next
      case 2
      from mem.IH have "trans_closure R x u"
        using \<open>m \<in> n\<close> \<open>trans_closure R x y\<close> \<open>rel_pow R m y u\<close> by blast
      then obtain k where "rel_pow R k x u" by auto
      then have "rel_pow R (succ k) x z"
        using \<open>R u z\<close> rel_pow_iff[of R] succ_eq_insert_self by blast
      then show ?thesis by blast
    qed
  qed
  then have "trans_closure R x z" if "trans_closure R x y" "trans_closure R y z" for x y z
    using that by blast
  then show ?thesis by fast
qed

lemma trans_closure_if_rel: "R x y \<Longrightarrow> trans_closure R x y"
  using rel_pow_if_rel[of R] by fast

lemma trans_closure_cases:
  assumes "trans_closure R x y"
  obtains (rel) "R x y" | (step) z where "trans_closure R x z" "R z y"
  using assms rel_powE[of R] by blast

lemma rel_if_rel_pow_if_le_if_transitive:
  includes HOL_order_syntax no_hotg_le_syntax
  assumes "transitive S"
  and "R \<le> S"
  and "rel_pow R n x y"
  shows "S x y"
using \<open>rel_pow R n x y\<close>
proof (induction n arbitrary: y rule: mem_induction)
  case (mem n)
  show ?case using \<open>rel_pow R n x y\<close>
  proof (cases rule: rel_powE)
    case rel
    then show ?thesis using \<open>R \<le> S\<close> by blast
  next
    case (step m z)
    with mem.IH have "S x z" by blast
    then show ?thesis using \<open>R z y\<close> \<open>R \<le> S\<close> \<open>transitive S\<close> by blast
  qed
qed

corollary rel_if_trans_closure_if_le_if_transitive:
  includes HOL_order_syntax no_hotg_le_syntax
  assumes "transitive S"
  and "R \<le> S"
  and "trans_closure R x y"
  shows "S x y"
  using assms rel_if_rel_pow_if_le_if_transitive by (elim trans_closureE)

text \<open>Note: together,
@{thm transitive_trans_closure trans_closure_if_rel rel_if_trans_closure_if_le_if_transitive}
show that @{term "trans_closure R"} satisfies the universal property:
it is the smallest transitive relation containing @{term R}.\<close>

lemma trans_closure_mem_eq_lt: "trans_closure (\<in>) = (<)"
proof -
  have "trans_closure (\<in>) x y \<Longrightarrow> x < y" for x y
    by (rule rel_if_trans_closure_if_le_if_transitive[where ?R="(\<in>)"])
    (use transitive_lt lt_if_mem in auto)
  moreover have "x < y \<Longrightarrow> trans_closure (\<in>) x y" for x y
  proof (induction y rule: mem_induction)
    case (mem y)
    from \<open>x < y\<close> obtain z where "x \<le> z" "z \<in> y" using lt_mem_leE by blast
    then show ?case
    proof (cases rule: leE)
      case lt
      with \<open>z \<in> y\<close> mem.IH have "trans_closure (\<in>) x z" by blast
      then show ?thesis using \<open>z \<in> y\<close> transitive_trans_closure[of "(\<in>)"]
      by (blast dest: trans_closure_if_rel)
    next
      case eq
      then show ?thesis using \<open>z \<in> y\<close> trans_closure_if_rel by auto
    qed
  qed
  ultimately show ?thesis by fastforce
qed

end