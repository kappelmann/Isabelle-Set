theory HOTG_Additive_Order
  imports HOTG_Addition
begin

definition additively_divides :: "set \<Rightarrow> set \<Rightarrow> bool" where
"additively_divides x y \<longleftrightarrow> (\<exists>d. x + d = y)"

bundle hotg_additive_order_syntax begin notation additively_divides (infix "\<unlhd>" 50) end
bundle no_hotg_additive_order_syntax begin no_notation additively_divides (infix "\<unlhd>" 50) end
unbundle hotg_additive_order_syntax

lemma additively_dividesI[intro]:
  assumes "x + d = y"
  shows "x \<unlhd> y"
  unfolding additively_divides_def using assms by auto

lemma additively_dividesE[elim]:
  assumes "x \<unlhd> y"
  obtains d where "x + d = y"
  using assms unfolding additively_divides_def by auto

lemma subset_if_additively_divides: "x \<unlhd> y \<Longrightarrow> x \<subseteq> y" 
  using add_eq_bin_union_lift by force

lemma le_if_additively_divides: "x \<unlhd> y \<Longrightarrow> x \<le> y"
  using le_self_add by auto

lemma reflexive_additively_divides: "reflexive (\<unlhd>)"
  using add_zero_eq_self by blast

lemma antisymmetric_additively_divides: "antisymmetric (\<unlhd>)"
  using subset_if_additively_divides by auto

lemma additively_divides_trans[trans]: "x \<unlhd> y \<Longrightarrow> y \<unlhd> z \<Longrightarrow> x \<unlhd> z"
  using add_assoc by force

corollary transitive_additively_divides: "transitive (\<unlhd>)"
  using additively_divides_trans by auto

corollary preorder_additively_divides: "preorder (\<unlhd>)"
  using reflexive_additively_divides transitive_additively_divides by blast

corollary additively_divides_partial_order: "partial_order (\<unlhd>)"
  using preorder_additively_divides antisymmetric_additively_divides by auto

lemma additively_divides_if_sums_equal:
  assumes "a + b = c + d"
  shows "a \<unlhd> c \<or> c \<unlhd> a"
proof (rule ccontr)
  assume ac_incomparable: "\<not> (a \<unlhd> c \<or> c \<unlhd> a)"
  have "\<forall>z. a + x \<noteq> c + z" for x
  proof (induction x rule: mem_induction)
    case (mem x)
    show ?case
    proof (cases "x = 0")
      case True
      then show ?thesis using ac_incomparable by auto
    next
      case False
      show ?thesis
      proof (rule ccontr)
        assume "\<not> (\<forall>z. a + x \<noteq> c + z)"
        then obtain z where hz: "a + x = c + z" by auto
        then have "z \<noteq> 0" using add_zero_eq_self ac_incomparable by auto
        from \<open>x \<noteq> 0\<close> obtain v where "v \<in> x" by auto
        then have "a + v \<in> c + z" unfolding hz[symmetric] using add_eq_bin_union_repl_add[of a x] by auto
        then consider (c) "a + v \<in> c" | (\<lambda>) "a + v \<in> lift c z" unfolding add_eq_bin_union_lift by auto
        then show "False"
        proof (cases)
          case c                             
          have "lift c z \<subseteq> lift a x"
          proof (rule ccontr)
            assume "\<not> lift c z \<subseteq> lift a x"
            then have "\<exists>z' : lift c z.  z' \<in> a" using hz unfolding add_eq_bin_union_lift by auto
            then obtain w where "c + w \<in> a" using lift_eq_repl_add by auto
            then have "c + w \<in> a + v" using add_eq_bin_union_lift by auto
            moreover have "a + v \<in> c + w" using add_eq_bin_union_lift[of c w] using c by auto
            ultimately show "False" using not_mem_if_mem by auto
          qed
          moreover from mem have "lift a x \<inter> lift c z = 0" for z using lift_eq_repl_add by auto
          ultimately have "lift c z = 0" by auto
          then show "False" using lift_eq_repl_add \<open>z \<noteq> 0\<close> by auto
        next
          case \<lambda>
          then show "False" using lift_eq_repl_add mem.IH \<open>v \<in> x\<close> by auto
        qed
      qed
    qed
  qed
  then show "False" using assms by auto
qed

end