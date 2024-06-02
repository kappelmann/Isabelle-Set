theory HOTG_Cardinals_Multiplication
  imports HOTG_Cardinals_Base HOTG_Pairs
begin

unbundle no_HOL_groups_syntax

definition cardinal_mul :: "set \<Rightarrow> set \<Rightarrow> set" where
"cardinal_mul \<kappa> \<mu> \<equiv> |\<kappa> \<times> \<mu>|"

bundle hotg_cardinal_mul_syntax begin notation cardinal_mul (infixl "\<otimes>" 65) end
bundle no_hotg_cardinal_mul_syntax begin no_notation cardinal_mul (infixl "\<otimes>" 65) end
unbundle hotg_cardinal_mul_syntax

lemma cardinal_mul_eq_cardinality_cartprod: "X \<otimes> Y = |X \<times> Y|"
  unfolding cardinal_mul_def ..

lemma cartprod_equipollent_if_equipollent:
  assumes "X \<approx> X'" and "Y \<approx> Y'"
  shows "X \<times> Y \<approx> X' \<times> Y'"
proof -
  from assms obtain fX gX fY gY where bijections:
    "bijection_on X X' (fX :: set \<Rightarrow> set) (gX :: set \<Rightarrow> set)"
    "bijection_on Y Y' (fY :: set \<Rightarrow> set) (gY :: set \<Rightarrow> set)"
    by (elim equipollentE)
  let ?f = "\<lambda>\<langle>x,y\<rangle>. \<langle>fX x, fY y\<rangle>"
  let ?g = "\<lambda>\<langle>x,y\<rangle>. \<langle>gX x, gY y\<rangle>"
  have "bijection_on (X \<times> Y :: set) (X' \<times> Y') ?f ?g"
    by (urule (rr) bijection_onI mono_wrt_predI inverse_onI)
    (use bijections in \<open>auto 0 4 simp: bijection_on_left_right_eq_self
      dest: bijection_on_right_left_if_bijection_on_left_right\<close>)
  then show ?thesis by auto 
qed

corollary cardinality_cartprod_equipollent_cartprod: "|X| \<times> |Y| \<approx> X \<times> Y"
  using cartprod_equipollent_if_equipollent by auto

corollary cardinality_mul_eq_cartprod_cardinality: "|X| \<otimes> |Y| = |X \<times> Y|"
  using cardinal_mul_eq_cardinality_cartprod cardinality_cartprod_equipollent_cartprod 
  using cardinality_eq_if_equipollent by auto

end