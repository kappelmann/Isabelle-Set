\<^marker>\<open>creator "Niklas Krofta"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOTG_Cardinals_Multiplication
  imports HOTG_Cardinals_Base HOTG_Pairs
begin

unbundle no_HOL_groups_syntax

definition "cardinal_mul X Y \<equiv> |X \<times> Y|"

bundle hotg_cardinal_mul_syntax begin notation cardinal_mul (infixl "\<otimes>" 65) end
bundle no_hotg_cardinal_mul_syntax begin no_notation cardinal_mul (infixl "\<otimes>" 65) end
unbundle hotg_cardinal_mul_syntax

lemma cardinal_mul_eq_cardinality_pair: "X \<otimes> Y = |X \<times> Y|"
  unfolding cardinal_mul_def ..

lemma pair_equipollent_self_commute: "X \<times> Y \<approx> Y \<times> X"
  by (intro equipollentI[where ?f=swap and ?g=swap]) fastforce

lemma cardinal_mul_comm: "X \<otimes> Y = Y \<otimes> X"
  unfolding cardinal_mul_eq_cardinality_pair
  by (intro cardinality_eq_if_equipollent pair_equipollent_self_commute)

lemma empty_pair_equipollent_self: "{} \<times> X \<approx> {}"
  by (intro equipollentI) fastforce

corollary zero_cardinal_mul_eq_zero [simp]: "0 \<otimes> X = 0"
  unfolding cardinal_mul_eq_cardinality_pair by (subst cardinality_zero_eq_zero[symmetric])
  (intro cardinality_eq_if_equipollent empty_pair_equipollent_self)

lemma pair_equipollent_assoc: "(X \<times> Y) \<times> Z \<approx> X \<times> (Y \<times> Z)"
proof (rule equipollentI)
   show "bijection_on ((X \<times> Y) \<times> Z :: set) (X \<times> (Y \<times> Z))
      (\<lambda>\<langle>p, z\<rangle>. \<langle>fst p, \<langle>snd p, z\<rangle>\<rangle>)
      (\<lambda>\<langle>x, p\<rangle>. \<langle>\<langle>x, fst p\<rangle>, snd p\<rangle>)"
    by (urule (rr) bijection_onI dep_mono_wrt_predI inverse_onI) fastforce+
qed

lemma pair_equipollent_if_equipollent:
  assumes "X \<approx> X'" and "Y \<approx> Y'"
  shows "X \<times> Y \<approx> X' \<times> Y'"
proof -
  from assms obtain fX gX fY gY where bijections:
    "bijection_on X X' (fX :: set \<Rightarrow> set) (gX :: set \<Rightarrow> set)"
    "bijection_on Y Y' (fY :: set \<Rightarrow> set) (gY :: set \<Rightarrow> set)"
    by (elim equipollentE)
  let ?f = "\<lambda>\<langle>x, y\<rangle>. \<langle>fX x, fY y\<rangle>"
  let ?g = "\<lambda>\<langle>x, y\<rangle>. \<langle>gX x, gY y\<rangle>"
  have "bijection_on (X \<times> Y :: set) (X' \<times> Y') ?f ?g"
    by (urule (rr) bijection_onI mono_wrt_predI inverse_onI)
    (use bijections in \<open>auto 0 4 simp: bijection_on_left_right_eq_self
      dest: bijection_on_right_left_if_bijection_on_left_right\<close>)
  then show ?thesis by auto
qed

corollary cardinality_pair_cardinality_equipollent_pair: "|X| \<times> |Y| \<approx> X \<times> Y"
  by (rule pair_equipollent_if_equipollent) simp_all

corollary cardinality_cardinal_mul_eq_cardinal_mul [simp]: "|X| \<otimes> |Y| = X \<otimes> Y"
  unfolding cardinal_mul_eq_cardinality_pair
  by (intro cardinality_eq_if_equipollent cardinality_pair_cardinality_equipollent_pair)

lemma cardinal_mul_assoc: "(X \<otimes> Y) \<otimes> Z = X \<otimes> (Y \<otimes> Z)"
proof -
  have "|(X \<times> Y)| \<times> Z \<approx> (X \<times> Y) \<times> Z"
    using reflexive_equipollent by (blast intro: pair_equipollent_if_equipollent dest: reflexiveD)
  moreover have "... \<approx> X \<times> (Y \<times> Z)" by (simp add: pair_equipollent_assoc)
  moreover have "... \<approx> X \<times> |Y \<times> Z|" using partial_equivalence_rel_equipollent
    by (blast intro: pair_equipollent_if_equipollent dest: reflexiveD symmetricD)
  ultimately have "|(X \<times> Y)| \<times> Z \<approx> X \<times> |Y \<times> Z|" using transitive_equipollent by blast
  then show ?thesis
    by (auto intro: cardinality_eq_if_equipollent simp: cardinal_mul_eq_cardinality_pair)
qed

end
