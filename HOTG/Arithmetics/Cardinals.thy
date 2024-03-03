theory Cardinals
  imports
    SAddition
    Coproduct
    Ordinals
    Transport.Functions_Bijection
    Transport.Equivalence_Relations
    Transport.Functions_Surjective
begin

(*TODO Kevin: bundle notation defined in this theory*)
(*TODO Kevin: tag bijection_onE as elim in AFP*)

unbundle no_HOL_groups_syntax no_HOL_ascii_syntax

definition "equipollent X Y \<equiv> \<exists>f g. bijection_on (mem_of X) (mem_of Y) (f :: set \<Rightarrow> set) g"

bundle hotg_equipollent_syntax begin notation equipollent (infixl "\<approx>" 50) end
bundle no_hotg_equipollent_syntax begin no_notation equipollent (infixl "\<approx>" 50) end
unbundle hotg_equipollent_syntax

lemma equipollentI [intro]:
  assumes "bijection_on (mem_of X) (mem_of Y) (f :: set \<Rightarrow> set) g"
  shows "X \<approx> Y"
  using assms by (auto simp: equipollent_def)

lemma equipollentE [elim]:
  assumes "X \<approx> Y"
  obtains f g where "bijection_on (mem_of X) (mem_of Y) (f :: set \<Rightarrow> set) g"
  using assms by (auto simp: equipollent_def)

lemma reflexive_equipollent: "reflexive (\<approx>)"
  using bijection_on_self_id by auto

lemma symmetric_equipollent: "symmetric (\<approx>)"
  by (intro symmetricI) (auto dest: bijection_on_right_left_if_bijection_on_left_right)

lemma inverse_on_compI:
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a" and f' :: "'b \<Rightarrow> 'c" and g' :: "'c \<Rightarrow> 'b"
  assumes "inverse_on P f g"
  and "inverse_on P' f' g'"
  and "([P] \<Rrightarrow>\<^sub>m P') f"
  shows "inverse_on P (f' \<circ> f) (g \<circ> g')"
  using assms by (intro inverse_onI) (auto dest!: inverse_onD)

lemma bijection_on_compI:
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool" and P'' :: "'c \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a" and f' :: "'b \<Rightarrow> 'c" and g' :: "'c \<Rightarrow> 'b"
  assumes "bijection_on P P' f g"
  and "bijection_on P' P'' f' g'"
  shows "bijection_on P P'' (f' \<circ> f) (g \<circ> g')"
  using assms by (intro bijection_onI)
  (auto intro: dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI' inverse_on_compI
    elim!: bijection_onE)

lemma transitive_equipollent: "transitive (\<approx>)"
  by (intro transitiveI) (blast intro: bijection_on_compI)

lemma preorder_equipollent: "preorder (\<approx>)"
  by (intro preorderI transitive_equipollent reflexive_equipollent)

lemma partial_equivalence_rel_equipollent: "partial_equivalence_rel (\<approx>)"
  by (intro partial_equivalence_relI transitive_equipollent symmetric_equipollent)

lemma equivalence_rel_equipollent: "equivalence_rel (\<approx>)"
  by (intro equivalence_relI partial_equivalence_rel_equipollent reflexive_equipollent)

definition "cardinality (X :: set) \<equiv> (LEAST Y. ordinal Y \<and> X \<approx> Y)"

bundle hotg_cardinality_syntax begin notation cardinality ("|_|") end
bundle no_hotg_cardinality_syntax begin no_notation cardinality ("|_|") end
unbundle hotg_cardinality_syntax

lemma Least_eq_Least_if_iff:
  assumes "\<And>Z. P Z \<longleftrightarrow> Q Z"
  shows "(LEAST Z. P Z) = (LEAST Z. Q Z)"
  using assms by simp

lemma cardinality_eq_if_equipollent:
  assumes "X \<approx> Y"
  shows "|X| = |Y|"
  unfolding cardinality_def using assms transitive_equipollent symmetric_equipollent
  by (intro Least_eq_Least_if_iff) (blast dest: symmetricD)

lemma cardinal_equipollent_self [iff]: "|X| \<approx> X"
  (*TODO: prove me later; needs order_types*)
  sorry

lemma cardinality_cardinality_eq_cardinality [simp]: "||X|| = |X|"
  by (intro cardinality_eq_if_equipollent cardinal_equipollent_self)

definition "cardinal_add \<kappa> \<mu> \<equiv> |\<kappa> \<Coprod> \<mu>|"

bundle hotg_cardinal_add_syntax begin notation cardinal_add (infixl "\<oplus>" 65) end
bundle no_hotg_cardinal_add_syntax begin no_notation cardinal_add (infixl "\<oplus>" 65) end
unbundle hotg_cardinal_add_syntax

lemma cardinal_add_eq_cardinality_coprod: "\<kappa> \<oplus> \<mu> = |\<kappa> \<Coprod> \<mu>|"
  unfolding cardinal_add_def ..

lemma equipollent_coprod_self_commute: "X \<Coprod> Y \<approx> Y \<Coprod> X"
  by (intro equipollentI[where ?f="coprod_rec inr inl" and ?g="coprod_rec inr inl"])
  (fastforce dest: inverse_onD)

lemma cardinal_add_comm: "X \<oplus> Y = Y \<oplus> X"
  unfolding cardinal_add_eq_cardinality_coprod
  by (intro cardinality_eq_if_equipollent cardinality_eq_if_equipollent equipollent_coprod_self_commute)

lemma coprod_zero_eqpoll: "{} \<Coprod> X \<approx> X"
  by (intro equipollentI[where ?f="coprod_rec inr id" and ?g="inr"] bijection_onI inverse_onI)
  auto

corollary zero_cardinal_add_eq_cardinality_self: "0 \<oplus> X = |X|"
  unfolding cardinal_add_eq_cardinality_coprod
  by (intro cardinality_eq_if_equipollent coprod_zero_eqpoll)

lemma coprod_assoc_eqpoll: "(X \<Coprod> Y) \<Coprod> Z \<approx> X \<Coprod> (Y \<Coprod> Z)"
proof (intro equipollentI)
   show "bijection_on (mem_of ((X \<Coprod> Y) \<Coprod> Z)) (mem_of (X \<Coprod> (Y \<Coprod> Z)))
      (coprod_rec (coprod_rec inl (inr \<circ> inl)) (inr \<circ> inr))
      (coprod_rec (inl \<circ> inl) (coprod_rec (inl \<circ> inr) inr))"
     by (intro bijection_onI inverse_onI dep_mono_wrt_predI) auto
 qed

lemma inverse_on_if_injectice:
  assumes "injective f"
  shows "\<exists>g. inverse_on (mem_of {f y | y \<in> Y}) g f"
proof -
  let ?g = "\<lambda>z. THE y. y \<in> Y \<and> z = f y"
  have "\<forall>y \<in> Y. (?g \<circ> f) y = y"
     using assms injectiveD by fastforce
  then have "inverse_on (mem_of {f y | y \<in> Y}) ?g f" by force
  then show ?thesis by auto
qed 

lemma card_lift_eq_card_right: "|lift X Y| = |Y|"
proof (intro cardinality_eq_if_equipollent equipollentI)
  let ?f = "\<lambda>z. THE y. y \<in> Y \<and> z = X + y"
  let ?g = "((+) X)"
  show "bijection_on (mem_of (lift X Y)) (mem_of Y) ?f ?g"
    by (intro bijection_onI dep_mono_wrt_predI)
    (auto intro: the1I2 simp: lift_eq_repl_add)
qed

lemma equipollent_bin_union_coprod_if_bin_inter_eq_empty:
  assumes "X \<inter> Y = {}"
  shows "X \<union> Y \<approx> X \<Coprod> Y"
proof -
  let ?l = "\<lambda>z. if z \<in> X then inl z else inr z"
  let ?r = "coprod_rec id id"
  from assms have "bijection_on (mem_of (X \<union> Y)) (mem_of (X \<Coprod> Y)) ?l ?r"
    by (intro bijection_onI dep_mono_wrt_predI inverse_onI) auto
  then show ?thesis by blast
qed

lemma equipollent_coprod_if_equipollent:
  assumes "X \<approx> X'"
  and "Y \<approx> Y'"
  shows "X \<Coprod> Y \<approx> X' \<Coprod> Y'"
proof -
  obtain fX gX fY gY where bijections:
      "bijection_on (mem_of X) (mem_of X') (fX :: set \<Rightarrow> set) gX"
      "bijection_on (mem_of Y) (mem_of Y') (fY :: set \<Rightarrow> set) gY"
    using assms by (elim equipollentE)
  let ?f = "coprod_rec (inl \<circ> fX) (inr \<circ> fY)"
  let ?g = "coprod_rec (inl \<circ> gX) (inr \<circ> gY)"
  have "bijection_on (mem_of (X \<Coprod> Y)) (mem_of (X' \<Coprod> Y')) ?f ?g"
    apply (intro bijection_onI dep_mono_wrt_predI inverse_onI)
    apply (auto elim: mem_coprodE)
    using bijections by (auto elim: mem_coprodE bijection_onE simp: bijection_on_left_right_eq_self
      dest: bijection_on_right_left_if_bijection_on_left_right)
  then show ?thesis by auto
qed

lemma cardinal_add_assoc_eq: "(X \<oplus> Y) \<oplus> Z = X \<oplus> (Y \<oplus> Z)"
proof -
  have "|(X \<Coprod> Y)| \<Coprod> Z \<approx> (X \<Coprod> Y) \<Coprod> Z"
    using reflexive_equipollent by (blast intro: equipollent_coprod_if_equipollent dest: reflexiveD)
  moreover have "... \<approx> X \<Coprod> (Y \<Coprod> Z)" by (simp add: coprod_assoc_eqpoll)
  moreover have "... \<approx> X \<Coprod> |Y \<Coprod> Z|"
    using partial_equivalence_rel_equipollent
    by (blast intro: equipollent_coprod_if_equipollent dest: reflexiveD symmetricD)
  ultimately have "|(X \<Coprod> Y)| \<Coprod> Z \<approx> X \<Coprod> |Y \<Coprod> Z|" using transitive_equipollent by blast
  then show ?thesis
    by (auto intro: cardinality_eq_if_equipollent simp: cardinal_add_eq_cardinality_coprod)
qed

lemma cardinal_disjoint_sup:
  assumes "X \<inter> Y = {}"
  shows "|X \<union> Y| = |X| \<oplus> |Y|"
proof-
  have cardinalization: "X \<Coprod> Y \<approx> |X| \<Coprod> |Y|"
    using symmetric_equipollent equipollent_coprod_if_equipollent by (force dest: symmetricD)
  show ?thesis
    apply (subst cardinal_add_eq_cardinality_coprod)
    apply (intro cardinality_eq_if_equipollent)
    apply (rule transitiveD[OF transitive_equipollent])
     apply (rule equipollent_bin_union_coprod_if_bin_inter_eq_empty)
      by (auto simp: assms cardinalization)
qed

lemma cardinality_add_eq_cardinal_add: "|X + Y| = |X| \<oplus> |Y|"
  using card_lift_eq_card_right by (simp add: add_eq_bin_union_lift cardinal_disjoint_sup)

end