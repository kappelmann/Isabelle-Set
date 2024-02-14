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

lemma fdsf:"X \<approx> X"
  using bijection_on_self_id by auto



(* lemma do_we_need_this_hmm:
  assumes "injective_on P f"
  and "surjective_at P' f"
  and "([P] \<Rrightarrow>\<^sub>m P') f"
  obtains h where "bijection_on P P' f h"
  oops
 *)
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

lemma cardinal_equipollent_self: "|X| \<approx> X"
  (*TODO: prove me later; needs order_types*)
  sorry

lemma cardinal_equipollent_self_re: "X \<approx> |X|"
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
   show "bijection_on (\<lambda>x. x \<in> (X \<Coprod> Y) \<Coprod> Z) (\<lambda>x. x \<in> X \<Coprod> (Y \<Coprod> Z))
      (coprod_rec (coprod_rec inl (\<lambda>x. inr (inl x)))  (inr \<circ> inr))
      (coprod_rec (\<lambda>x. inl (inl x)) (coprod_rec (\<lambda>x. inl (inr x)) inr))"
     by (intro bijection_onI  inverse_onI dep_mono_wrt_predI) auto  
qed

lemma dadss:
  assumes "f X = f Y \<longleftrightarrow> X = Y"
  shows "equipollent (f X) X"
  apply (intro equipollentI[where ?g = "f"])
  apply (intro bijection_onI)
     defer
     defer
     apply (intro inverse_onI)
     defer
     apply (intro inverse_onI)
     defer                                   
     apply (intro dep_mono_wrt_predI)
     defer
     apply (intro dep_mono_wrt_predI)
  sorry

lemma card_lift_eq_card_id: "|lift X Y| = |Y|"
  by (auto simp: dadss cardinality_eq_if_equipollent)

(*have a function replacing X by zero or give up this way*)

lemma card_lift: "|lift X Y| = |Y|"
proof (intro cardinality_eq_if_equipollent equipollentI)
  let ?f = undefined
  show "bijection_on (mem_of (lift X Y)) (mem_of Y) ?f ((+) X)"
    apply (intro bijection_onI)
    defer
    apply (intro dep_mono_wrt_predI)
    apply (fact add_mem_lift_if_mem_right)
    defer
    apply (intro inverse_onI)
    sorry
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
  obtain fX gX where A:"bijection_on (mem_of X) (mem_of X') (fX :: set \<Rightarrow> set) gX"
    using assms by (auto dest: equipollentE)
  obtain fY gY where B:"bijection_on (mem_of Y) (mem_of Y') (fY :: set \<Rightarrow> set) gY"
    using assms by (auto dest: equipollentE)
  also have C:"bijection_on (mem_of X') (mem_of X) (gX :: set \<Rightarrow> set) fX"
            "bijection_on (mem_of Y') (mem_of Y) (gY :: set \<Rightarrow> set) fY"
    using A B by (auto simp: bijection_on_right_left_if_bijection_on_left_right)
  then have Loop:"\<forall>y \<in> Y. gY (fY y) = y" 
    "\<forall>y' \<in> Y'. fY (gY y') = y'"
"\<forall>x \<in> X. gX (fX x) = x"
"\<forall>x' \<in> X'. fX (gX x') = x'"
    using A B C by (auto simp: bijection_on_left_right_eq_self )
  let ?f = "coprod_rec (inl \<circ> fX) (inr \<circ> fY)"
  let ?g = "coprod_rec (inl \<circ> gX) (inr \<circ> gY)"
  have "bijection_on (mem_of (X \<Coprod> Y)) (mem_of (X' \<Coprod> Y')) ?f ?g"
 (*by (intro bijection_onI  inverse_onI dep_mono_wrt_predI) (auto simp: Bi) *)
     apply (intro bijection_onI)
        defer
        defer
       apply  (intro inverse_onI)
        apply (rule mem_coprodE)
     defer
     defer
          defer
       apply  (intro inverse_onI)
        apply (rule mem_coprodE)
             apply (auto)
          defer
     defer
        apply (intro dep_mono_wrt_predI) 
     apply (rule mem_coprodE)
          defer
     defer
     defer
        apply (intro dep_mono_wrt_predI) 
            apply (rule mem_coprodE)
    apply auto
     sorry

(*    apply (elim bijection_onE[where ?f = "fX" and ?g = "gX"]) 
    apply (elim bijection_onE[where ?f = "fY" and ?g = "gY"])*)
  then show ?thesis by auto
qed

lemma cardinal_add_assoc_eq:"(X \<oplus> Y) \<oplus> Z = X \<oplus> (Y \<oplus> Z)"
proof -
  have A:"|(X \<Coprod> Y)| \<Coprod> Z  \<approx> (X \<Coprod> Y) \<Coprod> Z"
    by (auto simp:equipollent_coprod_if_equipollent  cardinal_equipollent_self fdsf)
  have B:"(X \<Coprod> Y) \<Coprod> Z \<approx> X \<Coprod> (Y \<Coprod> Z)"
    by (simp add: coprod_assoc_eqpoll)
  have C:"X \<Coprod> (Y \<Coprod> Z) \<approx> X \<Coprod> |Y \<Coprod> Z|"
    by (auto simp:equipollent_coprod_if_equipollent fdsf cardinal_equipollent_self_re)
  have "|(X \<Coprod> Y)| \<Coprod> Z \<approx> X \<Coprod> |Y \<Coprod> Z|" 
  using A B C sorry (* transitive_equipollent *)
  then show ?thesis by (auto simp: cardinality_eq_if_equipollent cardinal_add_eq_cardinality_coprod)
qed


lemma cardinal_disjoint_sup:
  assumes "X \<inter> Y = {}"
  shows "|X \<union> Y| = |X| \<oplus> |Y|"
proof-
  have a: "X \<Coprod> Y \<approx> |X| \<Coprod> |Y|"
    using symmetric_equipollent equipollent_coprod_if_equipollent cardinal_equipollent_self
    by (force dest: symmetricD)
  show ?thesis
    apply (subst cardinal_add_eq_cardinality_coprod)
    apply (intro cardinality_eq_if_equipollent)
    apply (rule transitiveD[OF transitive_equipollent])
    apply (rule equipollent_bin_union_coprod_if_bin_inter_eq_empty)
    apply (fact assms)
    apply (rule a)
    done
qed

lemma cardinality_add_eq_cardinal_add: "|X + Y| = |X| \<oplus> |Y|"
  using card_lift by (simp add: add_eq_bin_union_lift cardinal_disjoint_sup)

(*
  have "bijection_on ((mem_of ({ X + y | y \<in> Y })) (mem_of (lift X Y))) f g"
    unfolding bij_betw_def
    by (simp add: inj_on_def lift_def)
  then show "elts (lift x y) \<approx> elts y"
    using eqpoll_def eqpoll_sym by blast
*)

end