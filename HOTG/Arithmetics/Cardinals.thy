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

context
  fixes P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool" and P'' :: "'c \<Rightarrow> bool"
  and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a" and f' :: "'b \<Rightarrow> 'c" and g' :: "'c \<Rightarrow> 'b"
begin

lemma do_we_need_this_hmm:
  assumes "injective_on P f"
  and "surjective_at P' f"
  and "([P] \<Rrightarrow>\<^sub>m P') f"
  obtains h where "bijection_on P P' f h"
  oops

lemma inverse_on_compI:
  assumes "inverse_on P f g"
  and "inverse_on P' f' g'"
  and "([P] \<Rrightarrow>\<^sub>m P') f"
  shows "inverse_on P (f' \<circ> f) (g \<circ> g')"
  oops

lemma bijection_on_compI:
  assumes "bijection_on P P' f g"
  and "bijection_on P' P'' f' g'"
  shows "bijection_on P P'' (f' \<circ> f) (g \<circ> g')"
  using assms
  apply (intro bijection_onI)
  apply (rule dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI')
  apply (elim bijection_onE)
  apply assumption
  apply (elim bijection_onE)
  apply assumption
  apply (rule dep_mono_wrt_pred_comp_dep_mono_wrt_pred_compI')
  apply (elim bijection_onE)
  apply assumption
  apply (elim bijection_onE)
  apply assumption
  sorry

end

lemma transitive_equipollent: "transitive (\<approx>)"
  by (intro transitiveI) (fastforce dest: bijection_on_compI)

lemma partial_equivalence_rel_equipollent: "partial_equivalence_rel (\<approx>)"
  by (intro partial_equivalence_relI transitive_equipollent symmetric_equipollent)

lemma equivalence_rel_equipollent: "equivalence_rel (\<approx>)"
  by (intro equivalence_relI partial_equivalence_rel_equipollent reflexive_equipollent)

(* preorder*)

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

lemma cardinality_cardinality_eq_cardinality [simp]: "||X|| = |X|"
  by (intro cardinality_eq_if_equipollent cardinal_equipollent_self)

definition "cardinal_add \<kappa> \<mu> \<equiv> cardinality (\<kappa> \<Coprod> \<mu>)"

bundle hotg_cardinal_add_syntax begin notation cardinal_add (infixl "\<oplus>" 65) end
bundle no_hotg_cardinal_add_syntax begin no_notation cardinal_add (infixl "\<oplus>" 65) end
unbundle hotg_cardinal_add_syntax

(* lemma inl_nonzero [simp]:"inl x \<noteq> {}"
  by (auto simp: inl_def)

lemma inr_nonzero [simp]:"inr x \<noteq> {}"
  by (auto simp:inr_def) *)

(*why intersection*)

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

lemma cardinal_disjoint_sup:
  assumes "X \<inter> Y = {}"
  shows "|X \<union> Y| = cardinal_add |X| |Y|"
proof-
  have "X \<union> Y \<approx> X \<Coprod> Y"
  proof -
    let ?f = "\<lambda>z. if z \<in> X then inl z else inr z"
    let ?g = "coprod_rec id id"
    have "bijection_on (\<lambda>x. x \<in> X \<union> Y) (\<lambda>x. x \<in> X \<Coprod> Y) ?f ?g" sorry
    then show ?thesis by blast
  qed
  then show ?thesis sorry
qed

lemma vcard_add: "cardinality (X + Y) = cardinal_add (cardinality X) (cardinality Y)"
  using card_lift [of X Y] bin_inter_lift_self_eq_empty [of X]
  by (simp add: add_eq_bin_union_lift cardinal_disjoint_sup)

(*
  have "bijection_on ((mem_of ({ X + y | y \<in> Y })) (mem_of (lift X Y))) f g"
    unfolding bij_betw_def
    by (simp add: inj_on_def lift_def)
  then show "elts (lift x y) \<approx> elts y"
    using eqpoll_def eqpoll_sym by blast
*)

end