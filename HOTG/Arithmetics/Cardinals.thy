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
  using assms by (intro inverse_onI) (auto simp: inverse_onD)

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
   apply (elim bijection_onE)
   apply (auto intro: inverse_on_compI)
  apply (elim bijection_onE)
(*dk why dont work*)
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



lemma coprod_commutative_eqpoll:"X \<Coprod> Y \<approx> Y \<Coprod> X"
proof (intro equipollentI)
  have mono:"([(\<lambda>x. x \<in> X \<Coprod> Y)] \<Rrightarrow>\<^sub>m (\<lambda>x. x \<in> Y \<Coprod> X)) (coprod_rec inr inl)"
   "([(\<lambda>x. x \<in> Y \<Coprod> X)] \<Rrightarrow>\<^sub>m (\<lambda>x. x \<in> X \<Coprod> Y)) (coprod_rec inr inl)"
     apply(rule mem_coprodE)
       apply(rule dep_mono_wrt_predE)
         apply auto
    sorry
  also have inv:"inverse_on (\<lambda>x. x \<in> X \<Coprod> Y) (coprod_rec inr inl) (coprod_rec inr inl)"
            "inverse_on (\<lambda>x. x \<in> Y \<Coprod> X) (coprod_rec inr inl) (coprod_rec inr inl)"
    by (auto simp: inverse_onD)
  then show "bijection_on (\<lambda>x. x \<in> X \<Coprod> Y) (\<lambda>x. x \<in> Y \<Coprod> X) (coprod_rec inr inl) (coprod_rec inr inl)"
    using mono inv by auto
qed 

lemma cardinal_add_commutative:"X \<oplus> Y = Y \<oplus> X"
  by (auto simp: cardinal_add_def coprod_commutative_eqpoll cardinality_eq_if_equipollent)

find_theorems name:"dep_mono_wrt_predI"

lemma coprod_zero_eqpoll: "0 \<Coprod> X \<approx> X"
proof -
  have invP:"inverse_on (mem_of {inr b | b \<in> X}) snd inr" "inverse_on (mem_of X) inr snd"
    by (auto simp: inverse_on_pred_def inr_def)
  then have "bijection_on (mem_of {inr b | b \<in> X}) (mem_of X) snd inr"
    by (intro bijection_onI)(auto simp:inr_def invP)
  then show ?thesis 
    by (auto simp:coprod_def)
qed

lemma coprod_assoc_eqpoll: "(X \<Coprod> Y) \<Coprod> Z \<approx> X \<Coprod> (Y \<Coprod> Z)"
proof (intro equipollentI)
   show "bijection_on (\<lambda>x. x \<in> X \<Coprod> Y \<Coprod> Z) (\<lambda>x. x \<in> X \<Coprod> (Y \<Coprod> Z)) 
(coprod_rec (coprod_rec inl (\<lambda>x. inr (inl x)))  inr)  
(coprod_rec (\<lambda>x. inl (inl x)) (coprod_rec (\<lambda>x. inl (inr x)) inr))" sorry
qed

lemma cardinal_add_assoc_eq:"(X \<oplus> Y) \<oplus> Z = X \<oplus> (Y \<oplus> Z)"
  sorry

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
  shows "|X \<union> Y| = |X| \<oplus> |Y|"
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