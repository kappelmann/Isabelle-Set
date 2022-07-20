section \<open>Relations for Lifting\<close>
theory Lifting_Relations_New
  imports
    Binary_Relations_Base
    Functions_Base
begin

definition "Fun_Rel f x y \<equiv> f x = y"

lemma Fun_RelI:
  assumes "f x = y"
  shows "Fun_Rel f x y"
  unfolding Fun_Rel_def using assms by blast

lemma Fun_RelE:
  assumes "Fun_Rel f x y"
  obtains "f x = y"
  using assms unfolding Fun_Rel_def by blast

lemma left_total_Fun_Rel: "left_total (Fun_Rel f)"
  by (rule left_totalI) (blast intro: Fun_RelI in_domI)

lemma right_unique_Fun_Rel: "right_unique (Fun_Rel f)"
  by (rule right_uniqueI) (blast elim: Fun_RelE)

lemma rel_injective_on_Fun_Rel_if_injective_on:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> _"
  assumes "injective_on P f"
  shows "rel_injective_on P (Fun_Rel f)"
proof (rule rel_injective_onI)
  fix x x' y assume "Fun_Rel f x y" "Fun_Rel f x' y"
  then have "f x = f x'" by (blast elim: Fun_RelE)
  moreover assume "P x" "P x'"
  ultimately show "x = x'" using assms by (blast dest: injective_onD)
qed

lemma rel_injective_Fun_Rel_if_injective:
  assumes "injective f"
  shows "rel_injective (Fun_Rel f)"
  using assms
  by (intro rel_injectiveI) (blast elim!: Fun_RelE dest: injectiveD)

(* lemma z_property_Iso_Rel: "z_property (Iso_Rel A f)"
  using right_unique_Iso_Rel by (rule z_property_if_right_unique) *)

(* lemma lifting_relation_Iso_Rel: "lifting_relation (Iso_Rel A f)"
  using z_property_Iso_Rel by (rule lifting_relation_if_z_property) *)
lemma in_dom_Fun_Rel: "in_dom (Fun_Rel f) x"
  by (fact in_dom_if_left_total[OF left_total_Fun_Rel])

lemma in_codom_Fun_RelE:
  assumes "in_codom (Fun_Rel f) y"
  obtains x where "f x = y"
  using assms by (blast elim: in_codomE Fun_RelE)

lemma in_codom_Fun_RelI:
  assumes "f x = y"
  shows "in_codom (Fun_Rel f) y"
  using assms by (intro in_codomI) (blast intro: Fun_RelI)

lemma Fun_Rel_if_Fun_Rel_if_inverse:
  assumes "inverse f g"
  and "(Fun_Rel f) x y"
  shows "(Fun_Rel g) y x"
  using assms by (intro Fun_RelI) (blast elim: Fun_RelE dest: inverseD)

corollary Fun_Rel_if_Fun_Rel_if_bijection:
  assumes "bijection f g"
  and "(Fun_Rel f) x y"
  shows "(Fun_Rel g) y x"
  using assms by (blast intro: Fun_Rel_if_Fun_Rel_if_inverse dest: inverse_if_bijection)

corollary Fun_Rel_if_Fun_Rel_if_bijection':
  assumes "bijection f g"
  and "(Fun_Rel g) y x"
  shows "(Fun_Rel f) x y"
  using assms
  by (blast intro: Fun_Rel_if_Fun_Rel_if_bijection bijection_if_bijection)

corollary rel_inv_Fun_Rel_eq_Fun_Rel_if_bijection:
  assumes "bijection f g"
  shows "rel_inv (Fun_Rel f) = Fun_Rel g"
  using assms Fun_Rel_if_Fun_Rel_if_bijection Fun_Rel_if_Fun_Rel_if_bijection'
  by (intro ext, subst rel_inv_iff_rel) fast

(*TODO: could be generalised to more general relations and non-set functions*)
(* lemma lifting_triple_Iso_Rel_if_bijection:
  assumes bij: "bijection A B f g"
  shows "lifting_triple (Iso_Rel A f) f g"
proof (rule lifting_tripleI)
  {
    fix A f x assume "in_dom (Iso_Rel A f) x"
    then show "Iso_Rel A f x (f x)"
      by (blast intro: Iso_RelI dest: mem_if_in_dom_Iso_Rel)
  }
  note Iso_Rel_app_self = this
  fix y assume "in_codom (Iso_Rel A f) y"
  then have "in_dom (rel_inv (Iso_Rel A f)) y" by (subst in_dom_rel_inv_iff_in_codom)
  then have "in_dom (Iso_Rel B g) y"
    using bij by (simp only: rel_inv_Iso_Rel_eq_Iso_Rel_if_bijection)
  then have "(Iso_Rel B g) y (g y)" by (intro Iso_Rel_app_self)
  then have "rel_inv (Iso_Rel B g) (g y) y" by (rule rel_invI)
  then show "(Iso_Rel A f) (g y) y"
    using bijection_if_bijection[OF bij]
    by (simp only: rel_inv_Iso_Rel_eq_Iso_Rel_if_bijection)
qed (fact lifting_relation_Iso_Rel)
 *)

definition "Eq_Rel \<equiv> Fun_Rel id"

lemma Eq_Rel_eq_Fun_Rel_id: "Eq_Rel = Fun_Rel id"
  unfolding Eq_Rel_def ..

lemma Eq_RelI:
  assumes "x = y"
  shows "Eq_Rel x y"
  unfolding Eq_Rel_def using assms by (intro Fun_RelI) simp

lemma Eq_RelE:
  assumes "Eq_Rel x y"
  obtains "x = y"
  using assms unfolding Eq_Rel_def by (elim Fun_RelE) simp

corollary Eq_Rel_self: "Eq_Rel x x"
  by (rule Eq_RelI) simp

corollary reflexive_Eq_Rel: "reflexive Eq_Rel"
  by (rule reflexiveI) (fact Eq_Rel_self)

lemma symmetric_Eq_Rel: "symmetric Eq_Rel"
  by (rule symmetricI) (blast intro: Eq_RelI elim: Eq_RelE)

lemma transitive_Eq_Rel: "transitive Eq_Rel"
  by (rule transitiveI) (blast intro: Eq_RelI elim: Eq_RelE)

lemma partial_equivalence_Eq_Rel: "partial_equivalence Eq_Rel"
  using symmetric_Eq_Rel transitive_Eq_Rel
  by (rule partial_equivalenceI)

lemma injective_Eq_Rel: "rel_injective Eq_Rel"
  by (subst Eq_Rel_eq_Fun_Rel_id)
  (fact rel_injective_Fun_Rel_if_injective[OF injective_id])

(* lemma lifting_relation_Eq_Rel: "lifting_relation (Eq_Rel A)"
  by (subst Eq_Rel_eq_Iso_Rel) (rule lifting_relation_Iso_Rel)

lemma lifting_triple_Eq_Rel_id: "lifting_triple (Eq_Rel A) id id"
  using bijection_id
  by (subst Eq_Rel_eq_Iso_Rel) (intro lifting_triple_Iso_Rel_if_bijection) *)

(* lemma Eq_rep_Iso_Rel_eq_if_bijection:
  assumes biject: "bijection A B f g"
  shows "Eq_rep (Iso_Rel A f) = Eq_Rel A"
proof standard+
  fix x x' :: set
  {
    assume "x = x'"
    then have "Eq_rep (Iso_Rel A f) x x' \<longleftrightarrow> Eq_rep (Iso_Rel A f) x x" by simp
    also have "... \<longleftrightarrow> in_dom (Iso_Rel A f) x" by (rule Eq_rep_self_iff_in_dom)
    also have "... \<longleftrightarrow> x \<in> A" by (rule in_dom_Iso_Rel_iff_mem)
    also have "... \<longleftrightarrow> Eq_Rel A x x" by (rule Eq_Rel_iff_mem[symmetric])
    also have "... \<longleftrightarrow> Eq_Rel A x x'" by (simp only: \<open>x = x'\<close>)
    finally have 1: "Eq_rep (Iso_Rel A f) x x' \<longleftrightarrow> Eq_Rel A x x'" .
  }
  note 1 = this
  {
    have "injective (Iso_Rel A f)"
      using biject
      by (intro injective_Iso_Rel_if_injective_on injective_on_if_bijection)
    assume "Eq_rep (Iso_Rel A f) x x'"
    moreover then have "x = x'" using injectiveD[OF \<open>injective _\<close>] by (elim Eq_repE)
    ultimately show "Eq_Rel A x x'" using 1 by blast
  }
  assume "Eq_Rel A x x'"
  moreover then have "x = x'" using Eq_RelE by blast
  ultimately show "Eq_rep (Iso_Rel A f) x x'" using 1 by blast
qed *)


end