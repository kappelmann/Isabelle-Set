theory Binary_Relation_Isomorphism
  imports
    Binary_Relations_Strict_Linear_Order
    Transport.Functions_Bijection
begin

consts rel_isomorphism_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'c) \<Rightarrow> bool"

definition rel_isomorphism_on_pred :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 
  ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where 
"rel_isomorphism_on_pred A B R S \<phi> \<psi> 
  \<longleftrightarrow> bijection_on A B \<phi> \<psi> \<and> (\<forall>x y : A. S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y)"
adhoc_overloading rel_isomorphism_on rel_isomorphism_on_pred

lemma rel_isomorphism_onI:
  assumes "bijection_on A B \<phi> \<psi>" "\<And>x y. A x \<Longrightarrow> A y \<Longrightarrow> S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y"
  shows "rel_isomorphism_on A B R S \<phi> \<psi>"
  using assms unfolding rel_isomorphism_on_pred_def rel_map_def rel_bimap_def by blast

lemma rel_isomorphism_onI':
  assumes bij: "bijection_on A B \<phi> \<psi>"
  assumes hom_\<phi>: "\<And>x y. R\<restriction>\<^bsub>A\<^esub>\<upharpoonleft>\<^bsub>A\<^esub> x y \<Longrightarrow> S (\<phi> x) (\<phi> y)"
  assumes hom_\<psi>: "\<And>x y. S\<restriction>\<^bsub>B\<^esub>\<upharpoonleft>\<^bsub>B\<^esub> x y \<Longrightarrow> R (\<psi> x) (\<psi> y)"
  shows "rel_isomorphism_on A B R S \<phi> \<psi>"
proof -
  have "R x y" if "A x" "A y" "S (\<phi> x) (\<phi> y)" for x y
  proof -
    have "R (\<psi> (\<phi> x)) (\<psi> (\<phi> y))" using that hom_\<psi> bij mono_wrt_pred_if_bijection_on_left by blast
    then show ?thesis 
      using \<open>A x\<close> \<open>A y\<close> bij inverse_on_if_bijection_on_left_right by (force dest!: inverse_onD)
  qed
  then have "S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y" if "A x" "A y" for x y using that hom_\<phi> by fast
  then show ?thesis using bij by (auto intro: rel_isomorphism_onI)
qed

lemma bijection_on_if_rel_isomorphism_onD [dest]:
  assumes "rel_isomorphism_on A B R S \<phi> \<psi>"
  shows "bijection_on A B \<phi> \<psi>"
  using assms unfolding rel_isomorphism_on_pred_def by blast

lemma rel_iff_rel_if_rel_isomorphism_onD [dest]:
  assumes "rel_isomorphism_on A B R S \<phi> \<psi>" "A x" "A y"
  shows "S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y"
  using assms unfolding rel_isomorphism_on_pred_def by blast

lemma rel_iff_rel_if_rel_isomorphism_onD' [dest]:
  assumes iso: "rel_isomorphism_on A B R S \<phi> \<psi>" and "B x" "B y"
  shows "R (\<psi> x) (\<psi> y) \<longleftrightarrow> S x y"
proof -
  have "A (\<psi> x)" "A (\<psi> y)" using assms mono_wrt_pred_if_bijection_on_right by auto
  then have "R (\<psi> x) (\<psi> y) \<longleftrightarrow> S (\<phi> (\<psi> x)) (\<phi> (\<psi> y))" using iso by auto
  moreover have "\<phi> (\<psi> x) = x" "\<phi> (\<psi> y) = y" 
    using assms inverse_on_if_bijection_on_right_left by (auto dest!: inverse_onD)
  ultimately show ?thesis by auto
qed

lemma rel_isomorphism_on_if_connected_if_asymmetricI:
  assumes bij: "bijection_on A B \<phi> \<psi>"
  assumes connected: "connected_on A R" and asymmetric: "asymmetric_on B S"
  assumes homomorphism: "\<And>x y. R\<restriction>\<^bsub>A\<^esub>\<upharpoonleft>\<^bsub>A\<^esub> x y \<Longrightarrow> S (\<phi> x) (\<phi> y)"
  shows "rel_isomorphism_on A B R S \<phi> \<psi>"
proof -
  have "R x y" if "A x" "A y" "S (\<phi> x) (\<phi> y)" for x y
  proof (rule ccontr)
    assume "\<not> R x y"
    then consider (eq) "x = y" | (rev) "R y x" using \<open>A x\<close> \<open>A y\<close> connected by blast
    then show "False"
    proof cases
      case eq
      then show "False" 
        using \<open>S (\<phi> x) (\<phi> y)\<close> \<open>A x\<close> asymmetric bij mono_wrt_pred_if_bijection_on_left by blast
    next
      case rev
      then have "S (\<phi> y) (\<phi> x)" using that homomorphism by blast
      then show "False" using that asymmetric bij mono_wrt_pred_if_bijection_on_left by blast
    qed
  qed
  then have "S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y" if "A x" "A y" for x y using that homomorphism by blast
  then show ?thesis using bij by (blast intro: rel_isomorphism_onI)
qed

lemma rel_isomorphism_on_inverse:
  assumes "rel_isomorphism_on A B R S \<phi> \<psi>" 
  shows "rel_isomorphism_on B A S R \<psi> \<phi>"
  using assms by (blast intro: rel_isomorphism_onI)

lemma rel_isomorphism_on_compI:
  assumes iso1: "rel_isomorphism_on A B R S \<phi>\<^sub>1 \<psi>\<^sub>1"
  assumes iso2: "rel_isomorphism_on B C S T \<phi>\<^sub>2 \<psi>\<^sub>2"
  shows "rel_isomorphism_on A C R T (\<phi>\<^sub>2 \<circ> \<phi>\<^sub>1) (\<psi>\<^sub>1 \<circ> \<psi>\<^sub>2)"
proof -
  have "T ((\<phi>\<^sub>2 \<circ> \<phi>\<^sub>1) x) ((\<phi>\<^sub>2 \<circ> \<phi>\<^sub>1) y) \<longleftrightarrow> R x y" if "A x" "A y" for x y
  proof -
    have "T (\<phi>\<^sub>2 (\<phi>\<^sub>1 x)) (\<phi>\<^sub>2 (\<phi>\<^sub>1 y)) \<longleftrightarrow> S (\<phi>\<^sub>1 x) (\<phi>\<^sub>1 y)"
      using that assms mono_wrt_pred_if_bijection_on_left by blast
    also have "S (\<phi>\<^sub>1 x) (\<phi>\<^sub>1 y) \<longleftrightarrow> R x y" using that iso1 by blast
    finally show ?thesis by simp
  qed
  moreover have "bijection_on A C (\<phi>\<^sub>2 \<circ> \<phi>\<^sub>1) (\<psi>\<^sub>1 \<circ> \<psi>\<^sub>2)" 
    using assms by (force intro: bijection_on_compI)
  ultimately show ?thesis by (auto intro: rel_isomorphism_onI)
qed

lemma rel_isomorphism_on_id: "rel_isomorphism_on D D R R id id"
  using bijection_on_self_id by (auto intro!: rel_isomorphism_onI)


consts rel_isomorphic_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool"

definition rel_isomorphic_on_pred :: 
  "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where 
"rel_isomorphic_on_pred A B R S \<longleftrightarrow> (\<exists>\<phi> \<psi>. rel_isomorphism_on A B R S \<phi> \<psi>)"
adhoc_overloading rel_isomorphic_on rel_isomorphic_on_pred

lemma rel_isomorphic_onI [intro]:
  assumes "rel_isomorphism_on A B R S \<phi> \<psi>"
  shows "rel_isomorphic_on A B R S"
  using assms unfolding rel_isomorphic_on_pred_def by blast

lemma rel_isomorphic_onE [elim]:
  assumes "rel_isomorphic_on A B R S"
  obtains \<phi> \<psi> where "rel_isomorphism_on A B R S \<phi> \<psi>"
  using assms unfolding rel_isomorphic_on_pred_def by blast

lemma rel_isomorphic_on_if_rel_isomorphic_on:
  assumes "rel_isomorphic_on A B R S"
  shows "rel_isomorphic_on B A S R"
  using assms rel_isomorphism_on_inverse by (blast elim!: rel_isomorphic_onE)

lemma rel_isomorphic_on_trans [intro]:
  assumes "rel_isomorphic_on A B R S" "rel_isomorphic_on B C S T"
  shows "rel_isomorphic_on A C R T"
  using assms by (blast intro: rel_isomorphism_on_compI elim!: rel_isomorphic_onE)

lemma rel_isomorphic_on_self: "rel_isomorphic_on D D R R"
  using rel_isomorphism_on_id by blast

end