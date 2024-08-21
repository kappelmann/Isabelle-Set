theory Binary_Relation_Isomorphism
  imports
    Binary_Relations_Strict_Linear_Order
    Transport.Functions_Bijection
begin

definition "rel_isomorphism A B R S \<phi> \<psi> 
  \<longleftrightarrow> bijection_on A B \<phi> \<psi> \<and> (\<forall>x y : A. S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y)"

lemma rel_isomorphismI:
  assumes "bijection_on A B \<phi> \<psi>" "\<And>x y. A x \<Longrightarrow> A y \<Longrightarrow> S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y"
  shows "rel_isomorphism A B R S \<phi> \<psi>"
  using assms unfolding rel_isomorphism_def rel_map_def rel_bimap_def by blast

lemma bijection_on_if_rel_isomorphismE [dest]:
  assumes "rel_isomorphism A B R S \<phi> \<psi>"
  shows "bijection_on A B \<phi> \<psi>"
  using assms unfolding rel_isomorphism_def by blast

lemma rel_iff_rel_if_rel_isomorphismD [dest]:
  assumes "rel_isomorphism A B R S \<phi> \<psi>" "A x" "A y"
  shows "S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y"
  using assms unfolding rel_isomorphism_def by blast

lemma rel_iff_rel_if_rel_isomorphismD' [dest]:
  assumes iso: "rel_isomorphism A B R S \<phi> \<psi>" and "B x" "B y"
  shows "R (\<psi> x) (\<psi> y) \<longleftrightarrow> S x y"
proof -
  have "A (\<psi> x)" "A (\<psi> y)" using assms mono_wrt_pred_if_bijection_on_right by auto
  then have "R (\<psi> x) (\<psi> y) \<longleftrightarrow> S (\<phi> (\<psi> x)) (\<phi> (\<psi> y))" using iso by auto
  moreover have "\<phi> (\<psi> x) = x" "\<phi> (\<psi> y) = y" 
    using assms inverse_on_if_bijection_on_right_left by (auto dest!: inverse_onD)
  ultimately show ?thesis by auto
qed

lemma rel_isomorphism_if_strict_linear_order_onI:
  assumes bij: "bijection_on A B \<phi> \<psi>"
  assumes order_R: "strict_linear_order_on A R" and order_S: "strict_linear_order_on B S"
  assumes homomorphism: "\<And>x y. A x \<Longrightarrow> A y \<Longrightarrow> R x y \<Longrightarrow> S (\<phi> x) (\<phi> y)"
  shows "rel_isomorphism A B R S \<phi> \<psi>"
proof -
  have "R x y" if "A x" "A y" "S (\<phi> x) (\<phi> y)" for x y
  proof (rule ccontr)
    assume "\<not> R x y"
    then consider (eq) "x = y" | (R_y_x) "R y x" using \<open>A x\<close> \<open>A y\<close> order_R by blast
    then show "False"
    proof cases
      case eq
      then show "False" 
        using \<open>S (\<phi> x) (\<phi> y)\<close> \<open>A x\<close> order_S bij mono_wrt_pred_if_bijection_on_left by blast
    next
      case R_y_x
      then have "S (\<phi> y) (\<phi> x)" using that homomorphism by blast
      then show "False" using that order_S bij mono_wrt_pred_if_bijection_on_left by blast
    qed
  qed
  then have "S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y" if "A x" "A y" for x y using that homomorphism by blast
  then show ?thesis using bij by (blast intro: rel_isomorphismI)
qed

lemma rel_isomorphism_inverse:
  assumes "rel_isomorphism A B R S \<phi> \<psi>" 
  shows "rel_isomorphism B A S R \<psi> \<phi>"
  using assms by (blast intro: rel_isomorphismI)

lemma rel_isomorphism_compI:
  assumes iso1: "rel_isomorphism A B R S \<phi>\<^sub>1 \<psi>\<^sub>1"
  assumes iso2: "rel_isomorphism B C S T \<phi>\<^sub>2 \<psi>\<^sub>2"
  shows "rel_isomorphism A C R T (\<phi>\<^sub>2 \<circ> \<phi>\<^sub>1) (\<psi>\<^sub>1 \<circ> \<psi>\<^sub>2)"
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
  ultimately show ?thesis by (auto intro: rel_isomorphismI)
qed

lemma rel_isomorphism_id: "rel_isomorphism D D R R id id"
  using bijection_on_self_id by (auto intro!: rel_isomorphismI)

definition "rel_isomorphic A B R S \<longleftrightarrow> (\<exists>\<phi> \<psi>. rel_isomorphism A B R S \<phi> \<psi>)"

lemma rel_isomorphicI [intro]:
  assumes "rel_isomorphism A B R S \<phi> \<psi>"
  shows "rel_isomorphic A B R S"
  using assms unfolding rel_isomorphic_def by blast

lemma rel_isomorphicE [elim]:
  assumes "rel_isomorphic A B R S"
  obtains \<phi> \<psi> where "rel_isomorphism A B R S \<phi> \<psi>"
  using assms unfolding rel_isomorphic_def by blast

lemma rel_isomorphic_if_rel_isomorphic:
  assumes "rel_isomorphic A B R S"
  shows "rel_isomorphic B A S R"
  using assms rel_isomorphism_inverse by (blast elim!: rel_isomorphicE)

lemma rel_isomorphic_trans [intro]:
  assumes "rel_isomorphic A B R S" "rel_isomorphic B C S T"
  shows "rel_isomorphic A C R T"
  using assms by (blast intro: rel_isomorphism_compI elim!: rel_isomorphicE)

lemma rel_isomorphic_self: "rel_isomorphic D D R R"
  using rel_isomorphism_id by blast

end