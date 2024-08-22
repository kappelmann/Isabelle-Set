theory Binary_Relation_Isomorphism
  imports
    Binary_Relations_Strict_Linear_Order
    Transport.Functions_Bijection
begin

consts rel_isomorphism :: "'a \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'c) \<Rightarrow> bool"

overloading
  rel_isomorphism_pred \<equiv> "rel_isomorphism :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 
    ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "rel_isomorphism_pred (A :: 'a \<Rightarrow> bool) (B :: 'b \<Rightarrow> bool) 
    (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (S :: 'b \<Rightarrow> 'b \<Rightarrow> bool) (\<phi> :: 'a \<Rightarrow> 'b) (\<psi> :: 'b \<Rightarrow> 'a) 
    \<equiv> bijection_on A B \<phi> \<psi> \<and> (\<forall>x y : A. S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y)"
end

lemma rel_isomorphismI:
  assumes "bijection_on A B \<phi> \<psi>" "\<And>x y. A x \<Longrightarrow> A y \<Longrightarrow> S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y"
  shows "rel_isomorphism A B R S \<phi> \<psi>"
  using assms unfolding rel_isomorphism_pred_def rel_map_def rel_bimap_def by blast

lemma bijection_on_if_rel_isomorphismE [dest]:
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool" 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and \<phi> :: "'a \<Rightarrow> 'b"
  assumes "rel_isomorphism A B R S \<phi> \<psi>"
  shows "bijection_on A B \<phi> \<psi>"
  using assms unfolding rel_isomorphism_pred_def by blast

lemma rel_iff_rel_if_rel_isomorphismD [dest]:
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool" 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and \<phi> :: "'a \<Rightarrow> 'b"
  assumes "rel_isomorphism A B R S \<phi> \<psi>" "A x" "A y"
  shows "S (\<phi> x) (\<phi> y) \<longleftrightarrow> R x y"
  using assms unfolding rel_isomorphism_pred_def by blast

lemma rel_iff_rel_if_rel_isomorphismD' [dest]:
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool" 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and \<phi> :: "'a \<Rightarrow> 'b"
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
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool" 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and \<phi> :: "'a \<Rightarrow> 'b"
  assumes "rel_isomorphism A B R S \<phi> \<psi>" 
  shows "rel_isomorphism B A S R \<psi> \<phi>"
  using assms by (blast intro: rel_isomorphismI)

lemma rel_isomorphism_compI:
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool" and C :: "'c \<Rightarrow> bool" 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and T :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  fixes \<phi>\<^sub>1 :: "'a \<Rightarrow> 'b" and \<phi>\<^sub>2 :: "'b \<Rightarrow> 'c"
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

lemma rel_isomorphism_id: 
  shows "rel_isomorphism (D :: 'a \<Rightarrow> bool) D (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) R (id :: 'a \<Rightarrow> 'a) id"
  using bijection_on_self_id by (auto intro!: rel_isomorphismI)


consts rel_isomorphic :: "'a \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool"

overloading
  rel_isomorphic_pred \<equiv> "rel_isomorphic :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 
    ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_isomorphic_pred 
    (A :: 'a \<Rightarrow> bool) (B :: 'b \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (S :: 'b \<Rightarrow> 'b \<Rightarrow> bool) 
    \<equiv> \<exists>\<phi> \<psi>. rel_isomorphism A B R S (\<phi> :: 'a \<Rightarrow> 'b) \<psi>"
end

lemma rel_isomorphicI [intro]:
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool" 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "rel_isomorphism A B R S (\<phi> :: 'a \<Rightarrow> 'b) \<psi>"
  shows "rel_isomorphic A B R S"
  using assms unfolding rel_isomorphic_pred_def by blast

lemma rel_isomorphicE [elim]:
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool" 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "rel_isomorphic A B R S"
  obtains \<phi> \<psi> where "rel_isomorphism A B R S (\<phi> :: 'a \<Rightarrow> 'b) \<psi>"
  using assms unfolding rel_isomorphic_pred_def by blast

lemma rel_isomorphic_if_rel_isomorphic:
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool" 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "rel_isomorphic A B R S"
  shows "rel_isomorphic B A S R"
  using assms rel_isomorphism_inverse by (blast elim!: rel_isomorphicE)

lemma rel_isomorphic_trans [intro]:
  fixes A :: "'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> bool" and C :: "'c \<Rightarrow> bool"
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and T :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  assumes "rel_isomorphic A B R S" "rel_isomorphic B C S T"
  shows "rel_isomorphic A C R T"
  using assms by (blast intro: rel_isomorphism_compI elim!: rel_isomorphicE)

lemma rel_isomorphic_self: "rel_isomorphic (D :: 'a \<Rightarrow> bool) D (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) R"
  using rel_isomorphism_id by blast

end