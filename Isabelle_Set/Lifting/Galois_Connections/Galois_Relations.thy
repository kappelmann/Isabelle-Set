subsection \<open>Relations Using Galois Connections\<close>
theory Galois_Relations
  imports
    Galois_Connections_Base
begin

definition "(Galois L R r) x y \<equiv> in_codom R y \<and> L x (r y)"

lemma GaloisI:
  assumes "in_codom R y"
  and "L x (r y)"
  shows "(Galois L R r) x y"
  unfolding Galois_def using assms by blast

lemma GaloisE:
  assumes "(Galois L R r) x y"
  obtains "in_codom R y" "L x (r y)"
  using assms unfolding Galois_def by blast

lemma Galois_in_codom:
  assumes "(Galois L R r) x y"
  shows "in_codom R y"
  using assms by (elim GaloisE)

lemma Galois_left_rel_right:
  assumes "(Galois L R r) x y"
  shows "L x (r y)"
  using assms by (elim GaloisE)

corollary Galois_in_dom:
  assumes "(Galois L R r) x y"
  shows "in_dom L x"
  using assms by (intro in_domI) (drule Galois_left_rel_right)

corollary Galois_iff_in_codom_and_left_rel_right:
  "(Galois L R r) x y \<longleftrightarrow> in_codom R y \<and> L x (r y)"
  by (blast intro: GaloisI elim: GaloisE)

lemma galois_property_Galois_if_right_rel_left_if_in_dom:
  assumes "galois_property L R l r"
  and "in_dom L x"
  and "R (l x) y"
  shows "(Galois L R r) x y"
  using assms
  by (intro GaloisI)
    (blast intro: in_codomI galois_property_left_rel_right_if_right_rel_left)+

lemma galois_property_Galois_iff_in_dom_and_right_rel_left:
  assumes "galois_property L R l r"
  shows "(Galois L R r) x y \<longleftrightarrow> in_dom L x \<and> R (l x) y"
  using assms
    galois_property_Galois_if_right_rel_left_if_in_dom
    galois_property_right_rel_left_if_left_rel_right
  by (fastforce elim: GaloisE intro: Galois_in_dom)

corollary galois_property_GaloisE:
  assumes "galois_property L R l r"
  and "(Galois L R r) x y"
  obtains "in_dom L x" "R (l x) y"
  using assms galois_property_Galois_iff_in_dom_and_right_rel_left
  by fastforce

corollary galois_property_right_rel_left_if_Galois:
  assumes "galois_property L R l r"
  and "(Galois L R r) x y"
  shows "R (l x) y"
  using assms by (elim galois_property_GaloisE)

lemma galois_property_rel_inv_Galois_rel_inv_eq_Galois:
  assumes "galois_property L R l r"
  shows "rel_inv (Galois (rel_inv R) (rel_inv L) l) = Galois L R r"
proof (intro ext)
  fix x y
  have "rel_inv (Galois (rel_inv R) (rel_inv L) l) x y
    \<longleftrightarrow> (Galois (rel_inv R) (rel_inv L) l) y x"
    by (simp only: rel_inv_iff_rel)
  also have "... \<longleftrightarrow> in_codom (rel_inv L) x \<and> (rel_inv R) y (l x)"
    by (fact Galois_iff_in_codom_and_left_rel_right)
  also have "... \<longleftrightarrow> in_dom L x \<and> R (l x) y"
    by (simp only: rel_inv_iff_rel in_codom_rel_inv_iff_in_dom)
  also from assms have "... \<longleftrightarrow> (Galois L R r) x y"
    by (fact galois_property_Galois_iff_in_dom_and_right_rel_left[symmetric])
  finally show "rel_inv (Galois (rel_inv R) (rel_inv L) l) x y
    \<longleftrightarrow> (Galois L R r) x y" .
qed

corollary galois_property_rel_inv_Galois_eq_Galois_Rel_rel_inv:
  assumes "galois_property L R l r"
  shows "rel_inv (Galois L R r) = Galois (rel_inv R) (rel_inv L) l"
proof -
  from assms have "galois_property (rel_inv R) (rel_inv L) r l"
    by (rule galois_property_dual)
  from galois_property_rel_inv_Galois_rel_inv_eq_Galois[OF this] show ?thesis
    by (simp only: rel_inv_rel_inv_eq_self)
qed

lemma galois_connection_Galois_left_if_left_rel:
  assumes "galois_connection L R l r"
  and "L x x'"
  shows "(Galois L R r) x (l x')"
  using assms by (intro GaloisI)
    (blast intro: in_codomI galois_connection_right_rel_left_left_if_left_rel
      galois_connection_left_rel_right_left_if_left_rel)+

lemma galois_connection_Galois_right_if_right_rel:
  assumes galois_conn: "galois_connection L R l r"
  and "R y y'"
  shows "(Galois L R r) (r y) y'"
proof (rule galois_property_Galois_if_right_rel_left_if_in_dom)
  from assms have "L (r y) (r y')"
    by (rule galois_connection_left_rel_right_right_if_right_rel)
  then show "in_dom L (r y)" by (rule in_domI)
  from assms show "R (l (r y)) y'"
    by (rule galois_connection_right_rel_left_right_if_right_rel)
  from galois_conn show "galois_property L R l r"
    by (rule galois_property_if_galois_connection)
qed

definition "(Galois_Inv_Right L R l) y x \<equiv> in_dom L x \<and> R y (l x)"

lemma Galois_Inv_RightI:
  assumes "in_dom L x"
  and "R y (l x)"
  shows "(Galois_Inv_Right L R l) y x"
  unfolding Galois_Inv_Right_def using assms by blast

lemma Galois_Inv_RightE:
  assumes "(Galois_Inv_Right L R l) y x"
  obtains "in_dom L x" "R y (l x)"
  using assms unfolding Galois_Inv_Right_def by blast

lemma Galois_Inv_Right_in_dom:
  assumes "(Galois_Inv_Right L R l) y x"
  shows "in_dom L x"
  using assms by (elim Galois_Inv_RightE)

lemma Galois_Inv_Right_right_rel_left:
  assumes "(Galois_Inv_Right L R l) y x"
  shows "R y (l x)"
  using assms by (elim Galois_Inv_RightE)

lemma Galois_rel_inv_eq_Galois_Inv_Right:
  "Galois R (rel_inv L) l = Galois_Inv_Right L R l"
  by (intro ext) (fastforce
    iff: Galois_iff_in_codom_and_left_rel_right in_codom_rel_inv_iff_in_dom
    intro: Galois_Inv_RightI elim: Galois_Inv_RightE)

lemma galois_property_rel_inv_Galois_eq_Galois_Inv_Right_rel_inv:
  assumes "galois_property L R l r"
  shows "rel_inv (Galois L R r) = Galois_Inv_Right L (rel_inv R) l"
proof -
  from assms have "rel_inv (Galois L R r) = Galois (rel_inv R) (rel_inv L) l"
    by (rule galois_property_rel_inv_Galois_eq_Galois_Rel_rel_inv)
  also have "... = Galois_Inv_Right L (rel_inv R) l"
    by (simp only: Galois_rel_inv_eq_Galois_Inv_Right)
  finally show "?thesis" .
qed

definition "(Galois_Inv_Left L R r) y x \<equiv> in_codom R y \<and> L (r y) x"

lemma Galois_Inv_LeftI:
  assumes "in_codom R y"
  and "L (r y) x"
  shows "(Galois_Inv_Left L R r) y x"
  unfolding Galois_Inv_Left_def using assms by blast

lemma Galois_Inv_LeftE:
  assumes "(Galois_Inv_Left L R r) y x"
  obtains "in_codom R y" "L (r y) x"
  using assms unfolding Galois_Inv_Left_def by blast

lemma Galois_Inv_Left_in_codom:
  assumes "(Galois_Inv_Left L R r) y x"
  shows "in_codom R y"
  using assms by (elim Galois_Inv_LeftE)

lemma Galois_Inv_Left_left_rel_right:
  assumes "(Galois_Inv_Left L R r) y x"
  shows "L (r y) x"
  using assms by (elim Galois_Inv_LeftE)

lemma rel_inv_Galois_rel_inv_eq_Galois_Inv_Left:
  "rel_inv (Galois (rel_inv L) R r) = Galois_Inv_Left L R r"
  by (intro ext) (fastforce
    iff: Galois_iff_in_codom_and_left_rel_right rel_inv_iff_rel
    intro: Galois_Inv_LeftI elim: Galois_Inv_LeftE)

lemma galois_property_Galois_Inv_Left_rel_inv_eq_Galois:
  assumes "galois_property L R l r"
  shows "Galois_Inv_Left R (rel_inv L) l = Galois L R r"
proof -
  have "Galois_Inv_Left R (rel_inv L) l = rel_inv (Galois (rel_inv R) (rel_inv L) l)"
    by (simp only: rel_inv_Galois_rel_inv_eq_Galois_Inv_Left)
  also from assms have "... = Galois L R r "
    by (rule galois_property_rel_inv_Galois_rel_inv_eq_Galois)
  finally show "?thesis" .
qed

lemma rel_inv_Galois_Inv_Right_rel_inv_eq_Galois_Inv_Left:
  "rel_inv (Galois_Inv_Right (rel_inv R) (rel_inv L) r) = Galois_Inv_Left L R r"
proof -
  have "rel_inv (Galois_Inv_Right (rel_inv R) (rel_inv L) r) =
    rel_inv (Galois (rel_inv L) (rel_inv (rel_inv R)) r)"
    by (simp only: Galois_rel_inv_eq_Galois_Inv_Right)
  also have "... = rel_inv (Galois (rel_inv L) R r)"
    by (simp only: rel_inv_rel_inv_eq_self)
  also have "... = Galois_Inv_Left L R r"
    by (simp only: rel_inv_Galois_rel_inv_eq_Galois_Inv_Left)
  finally show ?thesis .
qed

corollary rel_inv_Galois_Inv_Left_eq_Galois_Inv_Right_rel_inv:
  "rel_inv (Galois_Inv_Left L R r) = Galois_Inv_Right (rel_inv R) (rel_inv L) r"
proof -
  have "rel_inv (Galois_Inv_Left L R r)
    = rel_inv (rel_inv (Galois_Inv_Right (rel_inv R) (rel_inv L) r))"
    by (simp only: rel_inv_Galois_Inv_Right_rel_inv_eq_Galois_Inv_Left)
  also have "... = Galois_Inv_Right (rel_inv R) (rel_inv L) r"
    by (simp only: rel_inv_rel_inv_eq_self)
  finally show ?thesis .
qed

corollary rel_inv_Galois_Inv_Left_rel_inv_eq_Galois_Inv_Right:
  "rel_inv (Galois_Inv_Left (rel_inv R) (rel_inv L) l) = Galois_Inv_Right L R l"
  by (simp only: rel_inv_Galois_Inv_Left_eq_Galois_Inv_Right_rel_inv
    rel_inv_rel_inv_eq_self)

definition "Galois_Comp_Left L1 R1 l1 r1 L2 \<equiv>
  Galois L1 R1 r1 \<circ>\<circ> L2 \<circ>\<circ> Galois_Inv_Right L1 R1 l1"

lemma Galois_Comp_LeftI:
  assumes "(Galois L1 R1 r1) x y"
  and "L2 y y'"
  and "(Galois_Inv_Right L1 R1 l1) y' x'"
  shows "(Galois_Comp_Left L1 R1 l1 r1 L2) x x'"
  unfolding Galois_Comp_Left_def using assms by (intro rel_compI)

lemma Galois_Comp_LeftE:
  assumes "(Galois_Comp_Left L1 R1 l1 r1 L2) x x'"
  obtains y y' where
    "(Galois L1 R1 r1) x y" "L2 y y'" "(Galois_Inv_Right L1 R1 l1) y' x'"
  using assms unfolding Galois_Comp_Left_def by (elim rel_compE)

definition "Galois_Comp_Right R1 L2 R2 r2 \<equiv>
  Galois_Inv_Left L2 R2 r2 \<circ>\<circ> R1 \<circ>\<circ> Galois L2 R2 r2"

lemma Galois_Comp_RightI:
  assumes "(Galois_Inv_Left L2 R2 r2) z y"
  and "R1 y y'"
  and "(Galois L2 R2 r2) y' z'"
  shows "(Galois_Comp_Right R1 L2 R2 r2) z z'"
  unfolding Galois_Comp_Right_def using assms by (intro rel_compI)

lemma Galois_Comp_RightE:
  assumes "(Galois_Comp_Right R1 L2 R2 r2) z z'"
  obtains y y' where
    "(Galois_Inv_Left L2 R2 r2) z y" "R1 y y'" "(Galois L2 R2 r2) y' z'"
  using assms unfolding Galois_Comp_Right_def by (elim rel_compE)

lemma galois_property_rel_inv_Galois_Comp_Left_eq_Galois_Comp_Right_rel_inv:
  assumes "galois_property L1 R1 l1 r1"
  shows "rel_inv (Galois_Comp_Left L1 R1 l1 r1 L2)
    = Galois_Comp_Right (rel_inv L2) (rel_inv R1) (rel_inv L1) l1"
proof -
  let ?L = "rel_inv (Galois_Inv_Right L1 R1 l1)" and ?M = "rel_inv L2"
  and ?R = "rel_inv (Galois L1 R1 r1)"
  have "rel_inv (Galois_Comp_Left L1 R1 l1 r1 L2)
    =  ?L \<circ>\<circ> ?M \<circ>\<circ> ?R"
    unfolding Galois_Comp_Left_def by (simp only: rel_inv_comp_eq rel_comp_assoc)
  also have "... = rel_inv (rel_inv (Galois_Inv_Left (rel_inv R1) (rel_inv L1) l1)) \<circ>\<circ> ?M \<circ>\<circ> ?R"
    by (simp only: rel_inv_Galois_Inv_Left_rel_inv_eq_Galois_Inv_Right)
  also have "... = Galois_Inv_Left (rel_inv R1) (rel_inv L1) l1 \<circ>\<circ> ?M \<circ>\<circ> ?R"
    by (simp only: rel_inv_rel_inv_eq_self)
  also from assms have "...
    = Galois_Inv_Left (rel_inv R1) (rel_inv L1) l1 \<circ>\<circ> ?M \<circ>\<circ> Galois (rel_inv R1) (rel_inv L1) l1"
    by (simp only: galois_property_rel_inv_Galois_eq_Galois_Rel_rel_inv)
  also have "... = Galois_Comp_Right (rel_inv L2) (rel_inv R1) (rel_inv L1) l1"
    unfolding Galois_Comp_Right_def ..
  finally show ?thesis .
qed

corollary galois_property_rel_inv_Galois_Comp_Right_eq_Galois_Comp_Left_rel_inv:
  assumes "galois_property L2 R2 l2 r2"
  shows "rel_inv (Galois_Comp_Right R1 L2 R2 r2)
    = Galois_Comp_Left (rel_inv R2) (rel_inv L2) r2 l2 (rel_inv R1)"
proof -
  from assms have "galois_property (rel_inv R2) (rel_inv L2) r2 l2"
    by (rule galois_property_dual)
  then have
    "rel_inv (Galois_Comp_Right (rel_inv (rel_inv R1)) (rel_inv (rel_inv L2)) (rel_inv (rel_inv R2)) r2)
      = rel_inv (rel_inv (Galois_Comp_Left (rel_inv R2) (rel_inv L2) r2 l2 (rel_inv R1)))"
    by (simp only: galois_property_rel_inv_Galois_Comp_Left_eq_Galois_Comp_Right_rel_inv)
  also have "... = Galois_Comp_Left (rel_inv R2) (rel_inv L2) r2 l2 (rel_inv R1)"
    by (simp only: rel_inv_rel_inv_eq_self)
  finally show ?thesis by (simp only: rel_inv_rel_inv_eq_self)
qed


end