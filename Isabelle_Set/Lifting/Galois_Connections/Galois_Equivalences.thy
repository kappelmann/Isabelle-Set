subsection \<open>Galois Equivalences\<close>
theory Galois_Equivalences
  imports
    Galois_Connections_Base
begin

definition "galois_equivalence_left L l r \<equiv> \<forall>x. in_dom L x \<longrightarrow> L (r (l x)) x"

lemma galois_equivalence_leftI:
  assumes "\<And>x. in_dom L x \<Longrightarrow> L (r (l x)) x"
  shows "galois_equivalence_left L l r"
  unfolding galois_equivalence_left_def using assms by blast

lemma galois_equivalence_leftE:
  assumes "galois_equivalence_left L l r"
  and "in_dom L x"
  obtains "L (r (l x)) x"
  using assms unfolding galois_equivalence_left_def by blast

lemma galois_equivalence_leftD:
  assumes "galois_equivalence_left L l r"
  and "in_dom L x"
  shows "L (r (l x)) x"
  using assms by (elim galois_equivalence_leftE)

definition "galois_equivalence_right R l r \<equiv> \<forall>y. in_codom R y \<longrightarrow> R y (l (r y))"

lemma galois_equivalence_rightI:
  assumes "\<And>y. in_codom R y \<Longrightarrow> R y (l (r y))"
  shows "galois_equivalence_right R l r"
  unfolding galois_equivalence_right_def using assms by blast

lemma galois_equivalence_rightE:
  assumes "galois_equivalence_right R l r"
  and "in_codom R y"
  obtains "R y (l (r y))"
  using assms unfolding galois_equivalence_right_def by blast

lemma galois_equivalence_rightD:
  assumes "galois_equivalence_right R l r"
  and "in_codom R y"
  shows "R y (l (r y))"
  using assms by (elim galois_equivalence_rightE)

lemma galois_equivalence_left_if_galois_equivalence_right_rel_inv:
  assumes "galois_equivalence_right (rel_inv L) r l"
  shows "galois_equivalence_left L l r"
  using assms
  by (intro galois_equivalence_leftI)
  (fastforce dest: galois_equivalence_rightD iff: in_codom_rel_inv_iff_in_dom rel_inv_iff_rel)

lemma galois_equivalence_right_if_galois_equivalence_left_rel_inv:
  assumes "galois_equivalence_left (rel_inv R) l r"
  shows "galois_equivalence_right R r l"
proof (rule galois_equivalence_rightI)
  fix y assume "in_codom R y"
  then have "in_dom (rel_inv R) y"
    by (simp only: in_codom_rel_inv_iff_in_dom[symmetric] rel_inv_rel_inv_eq_self)
  with assms show "R y (r (l y))"
    by (fastforce elim: galois_equivalence_leftE iff: rel_inv_iff_rel )
qed

corollary galois_equivalence_right_rel_inv_iff_galois_equivalence_left:
  "galois_equivalence_right (rel_inv L) r l \<longleftrightarrow> galois_equivalence_left L l r"
proof -
  have "galois_equivalence_right (rel_inv L) r l \<longleftrightarrow>
    galois_equivalence_right (rel_inv (rel_inv (rel_inv L))) r l"
    by (simp only: rel_inv_rel_inv_eq_self)
  also have "... \<longleftrightarrow> galois_equivalence_left (rel_inv (rel_inv L)) l r"
    using galois_equivalence_left_if_galois_equivalence_right_rel_inv
      galois_equivalence_right_if_galois_equivalence_left_rel_inv
    by (fastforce simp only: rel_inv_rel_inv_eq_self)
  also have "... \<longleftrightarrow> galois_equivalence_left L l r"
    by (simp only: rel_inv_rel_inv_eq_self)
  finally show ?thesis .
qed

corollary galois_equivalence_left_rel_inv_iff_galois_equivalence_right:
  "galois_equivalence_left (rel_inv R) l r \<longleftrightarrow> galois_equivalence_right R r l"
  by (simp only: galois_equivalence_right_rel_inv_iff_galois_equivalence_left[symmetric]
    rel_inv_rel_inv_eq_self)

definition "galois_equivalence L R l r \<equiv>
  galois_connection L R l r \<and>
  galois_equivalence_left L l r \<and>
  galois_equivalence_right R l r"

lemma galois_equivalenceI:
  assumes "galois_connection L R l r"
  and "galois_equivalence_left L l r"
  and "galois_equivalence_right R l r"
  shows "galois_equivalence L R l r"
  unfolding galois_equivalence_def using assms by blast

lemma galois_equivalenceE:
  assumes "galois_equivalence L R l r"
  obtains "galois_connection L R l r" "galois_equivalence_left L l r"
    "galois_equivalence_right R l r"
  using assms unfolding galois_equivalence_def by blast

lemma galois_connection_if_galois_equivalence:
  assumes "galois_equivalence L R l r"
  shows "galois_connection L R l r"
  using assms by (elim galois_equivalenceE)

lemma galois_equivalence_left_if_galois_equivalence:
  assumes "galois_equivalence L R l r"
  shows "galois_equivalence_left L l r"
  using assms by (elim galois_equivalenceE)

lemma galois_equivalence_right_if_galois_equivalence:
  assumes "galois_equivalence L R l r"
  shows "galois_equivalence_right R l r"
  using assms by (elim galois_equivalenceE)

lemma galois_equivalence_left_rel_right_left_self_if_in_dom:
  assumes "galois_equivalence L R l r"
  and "in_dom L x"
  shows "L (r (l x)) x"
  using assms
  by (blast dest: galois_equivalence_left_if_galois_equivalence galois_equivalence_leftD)

lemma galois_equivalence_right_rel_left_right_self_if_in_codom:
  assumes "galois_equivalence L R l r"
  and "in_codom R y"
  shows "R y (l (r y))"
  using assms
  by (blast dest: galois_equivalence_right_if_galois_equivalence galois_equivalence_rightD)

lemma galois_equivalence_dual:
  assumes "galois_equivalence L R l r"
  shows "galois_equivalence (rel_inv R) (rel_inv L) r l"
  using assms by (intro galois_equivalenceI) (auto
    intro: galois_connection_dual galois_equivalence_right_if_galois_equivalence
      galois_equivalence_left_if_galois_equivalence
    simp only: rel_inv_iff_rel galois_connection_if_galois_equivalence
      galois_equivalence_right_rel_inv_iff_galois_equivalence_left
      galois_equivalence_left_rel_inv_iff_galois_equivalence_right)


end