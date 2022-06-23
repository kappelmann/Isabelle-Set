subsection \<open>Lifting Triples\<close>
theory Lifting_Triples
  imports Lifting_Relations
begin

definition lifting_triple :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "lifting_triple R abs rep \<equiv>
    lifting_relation R \<and>
    \<comment> \<open>abs and rep respect the PERs of the domain and codomain\<close>
    (\<forall>x. in_dom R x \<longrightarrow> R x (abs x)) \<and>
    (\<forall>y. in_codom R y \<longrightarrow> R (rep y) y)"

lemma lifting_tripleI:
  assumes "lifting_relation R"
  and "\<And>x. in_dom R x \<Longrightarrow> R x (abs x)"
  and "\<And>y. in_codom R y \<Longrightarrow> R (rep y) y"
  shows "lifting_triple R abs rep"
  unfolding lifting_triple_def using assms by blast

lemma lifting_relation_if_lifting_triple:
  assumes "lifting_triple R abs rep"
  shows "lifting_relation R"
  using assms unfolding lifting_triple_def by blast

lemma z_property_if_lifting_triple:
  assumes "lifting_triple R abs rep"
  shows "z_property R"
  using assms lifting_relation_if_lifting_triple z_property_if_lifting_relation
  by blast

lemma lifting_triple_rel_abs_self_if_in_dom:
  assumes "lifting_triple R abs rep"
  and "in_dom R x"
  shows "R x (abs x)"
  using assms unfolding lifting_triple_def by blast

lemma lifting_triple_rel_rep_self_if_in_codom:
  assumes "lifting_triple R abs rep"
  and "in_codom R y"
  shows "R (rep y) y"
  using assms unfolding lifting_triple_def by blast

lemma lifting_triple_rel_inv_abs_if_in_codom_rel_inv:
  assumes "lifting_triple R abs rep"
  and "in_codom (rel_inv R) x"
  shows "rel_inv R (abs x) x"
  using assms lifting_triple_rel_abs_self_if_in_dom
    by (intro rel_invI) (fast dest!: iffD1[OF in_codom_rel_inv_iff_in_dom])

lemma lifting_triple_rel_inv_rep_if_in_dom_rel_inv:
  assumes "lifting_triple R abs rep"
  and "in_dom (rel_inv R) y"
  shows "rel_inv R y (rep y)"
  using assms lifting_triple_rel_rep_self_if_in_codom
    by (intro rel_invI) (fast dest!: iffD1[OF in_dom_rel_inv_iff_in_codom])

lemma lifting_triple_dual:
  assumes "lifting_triple R abs rep"
  shows "lifting_triple (rel_inv R) rep abs"
proof (intro lifting_tripleI lifting_relation_if_z_property)
  from assms show "z_property (rel_inv R)"
    by (intro z_property_rel_inv_if_z_property z_property_if_lifting_relation)
      (blast dest: lifting_relation_if_lifting_triple)
qed (blast intro!: lifting_triple_rel_inv_abs_if_in_codom_rel_inv
  lifting_triple_rel_inv_rep_if_in_dom_rel_inv assms)+

lemma lifting_triple_Eq_abs_abs_if_rel:
  assumes "lifting_triple R abs rep"
  and "R x y"
  shows "Eq_abs R (abs x) y"
  using assms
  by (intro Eq_absI) (blast intro: lifting_triple_rel_abs_self_if_in_dom in_domI)

lemma lifting_triple_Eq_rep_rep_if_rel:
  assumes "lifting_triple R abs rep"
  and "R x y"
  shows "Eq_rep R x (rep y)"
proof -
  from assms have "lifting_triple (rel_inv R) rep abs" "rel_inv R y x"
    by (blast intro: lifting_triple_dual rel_invI)+
  then have "Eq_abs (rel_inv R) (rep y) x" by (intro lifting_triple_Eq_abs_abs_if_rel)
  then have "Eq_rep R (rep y) x" by (subst (asm) Eq_abs_rel_inv_eq_Eq_rep)
  then show ?thesis by (blast dest: symmetricD[OF symmetric_Eq_rep])
qed

lemma lifting_triple_rel_abs_if_Eq_rep:
  assumes lift_trip: "lifting_triple R abs rep"
  and Eq_rep_x: "Eq_rep R x x'"
  shows "R x (abs x')"
proof -
  from Eq_rep_x obtain y where "R x y" "R x' y" by (rule Eq_repE)
  moreover then have "R x' (abs x')"
    by (intro lifting_triple_rel_abs_self_if_in_dom[OF lift_trip] in_domI)
  ultimately show "R x (abs x')"
    using z_propertyD'[OF z_property_if_lifting_triple[OF lift_trip]]
    by blast
qed

lemma lifting_triple_rel_rep_if_Eq_abs:
  assumes lift_trip: "lifting_triple R abs rep"
  and Eq_abs_y: "Eq_abs R y y'"
  shows "R (rep y) y'"
proof -
  from Eq_abs_y have "Eq_rep (rel_inv R) y y'" by (subst Eq_rep_rel_inv_eq_Eq_abs)
  then have "Eq_rep (rel_inv R) y' y" by (rule symmetricD[OF symmetric_Eq_rep])
  moreover from lift_trip have "lifting_triple (rel_inv R) rep abs"
    by (rule lifting_triple_dual)
  ultimately have "rel_inv R y' (rep y)" by (elim lifting_triple_rel_abs_if_Eq_rep)
  then show ?thesis by (blast dest: rel_invD)
qed

lemma lifting_triple_Eq_abs_abs_abs_if_Eq_rep:
  assumes "lifting_triple R abs rep"
  and "Eq_rep R x x'"
  shows "Eq_abs R (abs x) (abs x')"
  using assms
  by (intro lifting_triple_Eq_abs_abs_if_rel) (blast dest: lifting_triple_rel_abs_if_Eq_rep)+

lemma lifting_triple_Eq_rep_rep_rep_if_Eq_abs:
  assumes "lifting_triple R abs rep"
  and "Eq_abs R y1 y2"
  shows "Eq_rep R (rep y1) (rep y2)"
  using assms
  by (intro lifting_triple_Eq_rep_rep_if_rel) (blast dest: lifting_triple_rel_rep_if_Eq_abs)+

lemma lifting_triple_rel_comp_abs_abs_if_in_dom_rel_comp:
  assumes trans_trip1: "lifting_triple R1 abs1 rep1"
  and trans_trip2: "lifting_triple R2 abs2 rep2"
  and finer: "(Eq_abs R1 \<circ>\<circ> Eq_rep R2) \<sqsubseteq> (Eq_rep R2 \<circ>\<circ> Eq_abs R1)"
  and in_dom_x: "in_dom (R1 \<circ>\<circ> R2) x"
  shows "(R1 \<circ>\<circ> R2) x ((abs2 \<circ> abs1) x)"
proof (rule rel_compI)
  from in_dom_x obtain y where "(R1 \<circ>\<circ> R2) x y" by (rule in_domE)
  then obtain z where z: "R1 x z" "R2 z y" by (rule rel_compE)
  then have "in_dom R1 x" by (intro in_domI)
  then show R1_x_abs_x: "R1 x (abs1 x)"
    using trans_trip1 by (blast intro: lifting_triple_rel_abs_self_if_in_dom)
  then have "Eq_abs R1 z (abs1 x)" using z(1) by (intro Eq_absI)
  then have "Eq_abs R1 (abs1 x) z" using symmetric_Eq_abs by (fast dest: symmetricD)
  moreover from z(2) have "Eq_rep R2 z z" by (intro Eq_rep_self_if_in_dom in_domI)
  ultimately have "(Eq_abs R1 \<circ>\<circ> Eq_rep R2) (abs1 x) z" by (rule rel_compI)
  then have "(Eq_rep R2 \<circ>\<circ> Eq_abs R1) (abs1 x) z"
    using finer by (blast dest: finerD)
  then obtain z' where "Eq_abs R1 z' z" "Eq_rep R2 (abs1 x) z'" by (elim rel_compE)
  then have "Eq_rep R2 (abs1 x) (abs1 x)"
    using in_dom_if_Eq_rep by (fast intro: Eq_rep_self_if_in_dom)
  then show "R2 (abs1 x) ((abs2 \<circ> abs1) x)"
    unfolding comp_eq using trans_trip2
    by (blast intro: lifting_triple_rel_abs_if_Eq_rep)
qed

lemma lifting_triple_rel_comp_rep_rep_if_in_codom_rel_comp:
  assumes "lifting_triple R1 abs1 rep1"
  and "lifting_triple R2 abs2 rep2"
  and finer: "(Eq_abs R1 \<circ>\<circ> Eq_rep R2) \<sqsubseteq> (Eq_rep R2 \<circ>\<circ> Eq_abs R1)"
  and in_codom_y: "in_codom (R1 \<circ>\<circ> R2) y"
  shows "(R1 \<circ>\<circ> R2) ((rep1 \<circ> rep2) y) y"
proof -
  have "lifting_triple (rel_inv R2) rep2 abs2" "lifting_triple (rel_inv R1) rep1 abs1"
    using assms(1-2) by (blast intro: lifting_triple_dual)+
  moreover have "Eq_abs (rel_inv R2) \<circ>\<circ> Eq_rep (rel_inv R1) \<sqsubseteq>
    Eq_rep (rel_inv R1) \<circ>\<circ> Eq_abs (rel_inv R2)"
    using finer
    by (simp only: Eq_abs_rel_inv_eq_Eq_rep Eq_rep_rel_inv_eq_Eq_abs
      Eq_abs_rel_comp_Eq_rep_finer_iff)
  moreover from in_codom_y have "in_dom (rel_inv R2 \<circ>\<circ> rel_inv R1) y"
    by (subst rel_inv_comp_eq[symmetric] in_dom_rel_inv_iff_in_codom)+
  ultimately have "(rel_inv R2 \<circ>\<circ> rel_inv R1) y ((rep1 \<circ> rep2) y)"
    by (rule lifting_triple_rel_comp_abs_abs_if_in_dom_rel_comp)
  then have "rel_inv (R1 \<circ>\<circ> R2) y ((rep1 \<circ> rep2) y)" by (subst rel_inv_comp_eq)
  then show ?thesis by (rule rel_invD)
qed

lemma lifting_triple_compI:
  assumes trans_trip1: "lifting_triple R1 abs1 rep1"
  and trans_trip2: "lifting_triple R2 abs2 rep2"
  and finer: "(Eq_abs R1 \<circ>\<circ> Eq_rep R2) \<sqsubseteq> (Eq_rep R2 \<circ>\<circ> Eq_abs R1)"
  shows "lifting_triple (R1 \<circ>\<circ> R2) (abs2 \<circ> abs1) (rep1 \<circ> rep2)"
proof (rule lifting_tripleI)
  show "lifting_relation (R1 \<circ>\<circ> R2)"
    using assms
    by (intro lifting_relation_if_z_property
      z_property_rel_comp_if_rel_comp_finer_if_z_property' z_property_if_lifting_triple)
qed (blast intro!: lifting_triple_rel_comp_rep_rep_if_in_codom_rel_comp
  lifting_triple_rel_comp_abs_abs_if_in_dom_rel_comp assms)+

lemma lifting_triple_eq_id: "lifting_triple (=) id id"
  using lifting_relation_eq
  by (rule lifting_tripleI) (simp_all only: id_eq_self)


end