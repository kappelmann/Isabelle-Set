subsection \<open>Lifting Relations\<close>
theory Lifting_Relations
  imports LBinary_Relations
begin

subsubsection \<open>Induced Relations on Domain and Codomain\<close>

definition Eq_rep :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "Eq_rep R \<equiv> R \<circ>\<circ> rel_inv R"

lemma Eq_rep_eq_rel_comp_rel_inv: "Eq_rep R = R \<circ>\<circ> rel_inv R"
  unfolding Eq_rep_def by (rule refl)

lemma Eq_repI:
  assumes "R x y" "R x' y"
  shows "Eq_rep R x x'"
  unfolding Eq_rep_def using assms by (blast intro: rel_compI rel_invI)

lemma Eq_repE:
  assumes "Eq_rep R x x'"
  obtains y where "R x y" "R x' y"
  using assms unfolding Eq_rep_def by (blast elim: rel_compE dest: rel_invD)

lemma Eq_repD:
  assumes "Eq_rep R x x'"
  shows "(R \<circ>\<circ> rel_inv R) x x'"
  using assms unfolding Eq_rep_def .

text \<open>Note that @{term "Eq_rep R"} is symmetric but, in general, may not be transitive.\<close>

lemma symmetric_Eq_rep: "symmetric (Eq_rep R)"
  by (intro symmetricI, elim Eq_repE) (rule Eq_repI)

lemma in_dom_if_Eq_rep:
  assumes "Eq_rep R x x'"
  shows "in_dom R x"
  and "in_dom R x'"
  using assms by (blast elim: Eq_repE intro: in_domI)+

lemma Eq_rep_self_if_in_dom:
  assumes "in_dom R x"
  shows "Eq_rep R x x"
  using assms by (elim in_domE) (rule Eq_repI)

corollary Eq_rep_self_iff_in_dom: "Eq_rep R x x \<longleftrightarrow> in_dom R x"
  using in_dom_if_Eq_rep Eq_rep_self_if_in_dom by fast

definition Eq_abs :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  where "Eq_abs R \<equiv> rel_inv R \<circ>\<circ> R"

lemma Eq_abs_eq_rel_inv_rel_comp: "Eq_abs R = rel_inv R \<circ>\<circ> R"
  unfolding Eq_abs_def by (rule refl)

lemma Eq_absI:
  assumes "R x y" "R x y'"
  shows "Eq_abs R y y'"
  unfolding Eq_abs_def using assms by (blast intro: rel_compI rel_invI)

lemma Eq_absE:
  assumes "Eq_abs R y y'"
  obtains x where "R x y" "R x y'"
  using assms unfolding Eq_abs_def by (blast elim: rel_compE dest: rel_invD)

lemma Eq_absD:
  assumes "Eq_abs R y y'"
  shows "(rel_inv R \<circ>\<circ> R) y y'"
  using assms unfolding Eq_abs_def .

lemma Eq_rep_rel_inv_eq_Eq_abs: "Eq_rep (rel_inv R) = Eq_abs R"
proof standard+
  fix y y'
  {
    assume "Eq_rep (rel_inv R) y y'"
    then obtain x where "R x y" "R x y'" by (elim Eq_repE) (drule rel_invD)+
    then show "Eq_abs R y y'" by (rule Eq_absI)
  }
  assume "Eq_abs R y y'"
  then obtain x where "R x y" "R x y'" by (elim Eq_absE)
  then show "Eq_rep (rel_inv R) y y'" by (intro Eq_repI rel_invI)
qed

lemma Eq_abs_rel_inv_eq_Eq_rep: "Eq_abs (rel_inv R) = Eq_rep R"
proof -
  have "Eq_abs (rel_inv R) = Eq_rep (rel_inv (rel_inv R))"
    by (fact Eq_rep_rel_inv_eq_Eq_abs[symmetric])
  then show ?thesis by (subst (asm) rel_inv_rel_inv_eq_self)
qed

lemma symmetric_Eq_abs: "symmetric (Eq_abs R)"
  by (subst Eq_rep_rel_inv_eq_Eq_abs[symmetric]) (fact symmetric_Eq_rep)

lemma in_codom_if_Eq_abs:
  assumes "Eq_abs R y y'"
  shows "in_codom R y"
  and "in_codom R y'"
  using assms by (blast elim: Eq_absE intro: in_codomI)+

lemma Eq_abs_self_if_in_codom:
  assumes "in_codom R y"
  shows "Eq_abs R y y"
  using assms by (elim in_codomE) (rule Eq_absI)

corollary Eq_abs_self_iff_in_codom: "Eq_abs R y y \<longleftrightarrow> in_codom R y"
  using in_codom_if_Eq_abs Eq_abs_self_if_in_codom by fast

lemma Eq_abs_rel_comp_Eq_rep_finer_iff:
  "(Eq_abs R1 \<circ>\<circ> Eq_rep R2) \<sqsubseteq> (Eq_rep R2 \<circ>\<circ> Eq_abs R1) \<longleftrightarrow>
   (Eq_rep R2 \<circ>\<circ> Eq_abs R1) \<sqsubseteq> (Eq_abs R1 \<circ>\<circ> Eq_rep R2)"
  using symmetric_Eq_rep symmetric_Eq_abs
  by (intro rel_comp_finer_rel_comp_iff_if_symmetric)

lemma Eq_abs_rel_comp_Eq_rep_eq_if_finer:
  assumes "(Eq_abs R1 \<circ>\<circ> Eq_rep R2) \<sqsubseteq> (Eq_rep R2 \<circ>\<circ> Eq_abs R1)"
  shows "(Eq_abs R1 \<circ>\<circ> Eq_rep R2) = (Eq_rep R2 \<circ>\<circ> Eq_abs R1)"
  using assms symmetric_Eq_rep symmetric_Eq_abs
  by (intro eq_if_finer_if_symmetric)

corollary Eq_rep_rel_comp_Eq_abs_eq_if_finer:
  assumes "(Eq_rep R2 \<circ>\<circ> Eq_abs R1) \<sqsubseteq> (Eq_abs R1 \<circ>\<circ> Eq_rep R2)"
  shows "(Eq_rep R2 \<circ>\<circ> Eq_abs R1) = (Eq_abs R1 \<circ>\<circ> Eq_rep R2)"
  using assms
  by (subst (asm) Eq_abs_rel_comp_Eq_rep_finer_iff[symmetric])
    (intro Eq_abs_rel_comp_Eq_rep_eq_if_finer[symmetric])

lemma Eq_abs_rel_comp_Eq_rep_eq_Eq_rep_rel_comp_Eq_absI:
  assumes "transitive (Eq_rep R2)"
  and "Eq_abs R1 \<sqsubseteq> Eq_rep R2"
  and in_codom_if_in_dom: "\<And>x. in_dom R2 x \<Longrightarrow> in_codom R1 x"
  shows "Eq_abs R1 \<circ>\<circ> Eq_rep R2 = Eq_rep R2 \<circ>\<circ> Eq_abs R1"
proof (intro Eq_abs_rel_comp_Eq_rep_eq_if_finer
  rel_comp_finer_rel_comp_if_rel_self_if_finer_if_trans)
  fix x y assume "Eq_rep R2 x y"
  then have "in_dom R2 y" by (rule in_dom_if_Eq_rep)
  then have "in_codom R1 y" by (rule in_codom_if_in_dom)
  then show "Eq_abs R1 y y" by (rule Eq_abs_self_if_in_codom)
qed fact+


subsubsection \<open>Lifting Relations and Z-Property\<close>

definition lifting_relation :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "lifting_relation R \<equiv>
    \<comment>\<open>The induced relations on the domain and codomain are PERs\<close>
    partial_equivalence (Eq_rep R) \<and>
    partial_equivalence (Eq_abs R) \<and>
    \<comment>\<open>R respects the PERs on its domain and codomain\<close>
    (\<forall>x x' y y'. R x y \<and> Eq_rep R x x' \<and> Eq_abs R y y' \<longrightarrow> R x' y')"

lemma lifting_relationI:
  assumes "partial_equivalence (Eq_rep R)"
  and "partial_equivalence (Eq_abs R)"
  and "\<And>x x' y y'. \<lbrakk>R x y; Eq_rep R x x'; Eq_abs R y y'\<rbrakk> \<Longrightarrow> R x' y'"
  shows "lifting_relation R"
  unfolding lifting_relation_def using assms by blast

lemma partial_equivalence_Eq_rep_if_lifting_relation:
  assumes "lifting_relation R"
  shows "partial_equivalence (Eq_rep R)"
  using assms unfolding lifting_relation_def by blast

lemma partial_equivalence_Eq_abs_if_lifting_relation:
  assumes "lifting_relation R"
  shows "partial_equivalence (Eq_abs R)"
  using assms unfolding lifting_relation_def by blast

lemma rel_if_Eq_abs_if_Eq_rep_if_rel_if_lifting_relation:
  assumes "lifting_relation R"
  and "R x y"
  and "Eq_rep R x x'" "Eq_abs R y y'"
  shows "R x' y'"
  using assms unfolding lifting_relation_def by blast

paragraph \<open>Above properties are quite intuitive. However, they are not so elegant for
formalisation efforts. We next introduce a compact property that characterises exactly
the lifting relations.\<close>

definition z_property :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "z_property R \<equiv> R \<circ>\<circ> rel_inv R \<circ>\<circ> R = R"

lemma z_propertyI:
  assumes "R \<circ>\<circ> rel_inv R \<circ>\<circ> R = R"
  shows "z_property R"
  unfolding z_property_def using assms .

lemma z_propertyI':
  assumes "\<And>a b c d. \<lbrakk>R a b; R c b; R c d\<rbrakk> \<Longrightarrow> R a d"
  shows "z_property R"
  using assms
  by (intro z_propertyI ext) (blast intro: rel_compI rel_invI elim: rel_compE dest: rel_invD)

lemma z_propertyD:
  assumes "z_property R"
  shows "R \<circ>\<circ> rel_inv R \<circ>\<circ> R = R"
  using assms unfolding z_property_def .

lemma z_propertyD':
  assumes "z_property R"
  and "R a b" "R c b" "R c d"
  shows "R a d"
  using assms by (blast intro: rel_compI rel_invI dest: z_propertyD dest!: fun_cong)

lemma rel_comp_Eq_abs_eq_self_if_z_property:
  assumes "z_property R"
  shows "R \<circ>\<circ> Eq_abs R = R"
  using assms
  by (subst Eq_abs_eq_rel_inv_rel_comp rel_comp_assoc)+ (blast dest: z_propertyD)

lemma Eq_rep_rel_comp_eq_self_if_z_property:
  assumes "z_property R"
  shows "Eq_rep R \<circ>\<circ> R = R"
  using assms
  by (subst Eq_rep_eq_rel_comp_rel_inv rel_comp_assoc)+ (blast dest: z_propertyD)

lemma z_property_rel_inv_if_z_property:
  assumes "z_property R"
  shows "z_property (rel_inv R)"
  using assms by (intro z_propertyI') (blast intro: rel_invI dest: rel_invD z_propertyD')

lemma transitive_Eq_rep_if_z_property:
  assumes "z_property R"
  shows "transitive (Eq_rep R)"
  using assms
  by (intro transitiveI) (blast elim: Eq_repE intro: transitiveI Eq_repI dest: z_propertyD')

lemma partial_equivalence_Eq_rep_if_z_property:
  assumes "z_property R"
  shows "partial_equivalence (Eq_rep R)"
  using assms symmetric_Eq_rep transitive_Eq_rep_if_z_property
  by (intro partial_equivalenceI)

lemma transitive_Eq_abs_if_z_property:
  assumes "z_property R"
  shows "transitive (Eq_abs R)"
proof -
  from assms have "z_property (rel_inv R)" by (rule z_property_rel_inv_if_z_property)
  then have "transitive (Eq_rep (rel_inv R))" by (rule transitive_Eq_rep_if_z_property)
  then show ?thesis by (subst (asm) Eq_rep_rel_inv_eq_Eq_abs)
qed

lemma partial_equivalence_Eq_abs_if_z_property:
  assumes "z_property R"
  shows "partial_equivalence (Eq_abs R)"
  using assms symmetric_Eq_abs transitive_Eq_abs_if_z_property
  by (intro partial_equivalenceI)

lemma lifting_relation_if_z_property:
  assumes "z_property R"
  shows "lifting_relation R"
proof (rule lifting_relationI)
  fix x x' y y'
  assume "R x y" "Eq_rep R x x'" "Eq_abs R y y'"
  moreover from \<open>Eq_abs R y y'\<close> obtain x'' where "R x'' y" "R x'' y'"
    by (elim Eq_absE)
  ultimately have "R x y'" using assms by (blast dest: z_propertyD')
  from \<open>Eq_rep R x x'\<close> obtain y'' where "R x' y''" "R x y''"
    by (elim Eq_repE)
  with assms \<open>R x y'\<close> show "R x' y'" by (blast dest: z_propertyD')
qed (intro partial_equivalence_Eq_abs_if_z_property
  partial_equivalence_Eq_rep_if_z_property assms)+

lemma z_property_if_lifting_relation:
  assumes "lifting_relation R"
  shows "z_property R"
proof (rule z_propertyI')
  fix a b c d
  assume "R a b" "R c b" "R c d"
  then have "Eq_rep R a a" "Eq_abs R b d" by (blast intro: Eq_repI Eq_absI)+
  with \<open>R a b\<close> assms show "R a d"
    using rel_if_Eq_abs_if_Eq_rep_if_rel_if_lifting_relation by fast
qed

corollary lifting_relation_iff_z_property: "lifting_relation R \<longleftrightarrow> z_property R"
  using lifting_relation_if_z_property z_property_if_lifting_relation by blast

lemma lifting_relationI':
  assumes "\<And>a b c d. \<lbrakk>R a b; R c b; R c d\<rbrakk> \<Longrightarrow> R a d"
  shows "lifting_relation R"
  using assms by (intro lifting_relation_if_z_property z_propertyI')

lemma lifting_relation_rel_inv_if_lifting_relation:
  assumes "lifting_relation R"
  shows "lifting_relation (rel_inv R)"
  using assms
  by (blast intro: lifting_relation_if_z_property z_property_rel_inv_if_z_property
    dest: z_property_if_lifting_relation)

lemma z_property_rel_comp_if_rel_comp_finer_if_z_property:
  assumes z_prop1: "z_property R1"
  and z_prop2: "z_property R2"
  and Eq_finer: "(Eq_rep R2 \<circ>\<circ> Eq_abs R1) \<sqsubseteq> (Eq_abs R1 \<circ>\<circ> Eq_rep R2)"
  shows "z_property (R1 \<circ>\<circ> R2)"
proof (rule z_propertyI')
  fix x1 y1 x2 y2
  assume prems: "(R1 \<circ>\<circ> R2) x1 y1" "(R1 \<circ>\<circ> R2) x2 y1" "(R1 \<circ>\<circ> R2) x2 y2"
  obtain z1 where z1: "R1 x1 z1" "R2 z1 y1" using rel_compE prems(1) .
  obtain z2 where z2: "R1 x2 z2" "R2 z2 y1" using rel_compE prems(2) .
  obtain z3 where z3: "R1 x2 z3" "R2 z3 y2" using rel_compE prems(3) .
  have "Eq_rep R2 z1 z2" using z1(2) z2(2) by (rule Eq_repI)
  moreover have "Eq_abs R1 z2 z3" using z2(1) z3(1) by (rule Eq_absI )
  ultimately have "(Eq_rep R2 \<circ>\<circ> Eq_abs R1) z1 z3" by (rule rel_compI)
  then have "(Eq_abs R1 \<circ>\<circ> Eq_rep R2) z1 z3" by (rule finerD[OF Eq_finer])
  then obtain z4 where z4: "Eq_abs R1 z1 z4" "Eq_rep R2 z4 z3" by (elim rel_compE)
  obtain x3 where x3: "R1 x3 z1" "R1 x3 z4" using z4(1) by (rule Eq_absE)
  obtain y3 where y3: "R2 z4 y3" "R2 z3 y3" using z4(2) by (rule Eq_repE)
  have "R1 x1 z4" using z_prop1 z1(1) x3 by (rule z_propertyD')
  moreover have "R2 z4 y2" using z_prop2 y3 z3(2) by (rule z_propertyD')
  ultimately show "(R1 \<circ>\<circ> R2) x1 y2" by (rule rel_compI)
qed

corollary z_property_rel_comp_if_rel_comp_finer_if_z_property':
  assumes "z_property R1"
  and "z_property R2"
  and "(Eq_abs R1 \<circ>\<circ> Eq_rep R2) \<sqsubseteq> (Eq_rep R2 \<circ>\<circ> Eq_abs R1)"
  shows "z_property (R1 \<circ>\<circ> R2)"
  using assms z_property_rel_comp_if_rel_comp_finer_if_z_property
    Eq_abs_rel_comp_Eq_rep_finer_iff
  by blast

lemma z_property_rel_comp_if_in_codom_if_in_dom_if_finer_if_z_property:
  assumes z_prop1: "z_property R1"
  and z_prop2: "z_property R2"
  and finer: "Eq_abs R1 \<sqsubseteq> Eq_rep R2"
  and in_codom_if_in_dom: "\<And>x. in_dom R2 x \<Longrightarrow> in_codom R1 x"
  shows "z_property (R1 \<circ>\<circ> R2)"
proof -
  from z_prop2 have "transitive (Eq_rep R2)" by (rule transitive_Eq_rep_if_z_property)
  then have "Eq_abs R1 \<circ>\<circ> Eq_rep R2 = Eq_rep R2 \<circ>\<circ> Eq_abs R1"
    using finer in_codom_if_in_dom by (rule Eq_abs_rel_comp_Eq_rep_eq_Eq_rep_rel_comp_Eq_absI)
  then have "Eq_abs R1 \<circ>\<circ> Eq_rep R2 \<sqsubseteq> Eq_rep R2 \<circ>\<circ> Eq_abs R1"
    by (intro finerI) simp
  then show ?thesis
    using z_prop1 z_prop2
    by (intro z_property_rel_comp_if_rel_comp_finer_if_z_property' finer_self)
qed

corollary z_property_rel_comp_if_in_dom_if_in_codom_if_finer_if_z_property:
  assumes "z_property R1"
  and "z_property R2"
  and finer: "Eq_rep R2 \<sqsubseteq> Eq_abs R1"
  and in_dom_if_in_codom: "\<And>x. in_codom R1 x \<Longrightarrow> in_dom R2 x"
  shows "z_property (R1 \<circ>\<circ> R2)"
proof -
  from assms(1-2) have "z_property (rel_inv R2)" "z_property (rel_inv R1)"
    by (blast intro: z_property_rel_inv_if_z_property)+
  moreover from finer have "Eq_abs (rel_inv R2) \<sqsubseteq> Eq_rep (rel_inv R1)"
    by (subst Eq_abs_rel_inv_eq_Eq_rep Eq_rep_rel_inv_eq_Eq_abs)+
  moreover from in_dom_if_in_codom have
    "\<And>x. in_dom (rel_inv R1) x \<Longrightarrow> in_codom (rel_inv R2) x"
    by (simp only: in_dom_rel_inv_iff_in_codom in_codom_rel_inv_iff_in_dom)
  ultimately have "z_property (rel_inv R2 \<circ>\<circ> rel_inv R1)"
    by (rule z_property_rel_comp_if_in_codom_if_in_dom_if_finer_if_z_property)
  then have "z_property (rel_inv (R1 \<circ>\<circ> R2))"
    by (subst z_property_rel_inv_if_z_property rel_inv_comp_eq)
  then show ?thesis
    by (subst rel_inv_rel_inv_eq_self[symmetric]) (rule z_property_rel_inv_if_z_property)
qed

lemma z_property_if_right_unique:
  assumes "right_unique R"
  shows "z_property R"
  using assms by (intro z_propertyI') (blast dest: right_uniqueD)

lemma z_property_if_partial_equivalence:
  assumes "partial_equivalence R"
  shows "z_property R"
proof (rule z_propertyI)
  from assms have "R \<circ>\<circ> R = R"
    using rel_comp_self_eq_self_if_partial_equivalence by blast
  moreover from assms have "rel_inv R = R"
    using rel_inv_eq_self_if_symmetric by (blast elim: partial_equivalenceE)
  ultimately show "R \<circ>\<circ> rel_inv R \<circ>\<circ> R = R" by simp
qed

lemma lifting_relation_eq: "lifting_relation (=)"
  by (intro lifting_relation_if_z_property z_property_if_right_unique right_unique_eq)


end