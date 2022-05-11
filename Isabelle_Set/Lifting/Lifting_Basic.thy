theory Lifting_Basic
  imports HOL.HOL
begin

(* hide_const abs *)

text \<open>From HOL.fun\<close>


definition id :: "'a \<Rightarrow> 'a"
  where "id x \<equiv> x"

lemma id_eq_self [simp]: "id x = x"
  by (simp add: id_def)

definition comp :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c"  (infixl "\<circ>" 55)
  where "f \<circ> g \<equiv> (\<lambda>x. f (g x))"

lemma comp_eq [simp]: "(f \<circ> g) x \<equiv> f (g x)"
  by (simp add: comp_def)

text \<open>Basic functions on binary relations\<close>

definition rel_comp ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> bool)" (infixl "\<circ>\<circ>" 55)
  where "rel_comp R S x y \<equiv> (\<exists>z. R x z \<and> S z y)"

lemma rel_compI: "\<lbrakk>R x y; S y z\<rbrakk> \<Longrightarrow> (R \<circ>\<circ> S) x z"
  unfolding rel_comp_def by blast

lemma rel_compE:
  assumes "(R \<circ>\<circ> S) x y"
  obtains z where "R x z" "S z y"
  using assms unfolding rel_comp_def by blast

lemma rel_comp_assoc: "R \<circ>\<circ> (S \<circ>\<circ> T) = (R \<circ>\<circ> S) \<circ>\<circ> T"
  unfolding rel_comp_def by blast

definition rel_inv :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where "rel_inv R x y \<equiv> R y x"

lemma rel_invD: "rel_inv R x y \<Longrightarrow> R y x"
  unfolding rel_inv_def .

definition in_dom :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "in_dom R x \<equiv> (\<exists>y. R x y)"

definition in_codom :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool"
  where "in_codom R y \<equiv> (\<exists>x. R x y)"

lemma in_domI: "R x y \<Longrightarrow> in_dom R x"
  unfolding in_dom_def by blast

lemma in_codomI: "R x y \<Longrightarrow> in_codom R y"
  unfolding in_codom_def by blast

lemma in_domE:
  assumes "in_dom R x"
  obtains y where " R x y"
  using assms unfolding in_dom_def by blast

lemma in_codomE:
  assumes "in_codom R y"
  obtains x where " R x y"
  using assms unfolding in_codom_def by blast

text \<open>Properties of binary relations\<close>

definition symmetric :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "symmetric R \<equiv> (\<forall>x y. R x y \<longrightarrow> R y x)"

lemma symmetricI: "(\<And>x y. R x y \<Longrightarrow> R y x) \<Longrightarrow> symmetric R"
  unfolding symmetric_def
  by blast

lemma symmetricD: "symmetric R \<Longrightarrow> R x y \<Longrightarrow> R y x"
  unfolding symmetric_def
  by blast

lemma symetric_rel_comp_inv: "symmetric (R \<circ>\<circ> rel_inv R)"
  apply (rule symmetricI)
  unfolding rel_comp_def rel_inv_def
  by blast

lemma sym_rel_inv: "symmetric R \<Longrightarrow> symmetric (rel_inv R)"
  unfolding rel_inv_def by (blast intro: symmetricI dest: symmetricD)

lemma rel_inv_eq_self_if_symmetric: "symmetric R \<Longrightarrow> rel_inv R = R"
  unfolding rel_inv_def by (auto dest: symmetricD)

lemma rel_inv_comp_eq: "rel_inv (R \<circ>\<circ> S) = rel_inv S \<circ>\<circ> rel_inv R"
  unfolding rel_comp_def rel_inv_def
  by blast

lemma rel_inv_rel_inv_eq_self: "rel_inv (rel_inv R) = R"
  unfolding rel_inv_def ..

lemma rel_inv_comp_rel_inv_eq: "rel_inv (R \<circ>\<circ> rel_inv R) = R \<circ>\<circ> rel_inv R"
  unfolding rel_inv_comp_eq rel_inv_rel_inv_eq_self ..

lemma eq_if_rel_inv_eq: "rel_inv R = rel_inv S \<Longrightarrow> R = S"
  apply (rule ext)+
  apply (drule fun_cong)+
  unfolding rel_inv_def .

definition transitive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "transitive R \<equiv> (\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z)"

lemma transitiveI: "(\<And>x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z) \<Longrightarrow> transitive R"
  unfolding transitive_def
  by blast

lemma transitiveD: "transitive R \<Longrightarrow> \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z"
  unfolding transitive_def
  by blast

definition partial_equivalence :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "partial_equivalence R \<equiv> symmetric R \<and> transitive R"

lemmas partial_equivalence_unfold = partial_equivalence_def[unfolded symmetric_def transitive_def]

lemma partial_equivalenceI:
  "\<lbrakk>\<And>x y. R x y \<Longrightarrow> R y x; \<And>x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z\<rbrakk> \<Longrightarrow> partial_equivalence R"
  unfolding partial_equivalence_unfold
  by blast

lemma rel_if_sym_rel_if_partial_equivalence:
  assumes "partial_equivalence R"
  and "R x y"
  shows "R y x"
  using assms[unfolded partial_equivalence_unfold] by blast

lemma rel_if_rel_if_rel_if_partial_equivalence:
  assumes "partial_equivalence R"
  and "R x y" "R y z"
  shows "R x z"
  using assms[unfolded partial_equivalence_unfold] by blast

definition z_property :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "z_property R \<equiv> R \<circ>\<circ> rel_inv R \<circ>\<circ> R = R"

lemmas z_property_unfold = z_property_def[unfolded rel_comp_def rel_inv_def]

lemma z_propertyI: "(\<And>a b c d. \<lbrakk>R a b; R c b; R c d\<rbrakk> \<Longrightarrow> R a d) \<Longrightarrow> z_property R"
  unfolding z_property_def rel_comp_def rel_inv_def
  by blast

lemma z_propertyD:
  assumes "z_property R"
  and "R a b" "R c b" "R c d"
  shows "R a d"
  apply (subst assms(1)[unfolded z_property_unfold, symmetric])
  using assms by blast

lemma z_property_if_partial_equivalence:
  assumes part_eqiv_R: "partial_equivalence R"
  shows "z_property R"
proof (rule z_propertyI)
  fix a b c d
  assume rels: "R a b" "R c b" "R c d"
  have rel': "R b c"
    using rel_if_sym_rel_if_partial_equivalence part_eqiv_R rels(2) .
  note trans = rel_if_rel_if_rel_if_partial_equivalence[OF part_eqiv_R]
  show "R a d" using trans trans rels(1) rel' rels(3) .
qed

definition Eq_rep :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "Eq_rep T \<equiv> T \<circ>\<circ> rel_inv T"

lemma Eq_repI: "\<lbrakk>T x z; T y z\<rbrakk> \<Longrightarrow> Eq_rep T x y"
  unfolding Eq_rep_def rel_comp_def rel_inv_def
  by blast

lemma Eq_repD: "Eq_rep T x y \<Longrightarrow> (\<exists>z. T x z \<and> T y z)"
  unfolding Eq_rep_def rel_comp_def rel_inv_def
  by blast

lemma Eq_repE: "\<lbrakk>Eq_rep T x y; \<And>z. \<lbrakk>T x z; T y z\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding Eq_rep_def rel_comp_def rel_inv_def
  by blast

lemma Eq_rep_self_if_in_dom:
  assumes "in_dom T x"
  shows "Eq_rep T x x"
proof -
  obtain y where y: "T x y"
    using in_domE[OF assms] .
  show "Eq_rep T x x"
    apply (rule Eq_repI)
    by (fact y)+
qed

lemma in_dom_if_Eq_rep: "Eq_rep T x x' \<Longrightarrow> in_dom T x"
  apply (erule Eq_repE)
  apply (rule in_domI) .

lemma Eq_rep_self_eq_in_dom: "Eq_rep T x x = in_dom T x"
  using Eq_rep_self_if_in_dom in_dom_if_Eq_rep by fast

definition Eq_abs :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  where "Eq_abs T \<equiv> rel_inv T \<circ>\<circ> T"

lemma Eq_absI: "\<lbrakk>T x y; T x z\<rbrakk> \<Longrightarrow> Eq_abs T y z"
  unfolding Eq_abs_def rel_comp_def rel_inv_def
  by blast

lemma Eq_absD: "Eq_abs T y z \<Longrightarrow> (\<exists>x. T x y \<and> T x z)"
  unfolding Eq_abs_def rel_comp_def rel_inv_def
  by blast

lemma Eq_absE: "\<lbrakk>Eq_abs T y z; \<And>x. \<lbrakk>T x y; T x z\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding Eq_abs_def rel_comp_def rel_inv_def
  by blast

lemma Eq_abs_self_if_in_codom:
  assumes "in_codom T y"
  shows "Eq_abs T y y"
proof -
  obtain x where y: "T x y"
    using in_codomE[OF assms] .
  show "Eq_abs T y y"
    apply (rule Eq_absI)
    by (fact y)+
qed

lemma in_codom_if_Eq_abs: "Eq_abs T y y' \<Longrightarrow> in_codom T y"
  apply (erule Eq_absE)
  apply (rule in_codomI) .

lemma Eq_abs_self_eq_in_codom: "Eq_abs T x x = in_codom T x"
  using Eq_abs_self_if_in_codom in_codom_if_Eq_abs by fast

lemma Eq_rep_sym: "Eq_rep T x y \<Longrightarrow> Eq_rep T y x"
  unfolding Eq_rep_def rel_comp_def rel_inv_def by blast

lemma symmetric_Eq_rep: "symmetric (Eq_rep T)"
  using symmetricI Eq_rep_sym .

lemma Eq_abs_sym: "Eq_abs T x y \<Longrightarrow> Eq_abs T y x"
  unfolding Eq_abs_def rel_comp_def rel_inv_def by blast

lemma symmetric_Eq_abs: "symmetric (Eq_abs T)"
  using symmetricI Eq_abs_sym .

lemma z_property_rel_inv_if_z_property: "z_property T \<Longrightarrow> z_property (rel_inv T)"
  apply (rule z_propertyI)
  unfolding rel_inv_def
  apply (erule z_propertyD) .

lemma partial_equivalence_Eq_rep_if_z_property:
  "z_property T \<Longrightarrow> partial_equivalence (Eq_rep T)"
proof (rule partial_equivalenceI)
  fix x y
  assume assm: "Eq_rep T x y"
  obtain z where z: "T x z" "T y z"
    using Eq_repE[OF assm] by blast
  show "Eq_rep T y x"
    apply (rule Eq_repI)
    using z(2, 1) .
next
  fix x y z
  assume z_prop: "z_property T"
    and rels: "Eq_rep T x y" "Eq_rep T y z"
  obtain v where v: "T x v" "T y v"
    using Eq_repE[OF rels(1)] by blast
  obtain w where w: "T y w" "T z w"
    using Eq_repE[OF rels(2)] by blast
  show "Eq_rep T x z"
    apply (rule Eq_repI)
    using v w z_propertyD[OF z_prop]
    apply blast+
    done
qed

lemma partial_equivalence_Eq_abs_if_z_property:
  "z_property T \<Longrightarrow> partial_equivalence (Eq_abs T)"
proof -
  have 1: "Eq_abs T \<equiv> Eq_rep (rel_inv T)"
    unfolding Eq_abs_def Eq_rep_def rel_inv_def .
  show "z_property T \<Longrightarrow> partial_equivalence (Eq_abs T)"
    unfolding 1
    using z_property_rel_inv_if_z_property partial_equivalence_Eq_rep_if_z_property
    by blast
qed

definition "left_unique R \<equiv> (\<forall>x x'. Eq_rep R x x' \<longrightarrow> x = x')"

lemma left_uniqueI: "(\<And>x x'. Eq_rep R x x' \<Longrightarrow> x = x') \<Longrightarrow> left_unique R"
  unfolding left_unique_def by blast


subsection \<open>Lifting Triples\<close>

definition lifting_triple ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "lifting_triple T abs rep \<equiv>
    z_property T \<and>
    (\<forall>x. in_dom T x \<longrightarrow> T x (abs x)) \<and>
    (\<forall>y. in_codom T y \<longrightarrow> T (rep y) y)"

lemma lifting_tripleI:
  assumes z_prop: "z_property T"
  and abs: "\<And>x. in_dom T x \<Longrightarrow> T x (abs x)"
  and rep: "\<And>y. in_codom T y \<Longrightarrow> T (rep y) y"
  shows "lifting_triple T abs rep"
  using assms
  unfolding lifting_triple_def
  by blast

lemma lifting_triple_rel_abs_if_in_dom:
  "\<lbrakk>lifting_triple T abs rep; in_dom T x\<rbrakk> \<Longrightarrow> T x (abs x)"
  unfolding lifting_triple_def by blast

lemma lifting_triple_rel_rep_if_in_codom:
  "\<lbrakk>lifting_triple T abs rep; in_codom T y\<rbrakk> \<Longrightarrow> T (rep y) y"
  unfolding lifting_triple_def by blast

lemma lifting_triple_Eq_abs_abs_if_rel:
  assumes "lifting_triple T abs rep"
  shows "T x y \<Longrightarrow> Eq_abs T y (abs x)"
proof -
  have "\<And>x y. T x y \<Longrightarrow> T x (abs x)"
    using assms[unfolded lifting_triple_def in_dom_def in_codom_def]
    by blast
  then have "\<And>x y. T x y \<Longrightarrow> (rel_inv T \<circ>\<circ> T) y (abs x)"
    unfolding rel_comp_def rel_inv_def
    by blast
  then show "T x y \<Longrightarrow> Eq_abs T y (abs x)"
    unfolding Eq_abs_def .
qed

lemma lifting_triple_Eq_rep_rep_if_rel:
  assumes "lifting_triple T abs rep"
  shows "T x y \<Longrightarrow> Eq_rep T x (rep y)"
proof -
  have "\<And>x y. T x y \<Longrightarrow> T (rep y) y"
    using assms[unfolded lifting_triple_def in_dom_def in_codom_def]
    by blast
  then have "\<And>x y. T x y \<Longrightarrow> (T \<circ>\<circ> rel_inv T) x (rep y)"
    unfolding rel_comp_def rel_inv_def
    by blast
  then show "T x y \<Longrightarrow> Eq_rep T x (rep y)"
    unfolding Eq_rep_def .
qed

lemma lifting_tripleI':
  assumes "z_property T"
  and "\<And>x y. T x y \<Longrightarrow> Eq_abs T y (abs x)"
  and "\<And>x y. T x y \<Longrightarrow> Eq_rep T x (rep y)"
  shows "lifting_triple T abs rep"
proof (rule lifting_tripleI)
  show "z_property T"
    using assms(1) .
next
  fix x
  assume prem: "in_dom T x"
  obtain y where y: "T x y"
    using in_domE[OF prem] .
  have 1: "(rel_inv T \<circ>\<circ> T) y (abs x)"
    unfolding rel_comp_def rel_inv_def
    using Eq_absD assms(2) y .
  have "(T \<circ>\<circ> rel_inv T \<circ>\<circ> T) x (abs x)"
    unfolding rel_comp_assoc[symmetric]
    using rel_compI y 1 .
  then show "T x (abs x)"
    using assms(1) unfolding z_property_def by simp
next
  fix y
  assume prem: "in_codom T y"
  obtain x where x: "T x y"
    using in_codomE[OF prem] .
  have 1: "(T \<circ>\<circ> rel_inv T) (rep y) x"
    unfolding rel_comp_def rel_inv_def
    using Eq_repD Eq_rep_sym assms(3) x .
  have "(T \<circ>\<circ> rel_inv T \<circ>\<circ> T) (rep y) y"
    using rel_compI 1 x .
  then show "T (rep y) y"
    using assms(1) unfolding z_property_def by simp
qed

lemma z_property_if_lifting_triple:
  "lifting_triple T abs rep \<Longrightarrow> z_property T"
  unfolding lifting_triple_def
  by blast

lemma lifting_triple_rel_abs_if_Eq_rep:
  assumes lift_trip: "lifting_triple T abs rep"
  and Eq: "Eq_rep T x x'"
  shows "T x (abs x')"
proof -
  obtain y where y: "T x y" "T x' y"
    using Eq_repE Eq .
  have 1: "T x' (abs x')"
    using lifting_triple_rel_abs_if_in_dom lift_trip in_domI y(2) .
  show "T x (abs x')"
    using z_propertyD z_property_if_lifting_triple lift_trip y 1 .
qed

lemma in_dom_rel_inv_iff_in_codom: "in_dom (rel_inv T) x \<equiv> in_codom T x"
  unfolding in_dom_def in_codom_def rel_inv_def .

lemma in_codom_rel_inv_iff_in_dom: "in_codom (rel_inv T) y \<equiv> in_dom T y"
  unfolding in_dom_def in_codom_def rel_inv_def .

lemma lifting_triple_dual:
  assumes lift_trip: "lifting_triple T abs rep"
  shows "lifting_triple (rel_inv T) rep abs"
proof (rule lifting_tripleI)
  show "z_property (rel_inv T)"
    using z_property_rel_inv_if_z_property z_property_if_lifting_triple lift_trip .
next
  fix x
  assume in_dom_inv_y: "in_dom (rel_inv T) x"
  show "rel_inv T x (rep x)"
    unfolding rel_inv_def
    using lifting_triple_rel_rep_if_in_codom lift_trip
      in_dom_inv_y[unfolded in_dom_rel_inv_iff_in_codom] .
next
  fix y
  assume in_codom_inv_x: "in_codom (rel_inv T) y"
  show "rel_inv T (abs y) y"
    unfolding rel_inv_def
    using lifting_triple_rel_abs_if_in_dom lift_trip
      in_codom_inv_x[unfolded in_codom_rel_inv_iff_in_dom] .
qed

lemma  Eq_rep_rel_inv_eq_Eq_abs: "Eq_rep (rel_inv T) \<equiv> Eq_abs T"
  apply (rule eq_reflection, (rule ext)+)
  unfolding Eq_rep_def Eq_abs_def rel_comp_def rel_inv_def
  by blast

lemma  Eq_abs_rel_inv_eq_Eq_rep: "Eq_abs (rel_inv T) \<equiv> Eq_rep T"
  apply (rule eq_reflection, (rule ext)+)
  unfolding Eq_rep_def Eq_abs_def rel_comp_def rel_inv_def
  by blast

lemma lifting_triple_rel_rep_if_Eq_abs:
  assumes lift_trip: "lifting_triple T abs rep"
  and Eq: "Eq_abs T y y'"
  shows "T (rep y) y'"
proof -
  have 1: "Eq_rep (rel_inv T) y' y"
    using Eq_rep_sym Eq[folded  Eq_rep_rel_inv_eq_Eq_abs].
  have 2: "rel_inv T y' (rep y)"
    using lifting_triple_rel_abs_if_Eq_rep lifting_triple_dual[OF lift_trip] 1 .
  show "T (rep y) y'"
    using rel_invD 2 .
qed

lemma z_property_rel_compI:
  assumes z_prop1: "z_property T1"
  and z_prop2: "z_property T2"
  and Eq_comm: "rel_comp (Eq_abs T1) (Eq_rep T2) = rel_comp (Eq_rep T2) (Eq_abs T1)"
  shows "z_property (T1 \<circ>\<circ> T2)"
  proof (rule z_propertyI)
    fix x1 y1 x2 y2
    assume rels: "(T1 \<circ>\<circ> T2) x1 y1" "(T1 \<circ>\<circ> T2) x2 y1" "(T1 \<circ>\<circ> T2) x2 y2"
    obtain z1 where z1: "T1 x1 z1" "T2 z1 y1"
      using rel_compE rels(1) .
    obtain z2 where z2: "T1 x2 z2" "T2 z2 y1"
      using rel_compE rels(2) .
    obtain z3 where z3: "T1 x2 z3" "T2 z3 y2"
      using rel_compE rels(3) .
    have Eq_rep_z1_z2: "Eq_rep T2 z1 z2"
      using Eq_repI z1(2) z2(2) .
    have Eq_abs_z2_z3: "Eq_abs T1 z2 z3"
      using Eq_absI z2(1) z3(1) .
    obtain z4 where z4: "Eq_abs T1 z1 z4" "Eq_rep T2 z4 z3"
      apply (rule rel_compE)
      apply (subst Eq_comm)
      using rel_compI Eq_rep_z1_z2 Eq_abs_z2_z3 .
    obtain x3 where x3: "T1 x3 z1" "T1 x3 z4"
      using Eq_absE[OF z4(1)] .
    obtain y3 where y3: "T2 z4 y3" "T2 z3 y3"
      using Eq_repE[OF z4(2)] .
    have "T1 x1 z4"
      using z_propertyD z_prop1 z1(1) x3 .
    moreover have "T2 z4 y2"
      using z_propertyD z_prop2 y3 z3(2) .
    ultimately show "(T1 \<circ>\<circ> T2) x1 y2"
      by (rule rel_compI)
  qed

lemma rel_comp_eq_if_compatible_if_z_property:
  assumes z_prop1: "z_property T1"
  and z_prop2: "z_property T2"
  and Eq_sup: "\<And>x1 x2. Eq_abs T1 x1 x2 \<Longrightarrow> Eq_rep T2 x1 x2"
  and dom_sub: "\<And>x. in_dom T2 x \<Longrightarrow> in_codom T1 x"
  shows "rel_comp (Eq_abs T1) (Eq_rep T2) = rel_comp (Eq_rep T2) (Eq_abs T1)"
proof ((rule ext)+, rule iffI)
  fix x1 x2
  assume prem: "(Eq_abs T1 \<circ>\<circ> Eq_rep T2) x1 x2"
  obtain y where y: "Eq_abs T1 x1 y" "Eq_rep T2 y x2"
    using rel_compE prem .
  have 1: "Eq_rep T2 x1 y"
    using Eq_sup y(1) .
  have 2: "Eq_rep T2 x1 x2"
    using rel_if_rel_if_rel_if_partial_equivalence
      partial_equivalence_Eq_rep_if_z_property z_prop2 1 y(2) .
  obtain x where x: "T1 x y"
    using Eq_absE y(1) .
  obtain z where 5: "T2 x2 z"
    using Eq_repE y(2) .
  have 6: "in_dom T2 x2"
    using in_domI 5 .
  have 7: "in_codom T1 x2"
    using dom_sub 6 .
  have 4: "Eq_abs T1 x2 x2"
    using Eq_abs_self_if_in_codom 7 .
  show "(Eq_rep T2 \<circ>\<circ> Eq_abs T1) x1 x2"
    using rel_compI 2 4 .
next
  fix x1 x2
  assume prem: "(Eq_rep T2 \<circ>\<circ> Eq_abs T1) x1 x2"
  obtain y where y: "Eq_rep T2 x1 y" "Eq_abs T1 y x2"
    using rel_compE prem .
  have 1: "Eq_rep T2 y x2"
    using Eq_sup y(2) .
  have 2: "Eq_rep T2 x1 x2"
    using rel_if_rel_if_rel_if_partial_equivalence
      partial_equivalence_Eq_rep_if_z_property z_prop2 y(1) 1 .
  obtain x where x: "T1 x y"
    using Eq_absE y(2) .
  obtain z where 5: "T2 x1 z"
    using Eq_repE y(1) .
  have 6: "in_dom T2 x1"
    using in_domI 5 .
  have 7: "in_codom T1 x1"
    using dom_sub 6 .
  have 4: "Eq_abs T1 x1 x1"
    using Eq_abs_self_if_in_codom 7 .
  show "(Eq_abs T1 \<circ>\<circ> Eq_rep T2) x1 x2"
    using rel_compI 4 2 .
qed

lemma in_codom_rel_inv_eq_in_dom: "in_codom (rel_inv T) = in_dom T"
  apply (rule ext)
  unfolding in_dom_def in_codom_def rel_inv_def
  by blast

lemma in_dom_rel_inv_eq_in_codom: "in_dom (rel_inv T) = in_codom T"
  apply (rule ext)
  unfolding in_dom_def in_codom_def rel_inv_def
  by blast

lemma rel_comp_eq_if_compatible_if_z_property':
  assumes z_prop1: "z_property T1"
  and z_prop2: "z_property T2"
  and Eq_sup: "\<And>x1 x2. Eq_rep T2 x1 x2 \<Longrightarrow> Eq_abs T1 x1 x2"
  and dom_sub: "\<And>x. in_codom T1 x \<Longrightarrow> in_dom T2 x"
  shows "rel_comp (Eq_abs T1) (Eq_rep T2) = rel_comp (Eq_rep T2) (Eq_abs T1)"
proof -
  show "rel_comp (Eq_abs T1) (Eq_rep T2) = rel_comp (Eq_rep T2) (Eq_abs T1)"
    apply (rule sym)
    apply (subst  Eq_rep_rel_inv_eq_Eq_abs[symmetric])+
    apply (subst   Eq_abs_rel_inv_eq_Eq_rep[of T2, symmetric])+
    apply (rule rel_comp_eq_if_compatible_if_z_property)
    apply (rule z_property_rel_inv_if_z_property, fact z_prop2)
      apply (rule z_property_rel_inv_if_z_property, fact z_prop1)
    unfolding  Eq_abs_rel_inv_eq_Eq_rep  Eq_rep_rel_inv_eq_Eq_abs
     apply (fact Eq_sup)
    unfolding in_codom_rel_inv_eq_in_dom in_dom_rel_inv_eq_in_codom
    apply (fact dom_sub)
    done
qed

lemma lifting_triple_compI:
  assumes trans_trip1: "lifting_triple T1 abs1 rep1"
  and trans_trip2: "lifting_triple T2 abs2 rep2"
  and Eq_comm: "rel_comp (Eq_abs T1) (Eq_rep T2) = rel_comp (Eq_rep T2) (Eq_abs T1)"
  shows "lifting_triple (T1 \<circ>\<circ> T2) (abs2 \<circ> abs1) (rep1 \<circ> rep2)"
proof (rule lifting_tripleI)
  show "z_property (T1 \<circ>\<circ> T2)"
    apply (rule z_property_rel_compI)
    apply (rule z_property_if_lifting_triple, (fact trans_trip1 | fact trans_trip2))+
    using Eq_comm .
next
  fix x
  assume in_dom_x: "in_dom (T1 \<circ>\<circ> T2) x"
  obtain y where y: "(T1 \<circ>\<circ> T2) x y"
    using in_domE in_dom_x .
  obtain z where z: "T1 x z" "T2 z y"
    using rel_compE y .
  have in_dom1_x: "in_dom T1 x"
    using in_domI z(1) .
  have T1_x_abs_x: "T1 x (abs1 x)"
    using lifting_triple_rel_abs_if_in_dom trans_trip1 in_dom1_x .
  have Eq_x_abs_x: "Eq_abs T1 z (abs1 x)"
    using Eq_absI z(1) T1_x_abs_x .
  have Eq_z_z: "Eq_rep T2 z z"
    using Eq_repI z(2) z(2) .
  have Eq_abs_x_z: "(Eq_abs T1 \<circ>\<circ> Eq_rep T2) (abs1 x) z"
    using rel_compI Eq_abs_sym[OF Eq_x_abs_x] Eq_z_z .
  obtain z' where z': "Eq_abs T1 z' z" "Eq_rep T2 (abs1 x) z'"
    using rel_compE Eq_abs_x_z[unfolded Eq_comm] .
  have in_dom2_abs_x: "in_dom T2 (abs1 x)"
    using in_dom_if_Eq_rep z'(2) .
  have T2_abs_x_abs_abs_x: "T2 (abs1 x) ((abs2 \<circ> abs1) x)"
    unfolding comp_def
    using lifting_triple_rel_abs_if_in_dom trans_trip2 in_dom2_abs_x .
  show "(T1 \<circ>\<circ> T2) x ((abs2 \<circ> abs1) x)"
    using rel_compI T1_x_abs_x T2_abs_x_abs_abs_x .
next
  fix y
  assume in_codom_y: "in_codom (T1 \<circ>\<circ> T2) y"
  obtain x where x: "(T1 \<circ>\<circ> T2) x y"
    using in_codomE in_codom_y .
  obtain z where z: "T1 x z" "T2 z y"
    using rel_compE x .
  have in_codom2_y: "in_codom T2 y"
    using in_codomI z(2) .
  have T2_rep_y_y: "T2 (rep2 y) y"
    using lifting_triple_rel_rep_if_in_codom trans_trip2 in_codom2_y .
  have Eq_x_rep_y: "Eq_rep T2 z (rep2 y)"
    using Eq_repI z(2) T2_rep_y_y .
  have Eq_z_z: "Eq_abs T1 z z"
    using Eq_absI z(1) z(1) .
  have Eq_rep_y_z: "(Eq_rep T2 \<circ>\<circ> Eq_abs T1) (rep2 y) z"
    using rel_compI Eq_rep_sym[OF Eq_x_rep_y] Eq_z_z .
  obtain z' where z': "Eq_rep T2 z' z" "Eq_abs T1 (rep2 y) z'"
    using rel_compE Eq_rep_y_z[folded Eq_comm] .
  have in_codom1_rep_y: "in_codom T1 (rep2 y)"
    using in_codom_if_Eq_abs z'(2) .
  have T1_rep_y_rep_rep_y: "T1 ((rep1 \<circ> rep2) y) (rep2 y)"
    unfolding comp_def
    using lifting_triple_rel_rep_if_in_codom trans_trip1 in_codom1_rep_y .
  show "(T1 \<circ>\<circ> T2) ((rep1 \<circ> rep2) y) y"
    using rel_compI T1_rep_y_rep_rep_y T2_rep_y_y .
qed

lemma lifting_triple_Eq_abs_abs_abs_if_Eq_rep:
  assumes lift_trip: "lifting_triple T abs rep"
  and eq: "Eq_rep T x x'"
  shows "Eq_abs T (abs x) (abs x')"
proof -
  obtain y where rels: "T x y" "T x' y"
    using Eq_repE eq .
  have lifting_triple_rel_abs_if_in_dom1: "T x (abs x)"
    using lifting_triple_rel_abs_if_in_dom lift_trip in_dom_if_Eq_rep eq .
  have lifting_triple_rel_abs_if_in_dom2: "T x' (abs x')"
    using lifting_triple_rel_abs_if_in_dom lift_trip in_dom_if_Eq_rep Eq_rep_sym eq .
  have  eq_abs1: "Eq_abs T (abs x) y"
    using Eq_absI lifting_triple_rel_abs_if_in_dom1 rels(1) .
  have eq_abs2: "Eq_abs T y (abs x')"
    using Eq_absI rels(2) lifting_triple_rel_abs_if_in_dom2 .
  show "Eq_abs T (abs x) (abs x')"
    using rel_if_rel_if_rel_if_partial_equivalence
      partial_equivalence_Eq_abs_if_z_property z_property_if_lifting_triple
      lift_trip eq_abs1 eq_abs2 .
qed

lemma lifting_triple_Eq_rep_rep_rep_if_Eq_abs:
  assumes lift_trip: "lifting_triple T abs rep"
  and Eq_y: "Eq_abs T y1 y2"
  shows "Eq_rep T (rep y1) (rep y2)"
proof -
  obtain x where 1: "T x y1" "T x y2"
    using Eq_absE Eq_y .
  have 2: "Eq_rep T x (rep y1)"
    using Eq_repI 1(1) lifting_triple_rel_rep_if_in_codom lift_trip in_codomI 1(1) .
  have 3: "Eq_rep T x (rep y2)"
    using Eq_repI 1(2) lifting_triple_rel_rep_if_in_codom lift_trip in_codomI 1(2) .
  have 4: "Eq_rep T (rep y1) x"
    using rel_if_sym_rel_if_partial_equivalence
      partial_equivalence_Eq_rep_if_z_property z_property_if_lifting_triple lift_trip 2 .
  show "Eq_rep T (rep y1) (rep y2)"
    using rel_if_rel_if_rel_if_partial_equivalence
      partial_equivalence_Eq_rep_if_z_property z_property_if_lifting_triple lift_trip
      4 3 .
qed

lemma lifting_triple_rel_comp_Eq_abs_eq_self:
  assumes lift_trip: "lifting_triple T abs rep"
  shows "T \<circ>\<circ> Eq_abs T = T"
proof ((rule ext)+, rule iffI)
  fix x y
  assume prem: "(T \<circ>\<circ> Eq_abs T) x y"
  obtain y' where T_x_y: "T x y'" and Eq_y'_y: "Eq_abs T y' y"
    using rel_compE prem .
  obtain x' where T_x'_y': "T x' y'" and T_x'_y: "T x' y"
    using Eq_absE Eq_y'_y .
  show "T x y"
    using z_propertyD z_property_if_lifting_triple lift_trip T_x_y T_x'_y' T_x'_y .
next
  fix x y
  assume rel: "T x y"
  show "(T \<circ>\<circ> Eq_abs T) x y"
    using rel_compI rel Eq_abs_self_if_in_codom in_codomI rel .
qed

lemma lifting_triple_Eq_rep_rel_comp_eq_self:
  assumes lift_trip: "lifting_triple T abs rep"
  shows "Eq_rep T \<circ>\<circ> T = T"
proof -
  have "rel_inv T \<circ>\<circ> Eq_abs (rel_inv T) = rel_inv T"
    using lifting_triple_rel_comp_Eq_abs_eq_self[OF lifting_triple_dual[OF lift_trip]] .
  then have "rel_inv T \<circ>\<circ> Eq_rep T = rel_inv T"
    unfolding  Eq_abs_rel_inv_eq_Eq_rep .
  then have "rel_inv T \<circ>\<circ> rel_inv (Eq_rep T) = rel_inv T"
    apply (subst rel_inv_eq_self_if_symmetric[OF symmetric_Eq_rep]) .
  then have "rel_inv ((Eq_rep T) \<circ>\<circ> T)  = rel_inv T"
    unfolding rel_inv_comp_eq .
  then show "Eq_rep T \<circ>\<circ> T = T"
    by (rule eq_if_rel_inv_eq)
qed

lemma lifting_triple_rel_if_Eq_abs_if_rel:
  assumes lift_trip: "lifting_triple T abs rep"
  and rel: "T x y"
  and eq: "Eq_abs T y y'"
  shows "T x y'"
  apply (subst lifting_triple_rel_comp_Eq_abs_eq_self[OF lift_trip, symmetric])
  using rel_compI rel eq .

lemma lifting_triple_eq_id: "lifting_triple (=) id id"
  apply (rule lifting_tripleI)
  apply (rule z_propertyI)
  by simp+


end