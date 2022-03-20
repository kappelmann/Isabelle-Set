theory Basic
  imports HOL.HOL
begin

(* hide_const abs *)

text \<open>From HOL.fun\<close>

definition comp :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c"  (infixl "\<circ>" 55)
  where "f \<circ> g = (\<lambda>x. f (g x))"

lemma comp_apply [simp]: "(f \<circ> g) x = f (g x)"
  by (simp add: comp_def)

text \<open>Binary relations represented as binary predicates\<close>

definition related :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" ("_ _ \<Colon> _" [101, 101, 101] 100)
  where "related x y T \<equiv> T x y"

text \<open>Basic functions on binary relations\<close>

definition rel_comp ::
    "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> bool)" (infixl "\<circ>\<circ>" 55)
    where "rel_comp R S x y \<equiv> (\<exists>z. R x z \<and> S z y)"

lemma rel_compI: "\<lbrakk>R x y; S y z\<rbrakk> \<Longrightarrow> (R \<circ>\<circ> S) x z"
  unfolding rel_comp_def by blast

lemma rel_compE: "\<lbrakk>(R \<circ>\<circ> S) x y; \<And>z. \<lbrakk>R x z; S z y\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding rel_comp_def by blast  

lemma rel_comp_assoc: "R \<circ>\<circ> (S \<circ>\<circ> T) = (R \<circ>\<circ> S) \<circ>\<circ> T"
  unfolding rel_comp_def by blast

definition rel_inv :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where "rel_inv R x y \<equiv> R y x"

definition in_dom :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "in_dom R x \<equiv> (\<exists>y. R x y)"

definition in_co_dom :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool"
  where "in_co_dom R y \<equiv> (\<exists>x. R x y)"

lemma in_domI: "R x y \<Longrightarrow> in_dom R x"
  unfolding in_dom_def by blast

lemma in_co_domI: "R x y \<Longrightarrow> in_co_dom R y"
  unfolding in_co_dom_def by blast

lemma in_domE: "\<lbrakk>in_dom R x; \<And>y. R x y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding in_dom_def by blast

lemma in_co_domE: "\<lbrakk>in_co_dom R y; \<And>x. R x y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding in_co_dom_def by blast


text \<open>Properties of binary relations\<close>

definition symmetric :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "symmetric R \<equiv> (\<forall>x y. R x y \<longrightarrow> R y x)"

lemma symmetricI: "(\<And>x y. R x y \<Longrightarrow> R y x) \<Longrightarrow> symmetric R"
  unfolding symmetric_def
  by blast

lemma symmetricE:
  shows "symmetric R \<Longrightarrow> R x y \<Longrightarrow> R y x"
  unfolding symmetric_def
  by blast

lemma sym_rel_comp: "symmetric (R \<circ>\<circ> rel_inv R)"
  apply (rule symmetricI)
  unfolding rel_comp_def rel_inv_def
  by blast

lemma sym_rel_inv: "symmetric R \<Longrightarrow> symmetric (rel_inv R)"
  apply (rule symmetricI)
  apply (drule symmetricE)
  unfolding rel_inv_def .

lemma rel_inv_comp_dist: "rel_inv (R \<circ>\<circ> S) = rel_inv S \<circ>\<circ> rel_inv R"
  unfolding rel_comp_def rel_inv_def
  by blast

lemma rel_inv_inv: "rel_inv (rel_inv R) = R"
  unfolding rel_inv_def ..

lemma rel_inv_comp_self_inv: "rel_inv (R \<circ>\<circ> rel_inv R) = R \<circ>\<circ> rel_inv R"
  unfolding rel_inv_comp_dist rel_inv_inv ..

definition transitive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "transitive R \<equiv> (\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z)"

lemma transitiveI: "(\<And>x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z) \<Longrightarrow> transitive R"
  unfolding transitive_def
  by blast

lemma transitiveE: "transitive R \<Longrightarrow> \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z"
  unfolding transitive_def
  by blast

definition partial_equivalence :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "partial_equivalence R \<equiv> symmetric R \<and> transitive R"

lemmas partial_equivalence_unfold = partial_equivalence_def[unfolded symmetric_def transitive_def]

lemma partial_equivalenceI:
  "\<lbrakk>\<And>x y. R x y \<Longrightarrow> R y x; \<And>x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z\<rbrakk> \<Longrightarrow> partial_equivalence R"
  unfolding partial_equivalence_unfold
  by blast

lemma partial_equivalence_sym:
  assumes "partial_equivalence R"
  shows "R x y \<Longrightarrow> R y x"
  using assms[unfolded partial_equivalence_unfold]
    by blast

lemma partial_equivalence_trans:
  assumes "partial_equivalence R"
  shows "\<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z"
  using assms[unfolded partial_equivalence_unfold]
    by blast

definition z_property :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "z_property R \<equiv> R \<circ>\<circ> rel_inv R \<circ>\<circ> R = R"

lemmas z_property_unfold = z_property_def[unfolded rel_comp_def rel_inv_def]

lemma z_propertyI: "(\<And>a b c d. \<lbrakk>R a b; R c b; R c d\<rbrakk> \<Longrightarrow> R a d) \<Longrightarrow> z_property R"
  unfolding z_property_def rel_comp_def rel_inv_def
  by blast

lemma z_propertyE: "z_property R \<Longrightarrow> \<lbrakk>R a b; R c b; R c d\<rbrakk> \<Longrightarrow> R a d"
proof -
  assume z_prop: "z_property R"
    and rels: "R a b" "R c b" "R c d"
  show "R a d"
    apply (subst z_prop[unfolded z_property_unfold, symmetric])
    using rels by blast
qed

lemma z_property_subst: "z_property R \<Longrightarrow> R \<circ>\<circ> rel_inv R \<circ>\<circ> R \<equiv> R"
  apply (rule eq_reflection)
  unfolding z_property_def .

definition Eq_rep :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "Eq_rep T \<equiv> T \<circ>\<circ> rel_inv T"

lemma Eq_repI: "\<lbrakk>T x z; T y z\<rbrakk> \<Longrightarrow> Eq_rep T x y"
  unfolding Eq_rep_def rel_comp_def rel_inv_def
  by blast

lemma Eq_repE: "Eq_rep T x y \<Longrightarrow> (\<exists>z. T x z \<and> T y z)"
  unfolding Eq_rep_def rel_comp_def rel_inv_def
  by blast

lemma Eq_repE': "\<lbrakk>Eq_rep T x y; \<And>z. \<lbrakk>T x z; T y z\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding Eq_rep_def rel_comp_def rel_inv_def
  by blast

lemma
  assumes "in_dom T x"
  shows "Eq_rep T x x"
proof -
  obtain y where y: "T x y"
    using in_domE[OF assms] .
  show "Eq_rep T x x"
    apply (rule Eq_repI)
    by (fact y)+
qed

definition Eq_abs :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
  where "Eq_abs T \<equiv> rel_inv T \<circ>\<circ> T"

lemma Eq_absI: "\<lbrakk>T x y; T x z\<rbrakk> \<Longrightarrow> Eq_abs T y z"
  unfolding Eq_abs_def rel_comp_def rel_inv_def
  by blast

lemma Eq_absE: "Eq_abs T y z \<Longrightarrow> (\<exists>x. T x y \<and> T x z)"
  unfolding Eq_abs_def rel_comp_def rel_inv_def
  by blast

lemma Eq_absE': "\<lbrakk>Eq_abs T y z; \<And>x. \<lbrakk>T x y; T x z\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding Eq_abs_def rel_comp_def rel_inv_def
  by blast

lemma Eq_rep_sym: "Eq_rep T x y \<Longrightarrow> Eq_rep T y x"
  unfolding Eq_rep_def rel_comp_def rel_inv_def by blast

lemma Eq_abs_sym: "Eq_abs T x y \<Longrightarrow> Eq_abs T y x"
  unfolding Eq_abs_def rel_comp_def rel_inv_def by blast

lemma Eq_rep_then_in_dom: "Eq_rep T x x' \<Longrightarrow> in_dom T x"
  apply (erule Eq_repE')
  apply (rule in_domI) .

lemma Eq_abs_then_in_co_dom: "Eq_abs T y y' \<Longrightarrow> in_co_dom T y"
  apply (erule Eq_absE')
  apply (rule in_co_domI) .

lemma z_property_rel_inv: "z_property T \<Longrightarrow> z_property (rel_inv T)"
  apply (rule z_propertyI)
  unfolding rel_inv_def
  apply (erule z_propertyE) .

lemma partial_equivalence_Eq_rep: "z_property T \<Longrightarrow> partial_equivalence (Eq_rep T)"
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
    using v w z_propertyE[OF z_prop]
    apply blast+
    done
qed

lemma "z_property T \<Longrightarrow> partial_equivalence (Eq_abs T)"
proof -
  have 1: "Eq_abs T \<equiv> Eq_rep (rel_inv T)"
    unfolding Eq_abs_def Eq_rep_def rel_inv_def .
  show "z_property T \<Longrightarrow> partial_equivalence (Eq_abs T)"
    unfolding 1
    using z_property_rel_inv partial_equivalence_Eq_rep
    by blast
qed

text \<open>Transfer triple\<close>

definition transfer_triple ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "transfer_triple T abs rep \<equiv>
    z_property T \<and>
    (\<forall>x. in_dom T x \<longrightarrow> T x (abs x)) \<and>
    (\<forall>y. in_co_dom T y \<longrightarrow> T (rep y) y)"

lemma transfer_tripleI:
  assumes z_prop: "z_property T"
      and abs: "\<And>x. in_dom T x \<Longrightarrow> T x (abs x)"
      and rep: "\<And>y. in_co_dom T y \<Longrightarrow> T (rep y) y"
  shows "transfer_triple T abs rep"
  using assms
  unfolding transfer_triple_def
  by blast

lemma rel_abs: "\<lbrakk>transfer_triple T abs rep; in_dom T x\<rbrakk> \<Longrightarrow> T x (abs x)"
  unfolding transfer_triple_def by blast

lemma rel_rep: "\<lbrakk>transfer_triple T abs rep; in_co_dom T y\<rbrakk> \<Longrightarrow> T (rep y) y"
  unfolding transfer_triple_def by blast

lemma Eq_abs_abs:
  assumes "transfer_triple T abs rep"
  shows "T x y \<Longrightarrow> Eq_abs T y (abs x)"
proof -
  have "\<And>x y. T x y \<Longrightarrow> T x (abs x)"
    using assms[unfolded transfer_triple_def in_dom_def in_co_dom_def]
    by blast
  hence "\<And>x y. T x y \<Longrightarrow> (rel_inv T \<circ>\<circ> T) y (abs x)"
    unfolding rel_comp_def rel_inv_def
    by blast
  thus "T x y \<Longrightarrow> Eq_abs T y (abs x)"
    unfolding Eq_abs_def .
qed

lemma Eq_rep_rep:
  assumes "transfer_triple T abs rep"
  shows "T x y \<Longrightarrow> Eq_rep T x (rep y)"
proof -
  have "\<And>x y. T x y \<Longrightarrow> T (rep y) y"
    using assms[unfolded transfer_triple_def in_dom_def in_co_dom_def]
    by blast
  hence "\<And>x y. T x y \<Longrightarrow> (T \<circ>\<circ> rel_inv T) x (rep y)"
    unfolding rel_comp_def rel_inv_def
    by blast
  thus "T x y \<Longrightarrow> Eq_rep T x (rep y)"
    unfolding Eq_rep_def .
qed
  

lemma
  assumes "z_property T"
      and "\<And>x y. T x y \<Longrightarrow> Eq_abs T y (abs x)"
      and "\<And>x y. T x y \<Longrightarrow> Eq_rep T x (rep y)"
    shows "transfer_triple T abs rep"
proof (rule transfer_tripleI)
  show "z_property T"
    using assms(1) .
next
  fix x
  assume prem: "in_dom T x"
  obtain y where y: "T x y"
    using in_domE[OF prem] .
  have 1: "(rel_inv T \<circ>\<circ> T) y (abs x)"
    unfolding rel_comp_def rel_inv_def
    using Eq_absE assms(2) y .
  have "(T \<circ>\<circ> rel_inv T \<circ>\<circ> T) x (abs x)"
    unfolding rel_comp_assoc[symmetric]
    using rel_compI y 1 .
  thus "T x (abs x)"
    apply (subst z_property_subst[OF assms(1), symmetric]) .
next
  fix y
  assume prem: "in_co_dom T y"
  obtain x where x: "T x y"
    using in_co_domE[OF prem] .
  have 1: "(T \<circ>\<circ> rel_inv T) (rep y) x"
    unfolding rel_comp_def rel_inv_def
    using Eq_repE Eq_rep_sym assms(3) x .
  have "(T \<circ>\<circ> rel_inv T \<circ>\<circ> T) (rep y) y"
    using rel_compI 1 x .
  thus "T (rep y) y"
    apply (subst z_property_subst[OF assms(1), symmetric]) .
qed

lemma z_property_transfer_triple:
  "transfer_triple T abs rep \<Longrightarrow> z_property T"
  unfolding transfer_triple_def
  by blast

lemma z_property_rel_comp:
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
      using Eq_absE'[OF z4(1)] .
    obtain y3 where y3: "T2 z4 y3" "T2 z3 y3"
      using Eq_repE'[OF z4(2)] .
    have "T1 x1 z4"
      using z_propertyE z_prop1 z1(1) x3 .
    moreover have "T2 z4 y2"
      using z_propertyE z_prop2 y3 z3(2) .
    ultimately show "(T1 \<circ>\<circ> T2) x1 y2"
      by (rule rel_compI)
  qed

lemma lifting_triple_composition:
  assumes trans_trip1: "transfer_triple T1 abs1 rep1"
      and trans_trip2: "transfer_triple T2 abs2 rep2"
      and Eq_comm: "rel_comp (Eq_abs T1) (Eq_rep T2) = rel_comp (Eq_rep T2) (Eq_abs T1)"
    shows "transfer_triple (T1 \<circ>\<circ> T2) (abs2 \<circ> abs1) (rep1 \<circ> rep2)"
proof (rule transfer_tripleI)
  show "z_property (T1 \<circ>\<circ> T2)"
    apply (rule z_property_rel_comp)
    apply (rule z_property_transfer_triple, (fact trans_trip1 | fact trans_trip2))+
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
    using rel_abs trans_trip1 in_dom1_x .
  have Eq_x_abs_x: "Eq_abs T1 z (abs1 x)"
    using Eq_absI z(1) T1_x_abs_x .
  have Eq_z_z: "Eq_rep T2 z z"
    using Eq_repI z(2) z(2) .
  have Eq_abs_x_z: "(Eq_abs T1 \<circ>\<circ> Eq_rep T2) (abs1 x) z"
    using rel_compI Eq_abs_sym[OF Eq_x_abs_x] Eq_z_z .
  obtain z' where z': "Eq_abs T1 z' z" "Eq_rep T2 (abs1 x) z'"
    using rel_compE Eq_abs_x_z[unfolded Eq_comm] .
  have in_dom2_abs_x: "in_dom T2 (abs1 x)"
    using Eq_rep_then_in_dom z'(2) .
  have T2_abs_x_abs_abs_x: "T2 (abs1 x) ((abs2 \<circ> abs1) x)"
    unfolding comp_def
    using rel_abs trans_trip2 in_dom2_abs_x .
  show "(T1 \<circ>\<circ> T2) x ((abs2 \<circ> abs1) x)"
    using rel_compI T1_x_abs_x T2_abs_x_abs_abs_x .
next
  fix y
  assume in_co_dom_y: "in_co_dom (T1 \<circ>\<circ> T2) y"
  obtain x where x: "(T1 \<circ>\<circ> T2) x y"
    using in_co_domE in_co_dom_y .
  obtain z where z: "T1 x z" "T2 z y"
    using rel_compE x .
  have in_co_dom2_y: "in_co_dom T2 y"
    using in_co_domI z(2) .
  have T2_rep_y_y: "T2 (rep2 y) y"
    using rel_rep trans_trip2 in_co_dom2_y .
  have Eq_x_rep_y: "Eq_rep T2 z (rep2 y)"
    using Eq_repI z(2) T2_rep_y_y .
  have Eq_z_z: "Eq_abs T1 z z"
    using Eq_absI z(1) z(1) .
  have Eq_rep_y_z: "(Eq_rep T2 \<circ>\<circ> Eq_abs T1) (rep2 y) z"
    using rel_compI Eq_rep_sym[OF Eq_x_rep_y] Eq_z_z .
  obtain z' where z': "Eq_rep T2 z' z" "Eq_abs T1 (rep2 y) z'"
    using rel_compE Eq_rep_y_z[folded Eq_comm] .
  have in_co_dom1_rep_y: "in_co_dom T1 (rep2 y)"
    using Eq_abs_then_in_co_dom z'(2) .
  have T1_rep_y_rep_rep_y: "T1 ((rep1 \<circ> rep2) y) (rep2 y)"
    unfolding comp_def
    using rel_rep trans_trip1 in_co_dom1_rep_y .
  show "(T1 \<circ>\<circ> T2) ((rep1 \<circ> rep2) y) y"
    using rel_compI T1_rep_y_rep_rep_y T2_rep_y_y .
qed


end