theory Lifting_Functions
  imports
    Lifting_Triples
    Functions_Relators
begin

definition rel_rest ::
    "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)" ("[_ | _]" [102, 102])
  where "rel_rest R p \<equiv> (\<lambda>x y. R x y \<and> p x y)"

lemma rel_restI: "\<lbrakk>T x y; P x y\<rbrakk> \<Longrightarrow> [T | P] x y"
  unfolding rel_rest_def by simp

lemma rel_restE:
  assumes "[T | P] x y"
  obtains "T x y" "P x y"
  using assms unfolding rel_rest_def by simp

lemma z_property_rel_restI:
  assumes z_prop_T: "z_property T"
    and z_prop_P: "z_property P"
  shows "z_property [T | P]"
  apply (rule z_propertyI')
  using z_propertyD'[OF z_prop_T] z_propertyD'[OF z_prop_P]
  unfolding rel_rest_def
  by blast

lemma lifting_triple_rel_restI:
  assumes lift_trip: "lifting_triple T abs rep"
    and eq: "(Eq_rep T \<Rrightarrow> Eq_abs T \<Rrightarrow> (=)) P P"
  shows "lifting_triple [T | P] abs rep"
proof (intro lifting_tripleI lifting_relation_if_z_property)
  show "z_property [T | P]"
  proof (rule z_propertyI')
    fix x y x' y'
    assume rels: "[T | P] x y" "[T | P] x' y" "[T | P] x' y'"
    have in_dom_T_x: "in_dom T x"
      using rels(1) in_domI
      unfolding rel_rest_def
      by fast
    have Eq_abs_y_y': "Eq_abs T y y'"
      apply (rule Eq_absI)
      using rels(2, 3)
      unfolding rel_rest_def
      apply blast+
      done
    have T_x_y': "T x y'"
      using z_propertyD' z_property_if_lifting_triple[OF lift_trip] rels
      unfolding rel_rest_def
      by fast
    show "[T | P] x y'"
      apply (rule rel_restI)
      apply (fact T_x_y')
      apply (rule rel_restE[OF rels(1)])
      unfolding Dep_Fun_RelD[OF Dep_Fun_RelD[OF eq], OF Eq_rep_self_if_in_dom[OF in_dom_T_x] Eq_abs_y_y'] .
  qed
next
  fix x
  assume in_dom_rel_rest_x: "in_dom [T | P] x"
  obtain y where rel_rest_x_y: "[T | P] x y"
    using in_domE in_dom_rel_rest_x .
  have in_dom_T_x: "in_dom T x"
    apply (rule in_domI)
    by (rule rel_restE[OF rel_rest_x_y], assumption)
  have T_x_abs_x: "T x (abs x)"
    by (fact lifting_triple_rel_abs_self_if_in_dom[OF lift_trip, OF in_dom_T_x])
  have T_x_y: "T x y" and P_x_y: "P x y"
    by (rule rel_restE[OF rel_rest_x_y], assumption)+
  have lifting_triple_Eq_abs_abs_if_rel_x_y: "Eq_abs T (abs x) y"
    using Eq_absI T_x_abs_x T_x_y .
  show "[T | P] x (abs x)"
    apply (rule rel_restI)
    using Dep_Fun_RelD[OF Dep_Fun_RelD[OF eq], OF Eq_rep_self_if_in_dom[OF in_dom_T_x] lifting_triple_Eq_abs_abs_if_rel_x_y]
      T_x_abs_x P_x_y
    by simp+
next
  fix y
  assume in_codom_rel_rest_y: "in_codom [T | P] y"
  obtain x where rel_rest_x_y: "[T | P] x y"
    using in_codomE in_codom_rel_rest_y .
  have in_codom_T_y: "in_codom T y"
    apply (rule in_codomI)
    by (rule rel_restE[OF rel_rest_x_y], assumption)
  have T_rep_y_y: "T (rep y) y"
    by (fact lifting_triple_rel_rep_self_if_in_codom[OF lift_trip, OF in_codom_T_y])
  have T_x_y: "T x y" and P_x_y: "P x y"
    by (rule rel_restE[OF rel_rest_x_y], assumption)+
  have lifting_triple_Eq_rep_rep_if_rel_y_x: "Eq_rep T (rep y) x"
    using Eq_repI T_rep_y_y T_x_y .
  show "[T | P] (rep y) y"
    apply (rule rel_restI)
    using Dep_Fun_RelD[OF Dep_Fun_RelD[OF eq], OF lifting_triple_Eq_rep_rep_if_rel_y_x Eq_abs_self_if_in_codom[OF in_codom_T_y]]
      T_rep_y_y P_x_y
    by simp+
qed

definition rel_weak :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
    ("[_ \<longrightarrow> _]" [102, 102] 101)
  where "rel_weak P R \<equiv> (\<lambda>x y. P \<longrightarrow> R x y)"

definition rel_weak_rest :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
    ("[_ \<longrightarrow> _ | _]" [102, 102] 101)
  where "rel_weak_rest P R Q \<equiv> (\<lambda>x y. P \<longrightarrow> R x y \<and> Q x y)"

lemma z_property_fun_relI:
  assumes "z_property T1"
  and "z_property T2"
  shows "z_property (T1 \<Rrightarrow> T2)"
  apply (rule z_propertyI')
  apply (rule Dep_Fun_RelI)
  apply (drule Dep_Fun_RelD, assumption)+
  using z_propertyD'[OF assms(2)]
  by blast

lemma Eq_rep_appI:
  assumes lift_trip1: "lifting_triple T1 abs1 rep1"
  and lift_trip2: "\<And>x y. T1 x y \<Longrightarrow> lifting_triple (T2 x y) (abs2 y x) (rep2 x y)"
  and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
  and Eq_fun: "Eq_rep (Dep_Fun_Rel T1 T2) f f'"
  and Eq_arg: "Eq_rep T1 x x'"
  shows "Eq_rep (T2 x (abs1 x)) (f x) (f' x')"
proof -
  obtain g where Fun_Rel: "Dep_Fun_Rel T1 T2 f g" "Dep_Fun_Rel T1 T2 f' g"
    using Eq_repE Eq_fun .
  obtain y where rel_arg: "T1 x y" "T1 x' y"
    using Eq_repE Eq_arg .
  have lifting_triple_Eq_abs_abs_if_rel_x_y: "Eq_abs T1 (abs1 x) y"
    using Eq_absI lifting_triple_rel_abs_self_if_in_dom lift_trip1 in_domI rel_arg(1, 1) .
  have rel_res: "T2 x y (f x) (g y)"
    using Dep_Fun_RelE Fun_Rel(1) rel_arg(1) .
  have rel_res': "T2 x' y (f' x') (g y)"
    using Dep_Fun_RelE Fun_Rel(2) rel_arg(2) .
  have Eq_rel1: "T2 x y = T2 x' y"
    using T2_resp rel_arg(1) Eq_arg Eq_abs_self_if_in_codom in_codomI rel_arg(1) .
  have Eq_rel2: "T2 x y = T2 x (abs1 x)"
    using T2_resp rel_arg(1) Eq_rep_self_if_in_dom in_domI rel_arg(1)
      symmetricD[OF symmetric_Eq_abs] lifting_triple_Eq_abs_abs_if_rel_x_y .
  show " Eq_rep (T2 x (abs1 x)) (f x) (f' x')"
    using Eq_repI rel_res[unfolded Eq_rel2] rel_res'[folded Eq_rel1, unfolded Eq_rel2] .
qed

lemma Eq_abs_appI:
  assumes lift_trip1: "lifting_triple T1 abs1 rep1"
  and lift_trip2: "\<And>x y. T1 x y \<Longrightarrow> lifting_triple (T2 x y) (abs2 y x) (rep2 x y)"
  and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
  and Eq_fun: "Eq_abs (Dep_Fun_Rel T1 T2) g g'"
  and Eq_arg: "Eq_abs T1 y y'"
  shows "Eq_abs (T2 (rep1 y) y) (g y) (g' y')"
proof -
  obtain f where Fun_Rel: "Dep_Fun_Rel T1 T2 f g" "Dep_Fun_Rel T1 T2 f g'"
    using Eq_absE Eq_fun .
  obtain x where rel_arg: "T1 x y" "T1 x y'"
    using Eq_absE Eq_arg .
  have Eq_rep_x_rep_y: "Eq_rep T1 x (rep1 y)"
    using Eq_repI rel_arg(1) lifting_triple_rel_rep_self_if_in_codom lift_trip1 in_codomI rel_arg(1) .
  have rel_res: "T2 x y (f x) (g y)"
    using Dep_Fun_RelE Fun_Rel(1) rel_arg(1) .
  have rel_res': "T2 x y' (f x) (g' y')"
    using Dep_Fun_RelE Fun_Rel(2) rel_arg(2) .
  have Eq_rel1: "T2 x y = T2 x y'"
    using T2_resp rel_arg(1) Eq_rep_self_if_in_dom in_domI rel_arg(1) Eq_arg .
  have Eq_rel2: "T2 x y = T2 (rep1 y) y"
    using T2_resp rel_arg(1) Eq_rep_x_rep_y Eq_abs_self_if_in_codom in_codomI rel_arg(1) .
  show "Eq_abs (T2 (rep1 y) y) (g y) (g' y')"
    using Eq_absI rel_res[unfolded Eq_rel2] rel_res'[folded Eq_rel1, unfolded Eq_rel2] .
qed

lemma lifting_triple_if_related_fun_if_lifting_triple:
  assumes lift_trip: "lifting_triple T abs rep"
  and Eq_abs: "(Eq_rep T \<Rrightarrow> Eq_abs T) abs abs'"
  and Eq_rep: "(Eq_abs T \<Rrightarrow> Eq_rep T) rep rep'"
  shows "lifting_triple T abs' rep'"
proof (intro lifting_tripleI lifting_relation_if_z_property)
  show "z_property T" using z_property_if_lifting_triple lift_trip .
next
  fix x
  assume in_dom_x: "in_dom T x"
  have 1: "T x (abs x)"
    using lifting_triple_rel_abs_self_if_in_dom lift_trip in_dom_x .
  have 2: "Eq_abs T (abs x) (abs' x)"
    using Dep_Fun_RelD Eq_abs Eq_rep_self_if_in_dom in_dom_x .
  obtain x' where 3: "T x' (abs x)" "T x' (abs' x)"
    using Eq_absE 2 .
  show "T x (abs' x)"
    using z_propertyD' z_property_if_lifting_triple lift_trip 1 3 .
next
  fix y
  assume in_codom_y: "in_codom T y"
  have 1: "T (rep y) y"
    using lifting_triple_rel_rep_self_if_in_codom lift_trip in_codom_y .
  have 2: "Eq_rep T (rep y) (rep' y)"
    using Dep_Fun_RelD Eq_rep Eq_abs_self_if_in_codom in_codom_y .
  obtain y' where 3: "T (rep y) y'" "T (rep' y) y'"
    using Eq_repE 2 .
  show "T (rep' y) y"
    using z_propertyD' z_property_if_lifting_triple lift_trip 3(2, 1) 1 .
qed

(* Both, the transfer relation and the abstraction and representation function for the co-domains,
   may depend on the arguments, however they need to behave in an equivalent way for equivalent
   arguments. Intuitively, equivalent arguments map to equivalent transfer triples. In particular,
   this means, that the co-domain relation is fully determined by a single parameter since eg.
   \<forall>x y. T1 x y \<longrightarrow> T2 x y = T2 x (abs1 x). *)
lemma lifting_triple_Dep_Fun_RelI:
  assumes lift_trip1: "lifting_triple T1 abs1 rep1"
  and lift_trip2: "\<And>x y. T1 x y \<Longrightarrow> lifting_triple (T2 x y) (abs2 y x) (rep2 x y)"
  (* note swapped order of arguments for abs2 *)
  and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
  and rep2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow>
    (Eq_abs (T2 x y) \<Rrightarrow> Eq_rep (T2 x y)) (rep2 x y) (rep2 x' y')"
  and abs2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow>
    (Eq_rep (T2 x y) \<Rrightarrow> Eq_abs (T2 x y)) (abs2 y x) (abs2 y' x')"
  shows "lifting_triple (Dep_Fun_Rel T1 T2) (dep_fun_map rep1 abs2) (dep_fun_map abs1 rep2)"
proof (intro lifting_tripleI lifting_relation_if_z_property)
  show "z_property (Dep_Fun_Rel T1 T2)"
  proof (rule z_propertyI', rule Dep_Fun_RelI, (elim Dep_Fun_RelE, assumption)+)
    fix f1 g1 f2 g2 x y
    assume rel: "T1 x y"
       and fun_rels: "T2 x y (f1 x) (g1 y)" "T2 x y (f2 x) (g1 y)" "T2 x y (f2 x) (g2 y)"
    show "T2 x y (f1 x) (g2 y)"
      using z_propertyD' z_property_if_lifting_triple assms(2) rel fun_rels .
  qed
next
  fix f
  assume in_dom_f: "in_dom (Dep_Fun_Rel T1 T2) f"
  show "Dep_Fun_Rel T1 T2 f (dep_fun_map rep1 abs2 f)"
  proof (rule Dep_Fun_RelI)
    fix x y
    assume rel: "T1 x y"
    have 1: "Eq_rep T1 x (rep1 y)"
      using lifting_triple_Eq_rep_rep_if_rel lift_trip1 rel .
    have 2: "Eq_abs T1 y (abs1 x)"
      using symmetricD[OF symmetric_Eq_abs]
      lifting_triple_Eq_abs_abs_if_rel[OF lift_trip1 rel] .
    have 3: "T2 x y = T2 x (abs1 x)"
      using T2_resp rel Eq_rep_self_if_in_dom in_domI rel 2 .
    have 4: "Eq_rep (T2 x y) (f x) (f (rep1 y))"
      apply (subst 3)
      apply (rule Eq_rep_appI[of T1 _ _ T2])
      apply (fact lift_trip1 lift_trip2 T2_resp Eq_rep_self_if_in_dom[OF in_dom_f] 1)+
      done
    have 5: "lifting_triple (T2 x y) (abs2 y (rep1 y)) (rep2 x y)"
      using lifting_triple_if_related_fun_if_lifting_triple[OF lift_trip2, OF rel]
        abs2_resp[OF rel] 1 Eq_abs_self_if_in_codom in_codomI rel
        rep2_resp[OF rel] Eq_rep_self_if_in_dom in_domI rel Eq_abs_self_if_in_codom in_codomI rel .
    show "T2 x y (f x) (dep_fun_map rep1 abs2 f y)"
      unfolding dep_fun_map_def
      using lifting_triple_rel_abs_if_Eq_rep 5 4 .
  qed
next
  fix g
  assume in_codom_g: "in_codom (Dep_Fun_Rel T1 T2) g"
  show "Dep_Fun_Rel T1 T2 (dep_fun_map abs1 rep2 g) g"
  proof (rule Dep_Fun_RelI)
    fix x y
    assume rel: "T1 x y"
    have 1: "Eq_abs T1 y (abs1 x)"
      using symmetricD[OF symmetric_Eq_abs]
      lifting_triple_Eq_abs_abs_if_rel[OF lift_trip1 rel] .
    have 2: "Eq_rep T1 x (rep1 y)"
      using lifting_triple_Eq_rep_rep_if_rel lift_trip1 rel .
    have 3: "T2 x y = T2 (rep1 y) y"
      using T2_resp rel 2 Eq_abs_self_if_in_codom in_codomI rel .
    have 4: "Eq_abs (T2 x y) (g (abs1 x)) (g y)"
      apply (subst 3)
      apply (rule symmetricD[OF symmetric_Eq_abs])
      apply (rule Eq_abs_appI[of T1 _ _ T2])
      apply (fact lift_trip1 lift_trip2 T2_resp Eq_abs_self_if_in_codom[OF in_codom_g] 1)+
      done
    have 5: "lifting_triple (T2 x y) (abs2 y x) (rep2 x (abs1 x))"
      using lifting_triple_if_related_fun_if_lifting_triple[OF lift_trip2, OF rel]
        abs2_resp[OF rel] Eq_rep_self_if_in_dom in_domI rel Eq_abs_self_if_in_codom in_codomI rel
        rep2_resp[OF rel] Eq_rep_self_if_in_dom in_domI rel 1 .
    show "T2 x y (dep_fun_map abs1 rep2 g x) (g y)"
      unfolding dep_fun_map_def
      using lifting_triple_rel_rep_if_Eq_abs 5 4 .
  qed
qed

lemma lifting_triple_Dep_Fun_RelI':
  assumes lift_trip1: "lifting_triple T1 abs1 rep1"
  and lift_trip2: "\<And>x y. T1 x y \<Longrightarrow> lifting_triple (T2 x y) abs2 rep2"
  (* note swapped order of arguments for abs2 *)
  and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
  shows "lifting_triple (Dep_Fun_Rel T1 T2) (fun_map rep1 abs2) (fun_map abs1 rep2)"
  unfolding fun_map_def
  apply (rule lifting_triple_Dep_Fun_RelI)
  apply (fact lift_trip1)
  apply (fact lift_trip2)
    apply (fact T2_resp)
  unfolding Dep_Fun_Rel_def
   apply (rule allI)+ apply (rule impI)
  apply (rule lifting_triple_Eq_rep_rep_if_rel)
  apply (rule lift_trip2)
    apply assumption
  apply (rule lifting_triple_rel_rep_if_Eq_abs[OF lift_trip2])
    apply assumption+
   apply (rule allI)+ apply (rule impI)
  apply (rule lifting_triple_Eq_abs_abs_if_rel)
  apply (rule lift_trip2)
    apply assumption
  apply (rule lifting_triple_rel_abs_if_Eq_rep[OF lift_trip2])
   apply assumption
  apply assumption
  done

lemma lifting_triple_Fun_RelI:
  assumes lift_trip1: "lifting_triple T1 abs1 rep1"
      and lift_trip2: "lifting_triple T2 abs2 rep2"
    shows "lifting_triple (T1 \<Rrightarrow> T2) (fun_map rep1 abs2) (fun_map abs1 rep2)"
  unfolding fun_map_def
  apply (rule lifting_triple_Dep_Fun_RelI)
  apply (rule lift_trip1 lift_trip2 refl)+
   apply (rule Dep_Fun_RelI)
  apply (rule lifting_triple_Eq_rep_rep_rep_if_Eq_abs[OF lift_trip2], assumption)
   apply (rule Dep_Fun_RelI)
  apply (rule lifting_triple_Eq_abs_abs_abs_if_Eq_rep[OF lift_trip2], assumption)
  done

lemma rel_inv_Fun_Rel_eq_Fun_Rel_rel_inv:
  "rel_inv (T1 \<Rrightarrow> T2) = rel_inv T1 \<Rrightarrow> rel_inv T2"
  unfolding rel_inv_def Dep_Fun_Rel_def by blast

lemma Eq_rep_Fun_Rel_eq_Fun_Rel_Eq_repI:
  assumes "lifting_triple T1 abs1 rep1" and "lifting_triple T2 abs2 rep2"
  shows "Eq_rep (T1 \<Rrightarrow> T2) = Eq_rep T1 \<Rrightarrow> Eq_rep T2"
proof ((rule ext)+, rule iffI)
  fix f g
  assume prem1: "Eq_rep (T1 \<Rrightarrow> T2) f g"
  obtain h where h: "(T1 \<Rrightarrow> T2) f h" "(T1 \<Rrightarrow> T2) g h"
    using Eq_repE[OF prem1] by blast
  show "(Eq_rep T1 \<Rrightarrow> Eq_rep T2) f g"
  proof (rule Dep_Fun_RelI)
    fix x y
    assume prem2: "Eq_rep T1 x y"
    obtain z where z: "T1 x z" "T1 y z"
      using Eq_repE[OF prem2] by blast
    show "Eq_rep T2 (f x) (g y)"
      apply (rule Eq_repI)
      using Dep_Fun_RelD[OF h(1) z(1)] Dep_Fun_RelD[OF h(2) z(2)] .
  qed
next
  fix f g
  assume prem1: "(Eq_rep T1 \<Rrightarrow> Eq_rep T2) f g"
  define h where "h \<equiv> fun_map rep1 abs2 f"
  { fix x z
    assume rel_arg: "T1 x z"
    have 1: "Eq_rep T1 x (rep1 z)"
      using lifting_triple_Eq_rep_rep_if_rel assms(1) rel_arg .
    have 2: "Eq_rep T2 (f x) (g (rep1 z))"
      using Dep_Fun_RelD prem1 1 .
    have 3: "Eq_rep T2 (f x) (g x)"
      using Dep_Fun_RelD prem1 Eq_rep_self_if_in_dom in_domI rel_arg .
    have 4: "Eq_rep T2 (g x) (f (rep1 z))"
      using symmetricD[OF symmetric_Eq_rep] Dep_Fun_RelD prem1 symmetricD[OF symmetric_Eq_rep] 1 .
    have 5: "Eq_rep T2 (f x) (f (rep1 z))"
      using transitiveD partial_equivalence_transitive partial_equivalence_Eq_rep_if_z_property
        z_property_if_lifting_triple assms(2) 3 4 .
    have 6: "T2 (f (rep1 z)) (abs2 (f (rep1 z)))"
      using lifting_triple_rel_abs_self_if_in_dom assms(2) in_dom_if_Eq_rep symmetricD[OF symmetric_Eq_rep] 5 .
    have 7: "T2 (f x) (abs2 (f (rep1 z)))"
      apply (subst Eq_rep_rel_comp_eq_self_if_z_property[OF z_property_if_lifting_triple[OF assms(2)], symmetric])
      using rel_compI 5 6 .
    have "T2 (f x) (h z)"
      unfolding h_def fun_map_def dep_fun_map_def
      using 7 .
  }
  note 1 = this
  { fix x z
    assume rel_arg: "T1 x z"
    have 2: "T2 (f x) (h z)"
      using 1 rel_arg .
    have 3: "Eq_rep T2 (f x) (g x)"
      using Dep_Fun_RelD prem1 Eq_rep_self_if_in_dom in_domI rel_arg .
    have "T2 (g x) (h z)"
      apply (subst lifting_triple_Eq_rep_rel_comp_eq_self[OF assms(2), symmetric])
      using rel_compI symmetricD[OF symmetric_Eq_rep] 3 2 .
  }
  note 2 = this
  show "Eq_rep (T1 \<Rrightarrow> T2) f g"
    by (rule Eq_repI; rule Dep_Fun_RelI, fact 1 2)
qed

lemma Eq_abs_Fun_Rel_eq_Fun_Rel_Eq_absI:
  assumes "lifting_triple T1 abs1 rep1" and "lifting_triple T2 abs2 rep2"
  shows "Eq_abs (T1 \<Rrightarrow> T2) = Eq_abs T1 \<Rrightarrow> Eq_abs T2"
proof -
  have "Eq_abs (T1 \<Rrightarrow> T2) = Eq_rep (rel_inv (T1 \<Rrightarrow> T2))"
    apply (subst  Eq_rep_rel_inv_eq_Eq_abs) ..
  also have "... = Eq_rep (rel_inv T1 \<Rrightarrow> rel_inv T2)"
    apply (subst rel_inv_Fun_Rel_eq_Fun_Rel_rel_inv) ..
  also have "... = Eq_rep (rel_inv T1) \<Rrightarrow> Eq_rep (rel_inv T2)"
    apply (subst Eq_rep_Fun_Rel_eq_Fun_Rel_Eq_repI[OF
        lifting_triple_dual[OF assms(1)] lifting_triple_dual[OF assms(2)]]) ..
  also have "... = Eq_abs T1 \<Rrightarrow> Eq_abs T2"
    apply (subst  Eq_rep_rel_inv_eq_Eq_abs)+ ..
  finally show "Eq_abs (T1 \<Rrightarrow> T2) = Eq_abs T1 \<Rrightarrow> Eq_abs T2" .
qed

lemma z_property_if_all_dom_eq:
  assumes P_subst: "\<And>x x' y. P x y = P x' y"
  shows "z_property P"
proof (rule z_propertyI)
  fix x y x' y'
  assume rels: "P x y" "P x' y" "P x' y'"
  show "P x y'"
    apply (subst P_subst[of x y' x'])
    using rels(3) .
qed

lemma z_property_if_all_codom_eq:
  assumes P_subst: "\<And>x y y'. P x y = P x y'"
  shows "z_property P"
proof (rule z_propertyI)
  fix x y x' y'
  assume rels: "P x y" "P x' y" "P x' y'"
  show "P x y'"
    apply (subst P_subst[of x y' y])
    using rels(1) .
qed

lemma rel_comp: "((S \<Rrightarrow> T) \<Rrightarrow> (R \<Rrightarrow> S) \<Rrightarrow> R \<Rrightarrow> T) (\<circ>) (\<circ>)"
proof ((rule Dep_Fun_RelI)+, (subst comp_def)+)
  fix f f' g g' x x'
  assume rel_f: "(S \<Rrightarrow> T) f f'"
    and rel_g: "(R \<Rrightarrow> S) g g'"
    and rel_x: "R x x'"
  have rel_g_x: "S (g x) (g' x')"
    using Dep_Fun_RelD rel_g rel_x .
  show "T (f (g x)) (f' (g' x'))"
    using Dep_Fun_RelD rel_f rel_g_x .
qed

lemma z_property_if_rel_self:
  assumes eq: "(Eq_rep T \<Rrightarrow> Eq_abs T \<Rrightarrow> (=)) T T"
  shows "z_property T"
proof (rule z_propertyI)
  fix x y x' y'
  assume rels: "T x y" "T x' y" "T x' y'"
  have Eq_x_x: "Eq_rep T x x"
    using Eq_repI rels(1, 1) .
  have Eq_y'_y: "Eq_abs T y' y"
    using Eq_absI rels (3, 2) .
  show "T x y'"
    apply (subst Dep_Fun_RelD[OF Dep_Fun_RelD[OF eq], OF  Eq_x_x Eq_y'_y])
    using rels(1) .
qed

lemma in_dom_Fun_Rel_iff_if_lifting_triples:
  assumes "lifting_triple T1 abs1 rep1" "lifting_triple T2 abs2 rep2"
  shows "in_dom (T1 \<Rrightarrow> T2) f \<longleftrightarrow> (\<forall>x1 x2. Eq_rep T1 x1 x2 \<longrightarrow> Eq_rep T2 (f x1) (f x2))"
  apply (subst Eq_rep_self_eq_in_dom[symmetric])
  apply (subst Eq_rep_Fun_Rel_eq_Fun_Rel_Eq_repI[OF assms])
  unfolding Dep_Fun_Rel_def ..

lemma in_dom_Fun_Rel_if_Eq_rep_if_lifting_triples:
  assumes "lifting_triple T1 abs1 rep1" "lifting_triple T2 abs2 rep2"
  and "\<And>x1 x2. Eq_rep T1 x1 x2 \<Longrightarrow> Eq_rep T2 (f x1) (f x2)"
  shows "in_dom (T1 \<Rrightarrow> T2) f"
  using assms in_dom_Fun_Rel_iff_if_lifting_triples by fast

lemma in_dom_Fun_Rel_if_Eq_rep_if_lifting_triples':
  assumes "lifting_triple T1 abs1 rep1" "lifting_triple T2 abs2 rep2"
  and "left_unique T1"
  and "\<And>x. in_dom T1 x \<Longrightarrow> in_dom T2 (f x)"
  shows "in_dom (T1 \<Rrightarrow> T2) f"
  apply (rule in_dom_Fun_Rel_if_Eq_rep_if_lifting_triples)
    apply (fact assms)+
proof -
  fix x1 x2
  assume prem: "Eq_rep T1 x1 x2"
  obtain y where 1: "T1 x1 y"
    using Eq_repE prem .
  have 2: "in_dom T1 x1"
    using in_domI 1 .
  have 3: "in_dom T2 (f x1)"
    using assms(4) 2 .
  have 4: "x1 = x2"
    using assms(3) prem left_unique_def by fast
  show "Eq_rep T2 (f x1) (f x2)"
    apply (subst 4[symmetric])
    using Eq_rep_self_if_in_dom[OF 3] .
qed


end