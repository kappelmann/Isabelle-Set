theory Function
  imports Basic_T
begin

definition dep_rel_fun ::
    "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool"
  where "dep_rel_fun T1 T2 f g \<equiv> (\<forall>x y. T1 x y \<longrightarrow> T2 x y (f x) (g y))"

definition no_dep_rel_fun ::
    "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool"
  where "no_dep_rel_fun T1 T2 \<equiv> dep_rel_fun T1 (\<lambda>_ _. T2)"

syntax
  "_no_dep_rel_fun" :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> 'c) \<Rightarrow>
    ('b \<Rightarrow> 'd) \<Rightarrow> bool)" ("(_) \<Rrightarrow> (_)" [101, 100] 100)
  "_dep_rel_fun" :: "idt \<Rightarrow> idt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
    (('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> bool)" ("[_/ _/ \<Colon>/ _] \<Rrightarrow> (_)" [101, 101, 101, 100] 100)
translations
  "R \<Rrightarrow> S" \<rightleftharpoons> "CONST no_dep_rel_fun R S"
  "[x y \<Colon> R] \<Rrightarrow> S" \<rightleftharpoons> "CONST dep_rel_fun R (\<lambda>x y. S)"

term "R \<Rrightarrow> S"
term "[x y \<Colon> R] \<Rrightarrow> S x y"

lemma dep_rel_funE: "\<lbrakk>([x y \<Colon> R] \<Rrightarrow> S x y) f g; R x y\<rbrakk> \<Longrightarrow> S x y (f x) (g y)"
  unfolding dep_rel_fun_def by blast

lemma dep_rel_funI: "(\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)) \<Longrightarrow> ([x y \<Colon> R] \<Rrightarrow> S x y) f g"
  unfolding dep_rel_fun_def by blast

lemma no_dep_rel_funE: "(R \<Rrightarrow> S) f g \<Longrightarrow> R x y \<Longrightarrow> S (f x) (g y)"
  unfolding no_dep_rel_fun_def dep_rel_fun_def
  by blast

lemma no_dep_rel_funI: "(\<And>x y. R x y \<Longrightarrow> S (f x) (g y)) \<Longrightarrow> (R \<Rrightarrow> S) f g"
  unfolding no_dep_rel_fun_def dep_rel_fun_def
  by blast

definition rel_rest :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
    ("[_ | _]" [102, 102] 101)
    where "rel_rest R p \<equiv> (\<lambda>x y. R x y \<and> p x y)"

lemma rel_restI: "\<lbrakk>T x y; P x y\<rbrakk> \<Longrightarrow> rel_rest T P x y"
  unfolding rel_rest_def by simp

lemma rel_restE: "rel_rest T P x y \<Longrightarrow> (\<lbrakk>T x y; P x y\<rbrakk> \<Longrightarrow> Q) \<Longrightarrow> Q"
  unfolding rel_rest_def by simp

definition rel_weak :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
    ("[_ \<longrightarrow> _]" [102, 102] 101)
  where "rel_weak P R \<equiv> (\<lambda>x y. P \<longrightarrow> R x y)"

definition rel_weak_rest :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
    ("[_ \<longrightarrow> _ | _]" [102, 102] 101)
  where "rel_weak_rest P R Q \<equiv> (\<lambda>x y. P \<longrightarrow> R x y \<and> Q x y)"

term "[R | p]"
term "[p \<longrightarrow> R]"
term "[p \<longrightarrow> R | q]"

term "[x1 y1 \<Colon> [R1 | q1]] \<Rrightarrow> [x2 y2 \<Colon> [p2 x1 y1 \<longrightarrow> R2]] \<Rrightarrow> [R3 | q3 x1 y1 x2 y2]"
term "x1 y1 \<Colon> [R1 | p]"
term "x1 y1 \<Colon> [R1 | (\<lambda>x y. p x)]"

lemma z_property_no_dep_fun_rel:
  assumes "z_property T1"
      and "z_property T2"
    shows "z_property (T1 \<Rrightarrow> T2)"
  apply (rule z_propertyI)
  apply (rule no_dep_rel_funI)
  apply (drule no_dep_rel_funE, assumption)+
  using z_propertyE[OF assms(2)]
  by blast

definition dep_map_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'd"
  where "dep_map_fun f g h x \<equiv> g x (f x) (h (f x))"

definition map_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'd"
  where "map_fun f g h \<equiv> dep_map_fun f (\<lambda>_ _. g) h"

lemma map_fun_simp: "map_fun f g h \<equiv> g \<circ> h \<circ> f"
  unfolding map_fun_def dep_map_fun_def comp_def .

lemma Eq_rep_app:
  assumes trans_trip1: "transfer_triple T1 abs1 rep1"
      and trans_trip2: "\<And>x y. T1 x y \<Longrightarrow> transfer_triple (T2 x y) (abs2 y x) (rep2 x y)"
      and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
      and Eq_fun: "Eq_rep (dep_rel_fun T1 T2) f f'"
      and Eq_arg: "Eq_rep T1 x x'"
    shows "Eq_rep (T2 x (abs1 x)) (f x) (f' x')"
proof -
  obtain g where rel_fun: "dep_rel_fun T1 T2 f g" "dep_rel_fun T1 T2 f' g"
    using Eq_repE' Eq_fun .
  obtain y where rel_arg: "T1 x y" "T1 x' y"
    using Eq_repE' Eq_arg .
  have Eq_abs_abs_x_y: "Eq_abs T1 (abs1 x) y"
    using Eq_absI rel_abs trans_trip1 in_domI rel_arg(1, 1) .
  have rel_res: "T2 x y (f x) (g y)"
    using dep_rel_funE rel_fun(1) rel_arg(1) .
  have rel_res': "T2 x' y (f' x') (g y)"
    using dep_rel_funE rel_fun(2) rel_arg(2) .
  have Eq_rel1: "T2 x y = T2 x' y"
    using T2_resp rel_arg(1) Eq_arg Eq_abs_self in_co_domI rel_arg(1) .
  have Eq_rel2: "T2 x y = T2 x (abs1 x)"
    using T2_resp rel_arg(1) Eq_rep_self in_domI rel_arg(1) Eq_abs_sym Eq_abs_abs_x_y .
  show " Eq_rep (T2 x (abs1 x)) (f x) (f' x')"
    using Eq_repI rel_res[unfolded Eq_rel2] rel_res'[folded Eq_rel1, unfolded Eq_rel2] .
qed

lemma Eq_abs_app:
  assumes trans_trip1: "transfer_triple T1 abs1 rep1"
      and trans_trip2: "\<And>x y. T1 x y \<Longrightarrow> transfer_triple (T2 x y) (abs2 y x) (rep2 x y)"
      and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
      and Eq_fun: "Eq_abs (dep_rel_fun T1 T2) g g'"
      and Eq_arg: "Eq_abs T1 y y'"
    shows "Eq_abs (T2 (rep1 y) y) (g y) (g' y')"
proof -
  obtain f where rel_fun: "dep_rel_fun T1 T2 f g" "dep_rel_fun T1 T2 f g'"
    using Eq_absE' Eq_fun .
  obtain x where rel_arg: "T1 x y" "T1 x y'"
    using Eq_absE' Eq_arg .
  have Eq_rep_x_rep_y: "Eq_rep T1 x (rep1 y)"
    using Eq_repI rel_arg(1) rel_rep trans_trip1 in_co_domI rel_arg(1) .
  have rel_res: "T2 x y (f x) (g y)"
    using dep_rel_funE rel_fun(1) rel_arg(1) .
  have rel_res': "T2 x y' (f x) (g' y')"
    using dep_rel_funE rel_fun(2) rel_arg(2) .
  have Eq_rel1: "T2 x y = T2 x y'"
    using T2_resp rel_arg(1) Eq_rep_self in_domI rel_arg(1) Eq_arg .
  have Eq_rel2: "T2 x y = T2 (rep1 y) y"
    using T2_resp rel_arg(1) Eq_rep_x_rep_y Eq_abs_self in_co_domI rel_arg(1) .
  show "Eq_abs (T2 (rep1 y) y) (g y) (g' y')"
    using Eq_absI rel_res[unfolded Eq_rel2] rel_res'[folded Eq_rel1, unfolded Eq_rel2] .
qed

lemma Eq_rep_abs_transfer_triple:
  assumes trans_trip: "transfer_triple T abs rep"
      and Eq_abs: "(Eq_rep T \<Rrightarrow> Eq_abs T) abs abs'"
      and Eq_rep: "(Eq_abs T \<Rrightarrow> Eq_rep T) rep rep'"
    shows "transfer_triple T abs' rep'"
proof (rule transfer_tripleI)
  show "z_property T"
    using z_property_transfer_triple trans_trip .
next
  fix x
  assume in_dom_x: "in_dom T x"
  have 1: "T x (abs x)"
    using rel_abs trans_trip in_dom_x .
  have 2: "Eq_abs T (abs x) (abs' x)"
    using no_dep_rel_funE Eq_abs Eq_rep_self in_dom_x .
  obtain x' where 3: "T x' (abs x)" "T x' (abs' x)"
    using Eq_absE' 2 .
  show "T x (abs' x)"
    using z_propertyE z_property_transfer_triple trans_trip 1 3 .
next
  fix y
  assume in_co_dom_y: "in_co_dom T y"
  have 1: "T (rep y) y"
    using rel_rep trans_trip in_co_dom_y .
  have 2: "Eq_rep T (rep y) (rep' y)"
    using no_dep_rel_funE Eq_rep Eq_abs_self in_co_dom_y .
  obtain y' where 3: "T (rep y) y'" "T (rep' y) y'"
    using Eq_repE' 2 .
  show "T (rep' y) y"
    using z_propertyE z_property_transfer_triple trans_trip 3(2, 1) 1 .
qed

(* Both, the transfer relation and the abstraction and representation function for the co-domains,
   may depend on the arguments, however they need to behave in an equivalent way for equivalent
   arguments. Intuitively, equivalent arguments map to equivalent transfer triples. In particular,
   this means, that the co-domain relation is fully determined by a single parameter since eg.
   \<forall>x y. T1 x y \<longrightarrow> T2 x y = T2 x (abs1 x). *)
lemma fun_transfer_triple:
  assumes trans_trip1: "transfer_triple T1 abs1 rep1"
      and trans_trip2: "\<And>x y. T1 x y \<Longrightarrow> transfer_triple (T2 x y) (abs2 y x) (rep2 x y)"
          (* note swapped order of arguments for abs2 *)
      and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
      and rep2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> (Eq_abs (T2 x y) \<Rrightarrow> Eq_rep (T2 x y)) (rep2 x y) (rep2 x' y')"
      and abs2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> (Eq_rep (T2 x y) \<Rrightarrow> Eq_abs (T2 x y)) (abs2 y x) (abs2 y' x')"
  shows "transfer_triple (dep_rel_fun T1 T2) (dep_map_fun rep1 abs2) (dep_map_fun abs1 rep2)"
proof (rule transfer_tripleI)
  show "z_property (dep_rel_fun T1 T2)"
  proof (rule z_propertyI, rule dep_rel_funI, (drule dep_rel_funE, assumption)+)
    fix f1 g1 f2 g2 x y
    assume rel: "T1 x y"
       and fun_rels: "T2 x y (f1 x) (g1 y)" "T2 x y (f2 x) (g1 y)" "T2 x y (f2 x) (g2 y)"
    show "T2 x y (f1 x) (g2 y)"
      using z_propertyE z_property_transfer_triple assms(2) rel fun_rels .
  qed
next
  fix f
  assume in_dom_f: "in_dom (dep_rel_fun T1 T2) f"
  show "dep_rel_fun T1 T2 f (dep_map_fun rep1 abs2 f)"
  proof (rule dep_rel_funI)
    fix x y
    assume rel: "T1 x y"
    have 1: "Eq_rep T1 x (rep1 y)"
      using Eq_rep_rep trans_trip1 rel .
    have 2: "Eq_abs T1 y (abs1 x)"
      using Eq_abs_abs trans_trip1 rel .
    have 3: "T2 x y = T2 x (abs1 x)"
      using T2_resp rel Eq_rep_self in_domI rel 2 .
    have 4: "Eq_rep (T2 x y) (f x) (f (rep1 y))"
      apply (subst 3)
      apply (rule Eq_rep_app[of T1 _ _ T2])
      apply (fact trans_trip1 trans_trip2 T2_resp Eq_rep_self[OF in_dom_f] 1)+
      done
    have 5: "transfer_triple (T2 x y) (abs2 y (rep1 y)) (rep2 x y)"
      using Eq_rep_abs_transfer_triple[OF trans_trip2, OF rel]
        abs2_resp[OF rel] 1 Eq_abs_self in_co_domI rel
        rep2_resp[OF rel] Eq_rep_self in_domI rel Eq_abs_self in_co_domI rel .
    show "T2 x y (f x) (dep_map_fun rep1 abs2 f y)"
      unfolding dep_map_fun_def
      using rel_abs' 5 4 .
  qed
next
  fix g
  assume in_co_dom_g: "in_co_dom (dep_rel_fun T1 T2) g"
  show "dep_rel_fun T1 T2 (dep_map_fun abs1 rep2 g) g"
  proof (rule dep_rel_funI)
    fix x y
    assume rel: "T1 x y"
    have 1: "Eq_abs T1 y (abs1 x)"
      using Eq_abs_abs trans_trip1 rel .
    have 2: "Eq_rep T1 x (rep1 y)"
      using Eq_rep_rep trans_trip1 rel .
    have 3: "T2 x y = T2 (rep1 y) y"
      using T2_resp rel 2 Eq_abs_self in_co_domI rel .
    have 4: "Eq_abs (T2 x y) (g (abs1 x)) (g y)"
      apply (subst 3)
      apply (rule Eq_abs_sym)
      apply (rule Eq_abs_app[of T1 _ _ T2])
      apply (fact trans_trip1 trans_trip2 T2_resp Eq_abs_self[OF in_co_dom_g] 1)+
      done
    have 5: "transfer_triple (T2 x y) (abs2 y x) (rep2 x (abs1 x))"
      using Eq_rep_abs_transfer_triple[OF trans_trip2, OF rel]
        abs2_resp[OF rel] Eq_rep_self in_domI rel Eq_abs_self in_co_domI rel
        rep2_resp[OF rel] Eq_rep_self in_domI rel 1 .
    show "T2 x y (dep_map_fun abs1 rep2 g x) (g y)"
      unfolding dep_map_fun_def
      using rel_rep' 5 4 .
  qed
qed

lemma fun_transfer_triple':
  assumes trans_trip1: "transfer_triple T1 abs1 rep1"
      and trans_trip2: "\<And>x y. T1 x y \<Longrightarrow> transfer_triple (T2 x y) abs2 rep2"
          (* note swapped order of arguments for abs2 *)
      and T2_resp: "\<And>x x' y y'. \<lbrakk>T1 x y; Eq_rep T1 x x'; Eq_abs T1 y y'\<rbrakk> \<Longrightarrow> T2 x y = T2 x' y'"
    shows "transfer_triple (dep_rel_fun T1 T2) (map_fun rep1 abs2) (map_fun abs1 rep2)"
  unfolding map_fun_def
  apply (rule fun_transfer_triple)
  apply (fact trans_trip1)
  apply (fact trans_trip2)
    apply (fact T2_resp)
  unfolding no_dep_rel_fun_def dep_rel_fun_def
   apply (rule allI)+ apply (rule impI)
  apply (rule Eq_rep_rep)
  apply (rule trans_trip2)
    apply assumption
  apply (rule rel_rep'[OF trans_trip2])
    apply assumption+
   apply (rule allI)+ apply (rule impI)
  apply (rule Eq_abs_abs)
  apply (rule trans_trip2)
    apply assumption
  apply (rule rel_abs'[OF trans_trip2])
   apply assumption
  apply (rule partial_equivalence_sym[OF partial_equivalence_Eq_rep, OF z_property_transfer_triple, OF trans_trip2])
  apply assumption+
  done

lemma rel_comp_Eq_abs:
  assumes trans_trip: "transfer_triple T abs rep"
  shows "T \<circ>\<circ> Eq_abs T = T"
proof ((rule ext)+, rule iffI)
  fix x y
  assume prem: "(T \<circ>\<circ> Eq_abs T) x y"
  obtain y' where T_x_y: "T x y'" and Eq_y'_y: "Eq_abs T y' y"
    using rel_compE prem .
  obtain x' where T_x'_y': "T x' y'" and T_x'_y: "T x' y"
    using Eq_absE' Eq_y'_y .
  show "T x y"
    using z_propertyE z_property_transfer_triple trans_trip T_x_y T_x'_y' T_x'_y .
next
  fix x y
  assume rel: "T x y"
  show "(T \<circ>\<circ> Eq_abs T) x y"
    using rel_compI rel Eq_abs_self in_co_domI rel .
qed

lemma Eq_rep_rep_comp:
  assumes trans_trip: "transfer_triple T abs rep"
  shows "Eq_rep T \<circ>\<circ> T = T"
proof -
  have "rel_inv T \<circ>\<circ> Eq_abs (rel_inv T) = rel_inv T"
    using rel_comp_Eq_abs[OF transfer_triple_dual[OF trans_trip]] .
  hence "rel_inv T \<circ>\<circ> Eq_rep T = rel_inv T"
    unfolding Eq_abs_inv_simp .
  hence "rel_inv T \<circ>\<circ> rel_inv (Eq_rep T) = rel_inv T"
    apply (subst symmetric_then_eq_rel_inv_self[OF symmetric_Eq_rep]) .
  hence "rel_inv ((Eq_rep T) \<circ>\<circ> T)  = rel_inv T"
    unfolding rel_inv_comp_dist .
  thus "Eq_rep T \<circ>\<circ> T = T"
    by (rule eq_rel_inv_simp)
qed

lemma rel_Eq_abs:
  assumes trans_trip: "transfer_triple T abs rep"
    and rel: "T x y"
      and eq: "Eq_abs T y y'"
    shows "T x y'"
  apply (subst rel_comp_Eq_abs[OF trans_trip, symmetric])
  using rel_compI rel eq .

lemma Eq_arg_abs:
  assumes trans_trip: "transfer_triple T abs rep"
      and eq: "Eq_rep T x x'"
    shows "Eq_abs T (abs x) (abs x')"
proof -
  obtain y where rels: "T x y" "T x' y"
    using Eq_repE' eq .
  have rel_abs1: "T x (abs x)"
    using rel_abs trans_trip Eq_rep_then_in_dom eq .
  have rel_abs2: "T x' (abs x')"
    using rel_abs trans_trip Eq_rep_then_in_dom Eq_rep_sym eq .
  have  eq_abs1: "Eq_abs T (abs x) y"
    using Eq_absI rel_abs1 rels(1) .
  have eq_abs2: "Eq_abs T y (abs x')"
    using Eq_absI rels(2) rel_abs2 .
  show "Eq_abs T (abs x) (abs x')"
    using partial_equivalence_trans partial_equivalnce_Eq_abs z_property_transfer_triple
      trans_trip eq_abs1 eq_abs2 .
qed

lemma Eq_arg_rep:
  assumes trans_trip: "transfer_triple T abs rep"
      and eq: "Eq_abs T y y'"
    shows "Eq_rep T (rep y) (rep y')"
proof -
  show "Eq_rep T (rep y) (rep y')"
    apply (subst Eq_abs_inv_simp[symmetric])
    using Eq_arg_abs transfer_triple_dual[OF trans_trip] eq[folded Eq_rep_inv_simp] .
qed

lemma no_dep_fun_transfer_triple:
  assumes trans_trip1: "transfer_triple T1 abs1 rep1"
      and trans_trip2: "transfer_triple T2 abs2 rep2"
    shows "transfer_triple (T1 \<Rrightarrow> T2) (map_fun rep1 abs2) (map_fun abs1 rep2)"
  unfolding no_dep_rel_fun_def map_fun_def
  apply (rule fun_transfer_triple)
  apply (rule trans_trip1 trans_trip2 refl)+
   apply (rule no_dep_rel_funI)
  apply (rule Eq_arg_rep[OF trans_trip2], assumption)
   apply (rule no_dep_rel_funI)
  apply (rule Eq_arg_abs[OF trans_trip2], assumption)
  done

lemma rel_inv_no_dep_rel_fun_dist: "rel_inv (T1 \<Rrightarrow> T2) = rel_inv T1 \<Rrightarrow> rel_inv T2"
  unfolding rel_inv_def no_dep_rel_fun_def dep_rel_fun_def by blast

lemma Eq_rep_no_dep_rel_fun_dist:
  assumes "transfer_triple T1 abs1 rep1" and "transfer_triple T2 abs2 rep2"
  shows "Eq_rep (T1 \<Rrightarrow> T2) = Eq_rep T1 \<Rrightarrow> Eq_rep T2"
proof ((rule ext)+, rule iffI)
  fix f g
  assume prem1: "Eq_rep (T1 \<Rrightarrow> T2) f g"
  obtain h where h: "(T1 \<Rrightarrow> T2) f h" "(T1 \<Rrightarrow> T2) g h"
    using Eq_repE[OF prem1] by blast
  show "(Eq_rep T1 \<Rrightarrow> Eq_rep T2) f g"
  proof (rule no_dep_rel_funI)
    fix x y
    assume prem2: "Eq_rep T1 x y"
    obtain z where z: "T1 x z" "T1 y z"
      using Eq_repE[OF prem2] by blast
    show "Eq_rep T2 (f x) (g y)"
      apply (rule Eq_repI)
      using no_dep_rel_funE[OF h(1) z(1)] no_dep_rel_funE[OF h(2) z(2)] .
  qed
next
  fix f g
  assume prem1: "(Eq_rep T1 \<Rrightarrow> Eq_rep T2) f g"
  define h where "h \<equiv> map_fun rep1 abs2 f"
  { fix x z
    assume rel_arg: "T1 x z"
    have 1: "Eq_rep T1 x (rep1 z)"
      using Eq_rep_rep assms(1) rel_arg .
    have 2: "Eq_rep T2 (f x) (g (rep1 z))"
      using no_dep_rel_funE prem1 1 .
    have 3: "Eq_rep T2 (f x) (g x)"
      using no_dep_rel_funE prem1 Eq_rep_self in_domI rel_arg .
    have 4: "Eq_rep T2 (g x) (f (rep1 z))"
      using  Eq_rep_sym no_dep_rel_funE prem1 Eq_rep_sym 1 .
    have 5: "Eq_rep T2 (f x) (f (rep1 z))"
      using partial_equivalence_trans partial_equivalence_Eq_rep z_property_transfer_triple assms(2) 3 4 .
    have 6: "T2 (f (rep1 z)) (abs2 (f (rep1 z)))"
      using rel_abs assms(2) Eq_rep_then_in_dom Eq_rep_sym 5 .
    have 7: "T2 (f x) (abs2 (f (rep1 z)))"
      apply (subst  Eq_rep_rep_comp[OF assms(2), symmetric])
      using rel_compI 5 6 .
    have "T2 (f x) (h z)"
      unfolding h_def map_fun_def dep_map_fun_def
      using 7 .
  }
  note 1 = this
  { fix x z
    assume rel_arg: "T1 x z"
    have 2: "T2 (f x) (h z)"
      using 1 rel_arg .
    have 3: "Eq_rep T2 (f x) (g x)"
      using no_dep_rel_funE prem1 Eq_rep_self in_domI rel_arg .
    have "T2 (g x) (h z)"
      apply (subst Eq_rep_rep_comp[OF assms(2), symmetric])
      using rel_compI Eq_rep_sym 3 2 .
  }
  note 2 = this
  show "Eq_rep (T1 \<Rrightarrow> T2) f g"
    by (rule Eq_repI; rule no_dep_rel_funI, fact 1 2)
qed

lemma Eq_abs_no_dep_rel_fun_dist:
  assumes "transfer_triple T1 abs1 rep1" and "transfer_triple T2 abs2 rep2"
  shows "Eq_abs (T1 \<Rrightarrow> T2) = Eq_abs T1 \<Rrightarrow> Eq_abs T2"
proof -
  have "Eq_abs (T1 \<Rrightarrow> T2) = Eq_rep (rel_inv (T1 \<Rrightarrow> T2))"
    apply (subst Eq_rep_inv_simp) ..
  also have "... = Eq_rep (rel_inv T1 \<Rrightarrow> rel_inv T2)"
    apply (subst rel_inv_no_dep_rel_fun_dist) ..
  also have "... = Eq_rep (rel_inv T1) \<Rrightarrow> Eq_rep (rel_inv T2)"
    apply (subst Eq_rep_no_dep_rel_fun_dist[OF
        transfer_triple_dual[OF assms(1)] transfer_triple_dual[OF assms(2)]]) ..
  also have "... = Eq_abs T1 \<Rrightarrow> Eq_abs T2"
    apply (subst Eq_rep_inv_simp)+ ..
  finally show "Eq_abs (T1 \<Rrightarrow> T2) = Eq_abs T1 \<Rrightarrow> Eq_abs T2" .
qed

lemma z_property_rel_rest:
  assumes z_prop_T: "z_property T"
    and z_prop_P: "z_property P"
  shows "z_property (rel_rest T P)"
  apply (rule z_propertyI)
  using z_propertyE[OF z_prop_T] z_propertyE[OF z_prop_P]
  unfolding rel_rest_def
  by blast

lemma indep_fst_then_z_property:
  assumes P_subst: "\<And>x x' y. P x y = P x' y"
  shows "z_property P"
proof (rule z_propertyI)
  fix x y x' y'
  assume rels: "P x y" "P x' y" "P x' y'"
  show "P x y'"
    apply (subst P_subst[of x y' x'])
    using rels(3) .
qed

lemma indep_snd_then_z_property:
  assumes P_subst: "\<And>x y y'. P x y = P x y'"
  shows "z_property P"
proof (rule z_propertyI)
  fix x y x' y'
  assume rels: "P x y" "P x' y" "P x' y'"
  show "P x y'"
    apply (subst P_subst[of x y' y])
    using rels(1) .
qed

lemma rel_rest_transfer_triple:
  assumes trans_trip: "transfer_triple T abs rep"
    and eq: "(Eq_rep T \<Rrightarrow> Eq_abs T \<Rrightarrow> (=)) P P"
  shows "transfer_triple (rel_rest T P) abs rep"
proof (rule transfer_tripleI)
  show "z_property (rel_rest T P)"
  proof (rule z_propertyI)
  fix x y x' y'
  assume rels: "rel_rest T P x y" "rel_rest T P x' y" "rel_rest T P x' y'"
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
    using z_propertyE z_property_transfer_triple[OF trans_trip] rels
    unfolding rel_rest_def
    by fast
  show "rel_rest T P x y'"
    apply (rule rel_restI)
    apply (fact T_x_y')
    apply (rule rel_restE[OF rels(1)])
    unfolding no_dep_rel_funE[OF no_dep_rel_funE[OF eq], OF Eq_rep_self[OF in_dom_T_x] Eq_abs_y_y'] .
qed
next
  fix x
  assume in_dom_rel_rest_x: "in_dom (rel_rest T P) x"
  obtain y where rel_rest_x_y: "rel_rest T P x y"
    using in_domE in_dom_rel_rest_x .
  have in_dom_T_x: "in_dom T x"
    apply (rule in_domI)
    by (rule rel_restE[OF rel_rest_x_y], assumption) 
  have T_x_abs_x: "T x (abs x)"
    by (fact rel_abs[OF trans_trip, OF in_dom_T_x])
  have T_x_y: "T x y" and P_x_y: "P x y"
    by (rule rel_restE[OF rel_rest_x_y], assumption)+
  have Eq_abs_abs_x_y: "Eq_abs T (abs x) y"
    using Eq_absI T_x_abs_x T_x_y .
  show "rel_rest T P x (abs x)"
    apply (rule rel_restI)
    using no_dep_rel_funE[OF no_dep_rel_funE[OF eq], OF Eq_rep_self[OF in_dom_T_x] Eq_abs_abs_x_y]
      T_x_abs_x P_x_y
    by simp+
next
  fix y
  assume in_co_dom_rel_rest_y: "in_co_dom (rel_rest T P) y"
  obtain x where rel_rest_x_y: "rel_rest T P x y"
    using in_co_domE in_co_dom_rel_rest_y .
  have in_co_dom_T_y: "in_co_dom T y"
    apply (rule in_co_domI)
    by (rule rel_restE[OF rel_rest_x_y], assumption) 
  have T_rep_y_y: "T (rep y) y"
    by (fact rel_rep[OF trans_trip, OF in_co_dom_T_y])
  have T_x_y: "T x y" and P_x_y: "P x y"
    by (rule rel_restE[OF rel_rest_x_y], assumption)+
  have Eq_rep_rep_y_x: "Eq_rep T (rep y) x"
    using Eq_repI T_rep_y_y T_x_y .
  show "rel_rest T P (rep y) y"
    apply (rule rel_restI)
    using no_dep_rel_funE[OF no_dep_rel_funE[OF eq], OF Eq_rep_rep_y_x Eq_abs_self[OF in_co_dom_T_y]]
      T_rep_y_y P_x_y
    by simp+
qed

lemma rel_comp: "((S \<Rrightarrow> T) \<Rrightarrow> (R \<Rrightarrow> S) \<Rrightarrow> R \<Rrightarrow> T) (\<circ>) (\<circ>)"
proof ((rule no_dep_rel_funI)+, (subst comp_def)+)
  fix f f' g g' x x'
  assume rel_f: "(S \<Rrightarrow> T) f f'"
    and rel_g: "(R \<Rrightarrow> S) g g'"
    and rel_x: "R x x'"
  have rel_g_x: "S (g x) (g' x')"
    using no_dep_rel_funE rel_g rel_x .
  show "T (f (g x)) (f' (g' x'))"
    using no_dep_rel_funE rel_f rel_g_x .
qed

lemma
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
    apply (subst no_dep_rel_funE[OF no_dep_rel_funE[OF eq], OF  Eq_x_x Eq_y'_y])
    using rels(1) .
qed

end