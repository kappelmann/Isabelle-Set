theory Function
  imports Basic
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

lemma no_dep_rel_funE: "(R \<Rrightarrow> S) f g \<Longrightarrow> R x y \<Longrightarrow> S (f x) (g y)"
  unfolding no_dep_rel_fun_def dep_rel_fun_def
  by blast

lemma no_dep_rel_funI: "(\<And>x y. R x y \<Longrightarrow> S (f x) (g y)) \<Longrightarrow> (R \<Rrightarrow> S) f g"
  unfolding no_dep_rel_fun_def dep_rel_fun_def
  by blast

definition rel_rest :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"
    ("[_ | _]" [102, 102] 101)
  where "rel_rest R p \<equiv> (\<lambda>x y. R x y \<and> p x y)"

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

lemma Eq_rep_app:
  assumes trans_trip1: "transfer_triple T1 abs1 rep1"
      and trans_trip2: "transfer_triple T2 abs2 rep2"
      and Eq_rep_fun: "Eq_rep (T1 \<Rrightarrow> T2) f f'"
      and Eq_rep_arg: "Eq_rep T1 x x'"
  shows "Eq_rep T2 (f x) (f' x')"
proof -
  obtain y where rel_arg: "T1 x y" "T1 x' y"
    using Eq_rep_arg Eq_repE by fast
  obtain g where rel_fun: "(T1 \<Rrightarrow> T2) f g" "(T1 \<Rrightarrow> T2) f' g"
    using Eq_rep_fun Eq_repE by fast
  show "Eq_rep T2 (f x) (f' x')"
    apply (rule Eq_repI)
      using no_dep_rel_funE[OF rel_fun(1) rel_arg(1)] no_dep_rel_funE[OF rel_fun(2) rel_arg(2)] .
  qed

lemma
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
  { fix x y
    assume "Eq_rep T1 x y"
    hence "Eq_rep T2 (f x) (g y)"
      using no_dep_rel_funE[OF prem1] by simp
  }
  note 1 = this
  { fix x y
    assume prem2: "Eq_rep T1 x y"
    obtain z where z: "T2 (f x) z" "T2 (g y) z"
      using Eq_repE[OF 1, of x y, OF prem2] by blast
    hence "\<exists>h. T2 (f x) (h x) \<and> T2 (g y) (h y)" by auto
  }
  note 2 = this
  obtain h where h: "(T1 \<Rrightarrow> T2) f h" "(T1 \<Rrightarrow> T2) g h"
    using 2 Eq_repI Eq_repE no_dep_rel_funE[OF prem1]
    sorry
  show "Eq_rep (T1 \<Rrightarrow> T2) f g"
    apply (rule Eq_repI)
    using h .
qed

lemma fun_lifting:
  assumes "transfer_triple T1 abs1 rep1" and "transfer_triple T2 abs2 rep2"
  shows "transfer_triple (T1 \<Rrightarrow> T2) (map_fun rep1 abs2) (map_fun abs1 rep2)"
proof (rule transfer_tripleI)
  show "z_property (T1 \<Rrightarrow> T2)"
   apply (rule z_property_no_dep_fun_rel)
     apply (rule z_property_transfer_triple, fact assms)+
    done
next
  fix f
  assume prem1: "in_dom (T1 \<Rrightarrow> T2) f"
  show "(T1 \<Rrightarrow> T2) f (map_fun rep1 abs2 f)"
  proof (rule no_dep_rel_funI)
    fix x y
    assume prem2: "T1 x y"
    have 1: "Eq_rep T1 x (rep1 y)"
      using Eq_rep_rep[OF assms(1) prem2] .
    hence "Eq_rep T2 (f x) (f (rep1 y))"
      using Eq_rep_app[OF assms]
      using prem1
      using Eq_repE Eq_repI dep_rel_fun_def in_dom_def no_dep_rel_fun_def prem1
      sorry
    show "T2 (f x) (map_fun rep1 abs2 f y)"
      using assms prem1 prem2
      using z_propertyE[OF z_property_transfer_triple[OF assms(1)]]
        z_propertyE[OF z_property_transfer_triple[OF assms(2)]]
      unfolding in_co_dom_def in_dom_def
      using no_dep_rel_funE
      using assms(1) assms(2) in_co_dom_def in_dom_def transfer_triple_def
      sorry
  qed
next
  fix g
  assume prem: "in_co_dom (T1 \<Rrightarrow> T2) g"
  show "(T1 \<Rrightarrow> T2) (map_fun abs1 rep2 g) g"
    sorry
qed

end