theory Lifting_Set
  imports
    Atomize
    Dep_Rel
    HOTG.Basic
    HOL.Metis
begin

no_notation Set.member ("(_/ : _)" [51, 51] 50)
no_notation Set.member  ("'(\<in>')")
no_notation Set.member ("(_/ \<in> _)" [51, 51] 50)
no_notation Set.empty ("{}")
no_notation BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")
no_notation Product_Type.Times (infixr "\<times>" 80)
no_notation Nat.Nats ("\<nat>")
no_notation Groups.plus_class.plus (infixl "+" 65)
no_notation Groups.zero_class.zero ("0")
hide_fact sumE
hide_const fst snd
hide_const Nat
hide_const abs
hide_type Set.set
notation rel_fun  (infixr "===>" 55)

lemma rel_funE': "(A ===> B) f g \<Longrightarrow> (\<And>x y. A x y \<Longrightarrow> B (f x) (g y))"
  using rel_fun_def by metis

lemma conjE1: "(A \<and> B \<Longrightarrow> A)"
  by (rule HOL.conjE, assumption+)

lemma conjE1': "A \<and> B \<Longrightarrow> (B \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule HOL.conjE, assumption+)

lemma conjE2: "A \<and> B \<Longrightarrow> B"
  by (erule conjE, assumption)

lemma conjE': "(P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> (P \<and> Q \<Longrightarrow> R)"
  by (erule conjE, assumption)

lemma ex_conj_True: "\<exists>x. P x \<Longrightarrow> \<exists>x. P x \<and> True" by simp

(* set based version of relation properties *)

definition symmetric :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "symmetric p \<equiv> (\<forall>x y. p x y \<longrightarrow> p y x)"

definition transitive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "transitive p \<equiv> (\<forall>x y z. p x y \<and> p y z \<longrightarrow> p x z)"

definition partial_equivalence :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "partial_equivalence p \<equiv> symmetric p \<and> transitive p"

definition partial_equality :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "partial_equality p \<equiv> (\<forall>x y. p x y \<longrightarrow> x = y)"

lemmas partial_equivalence_unfold = partial_equivalence_def[unfolded symmetric_def transitive_def]

lemma partial_equivalence_semi_reflexive:
  assumes "partial_equivalence R"
     and "R x y"
   shows "R x x" "R y y"
  using assms
  unfolding partial_equivalence_unfold
  by blast+

definition left_total_set :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "left_total_set in_dom in_rng R \<equiv> (\<forall>x. in_dom x \<longrightarrow> (\<exists>y. in_rng y \<and> R x y))"

definition right_total_set :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "right_total_set in_dom in_rng R \<equiv> (\<forall>y. in_rng y \<longrightarrow> (\<exists>x. in_dom x \<and> R x y))"

definition bi_total_set :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "bi_total_set in_dom in_rng R \<equiv> left_total_set in_dom in_rng R \<and> right_total_set in_dom in_rng R"

lemmas bi_total_set_unfold = bi_total_set_def[unfolded left_total_set_def right_total_set_def]

lemma left_total_setE1: "left_total_set in_dom in_rng R \<Longrightarrow> in_dom x \<Longrightarrow> \<exists>y. R x y"
  unfolding left_total_set_def by fast

lemma left_total_setE2: "left_total_set in_dom in_rng R \<Longrightarrow> in_dom x \<Longrightarrow> \<exists>y. in_rng y"
  unfolding left_total_set_def by fast

definition left_unique_set :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "left_unique_set R \<equiv> (\<forall>x y z. R x z \<longrightarrow> R y z \<longrightarrow> x = y)"

definition right_unique_set :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "right_unique_set R \<equiv> (\<forall>x y z. R x y \<longrightarrow> R x z \<longrightarrow> y = z)"

definition bi_unique_set :: " ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "bi_unique_set R \<longleftrightarrow> left_unique_set R \<and> right_unique_set R"

lemmas bi_unique_set_unfold = bi_unique_set_def[unfolded left_unique_set_def right_unique_set_def]

lemma bi_uniqueE: "\<lbrakk>bi_unique_set R; R x x'; R y y'\<rbrakk> \<Longrightarrow> x = y \<longleftrightarrow> x' = y'"
  unfolding bi_unique_set_def left_unique_set_def right_unique_set_def
  by blast

definition "is_isomorphism_set in_dom in_rng R \<equiv> bi_total_set in_dom in_rng R \<and> bi_unique_set R"

definition "is_equality_set in_dom R \<equiv> (\<forall>x. in_dom x \<longrightarrow> R x x) \<and> (\<forall>x y. R x y \<longrightarrow> x = y \<and> in_dom x)"

lemma equalityE:
  assumes assms: "is_equality_set in_dom R" "R x y"
  shows "x = y" "in_dom x"
  using assms
  unfolding is_equality_set_def
  by blast+

lemma equalityI: "is_equality_set in_dom R \<Longrightarrow> in_dom x \<Longrightarrow> R x x"
  unfolding is_equality_set_def
  by blast

lemma equalityI': "is_equality_set in_dom R \<Longrightarrow> in_dom x \<Longrightarrow> x = y \<Longrightarrow> R x y"
  unfolding is_equality_set_def
  by blast

lemma equality_sym: "is_equality_set in_dom R \<Longrightarrow> symmetric R"
  unfolding is_equality_set_def symmetric_def
  by blast

lemma equality_is_partial_equivalence: "is_equality_set in_dom R \<Longrightarrow> partial_equivalence R"
  unfolding is_equality_set_def partial_equivalence_unfold
  by blast

lemma symE: "symmetric R \<Longrightarrow> R x y \<Longrightarrow> R y x"
  unfolding symmetric_def by blast

lemma rel_fun_sym: "symmetric R \<Longrightarrow> symmetric S \<Longrightarrow> symmetric (R ===> S)"
  unfolding symmetric_def rel_fun_def
  by blast


definition "eq_rel_resp_trans_rel Eq_rep Eq_abs T \<equiv>
  (\<forall>x y z. T x z \<and> T y z \<longrightarrow> Eq_rep x y) \<and>
  (\<forall>x y z. T x y \<and> T x z \<longrightarrow> Eq_abs y z)"

definition "trans_rel_resp_eq_rel Eq_rep Eq_abs T \<equiv>
  (\<forall>x y z. Eq_rep x y \<and> T x z \<longrightarrow> T y z) \<and>
  (\<forall>x y z. Eq_abs y z \<and> T x y \<longrightarrow> T x z)"

(* this predicate corresponds to the quotient predicate *)
definition lifting ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "lifting Eq_rep Eq_abs T Abs Rep \<equiv>
    partial_equivalence Eq_rep \<and> partial_equivalence Eq_abs \<and>
    eq_rel_resp_trans_rel Eq_rep Eq_abs T \<and>
    trans_rel_resp_eq_rel Eq_rep Eq_abs T \<and>
    (\<forall>x. Eq_rep x x \<longrightarrow> T x (Abs x) \<and> Eq_rep (Rep (Abs x)) x) \<and>
    (\<forall>y. Eq_abs y y \<longrightarrow> T (Rep y) y \<and> Eq_abs (Abs (Rep y)) y) \<and>
    (\<forall>x y. T x y \<longrightarrow> Eq_rep x x \<and> Eq_abs y y)" (* redundant *)

lemma lifting_simp:
   "partial_equivalence Eq_rep \<Longrightarrow>
    partial_equivalence Eq_abs \<Longrightarrow>
    eq_rel_resp_trans_rel Eq_rep Eq_abs T \<Longrightarrow>
    trans_rel_resp_eq_rel Eq_rep Eq_abs T \<Longrightarrow>
    (\<And>x. Eq_rep x x \<Longrightarrow> T x (abs x)) \<Longrightarrow>
    (\<And>y. Eq_abs y y \<Longrightarrow> T (rep y) y) \<Longrightarrow>
    lifting Eq_rep Eq_abs T abs rep"
  unfolding lifting_def partial_equivalence_unfold eq_rel_resp_trans_rel_def trans_rel_resp_eq_rel_def
  by meson

lemma liftingI:
   "(\<And>x y. Eq_rep x y \<Longrightarrow> Eq_rep y x) \<Longrightarrow>
    (\<And>x y z. Eq_rep x y \<Longrightarrow> Eq_rep y z \<Longrightarrow> Eq_rep x z) \<Longrightarrow>
    (\<And>x y. Eq_abs x y \<Longrightarrow> Eq_abs y x) \<Longrightarrow>
    (\<And>x y z. Eq_abs x y \<Longrightarrow> Eq_abs y z \<Longrightarrow> Eq_abs x z) \<Longrightarrow>
    (\<And>x y z. T x z \<Longrightarrow> T y z \<Longrightarrow> Eq_rep x y) \<Longrightarrow>
    (\<And>x y z. T x y \<Longrightarrow> T x z \<Longrightarrow> Eq_abs y z) \<Longrightarrow>
    (\<And>x y z. Eq_rep x y \<Longrightarrow> T x z \<Longrightarrow> T y z) \<Longrightarrow>
    (\<And>x y z. Eq_abs y z \<Longrightarrow> T x y \<Longrightarrow> T x z) \<Longrightarrow>
    (\<And>x. Eq_rep x x \<Longrightarrow> T x (abs x)) \<Longrightarrow>
    (\<And>y. Eq_abs y y \<Longrightarrow> T (rep y) y) \<Longrightarrow>
    lifting Eq_rep Eq_abs T abs rep"
  unfolding lifting_def partial_equivalence_unfold eq_rel_resp_trans_rel_def trans_rel_resp_eq_rel_def
  by meson

lemmas lifting_unfold = lifting_def[
    unfolded partial_equivalence_unfold eq_rel_resp_trans_rel_def trans_rel_resp_eq_rel_def]

definition "in_rep Eq_A x \<equiv> Eq_A x x"
definition "in_abs Eq_B x \<equiv> Eq_B x x"

lemma in_repI: "E x x \<Longrightarrow> in_rep E x"
  unfolding in_rep_def
  .

lemma in_repI': "partial_equivalence E \<Longrightarrow> E x y \<Longrightarrow> in_rep E x"
  unfolding in_rep_def partial_equivalence_unfold
  by blast

lemma in_absI1: "partial_equivalence E \<Longrightarrow> E x y \<Longrightarrow> in_abs E x"
  unfolding in_abs_def partial_equivalence_unfold
  by blast

lemma in_absI2: "partial_equivalence E \<Longrightarrow> E x y \<Longrightarrow> in_abs E y"
  unfolding in_abs_def partial_equivalence_unfold
  by blast

lemma in_rep_funE: "in_rep (E ===> F) f \<Longrightarrow> in_rep E x \<Longrightarrow> in_rep F (f x)"
  unfolding in_rep_def rel_fun_def
  by blast

lemma Eq_Abs: "lifting Eq_rep Eq_abs R Abs Rep \<Longrightarrow> (Eq_rep ===> Eq_abs) Abs Abs"
  unfolding lifting_unfold rel_fun_def
  by metis

lemma lifting_rel:
  fixes Eq_rep Eq_abs T Abs Rep
  assumes axiom: "lifting Eq_rep Eq_abs T Abs Rep"
    and rel: "T x y"
  shows "Eq_rep (Rep y) x" "Eq_abs (Abs x) y" "in_rep Eq_rep x" "in_abs Eq_abs y" "T (Rep y) (Abs x)"
  using axiom rel
  unfolding lifting_unfold in_rep_def in_abs_def
  by meson+

lemma lifting_Eq_rep:
  fixes Eq_rep Eq_abs T Abs Rep
  assumes axiom: "lifting Eq_rep Eq_abs T Abs Rep"
    and x: "Eq_rep x1 x2"
  shows "T x1 (Abs x2)" "Eq_rep (Rep (Abs x1)) x2" "Eq_abs (Abs x1) (Abs x2)" "Eq_rep x1 x1" "in_rep Eq_rep x1"
  using axiom x
  unfolding lifting_unfold in_rep_def
  by metis+

lemma lifting_Eq_abs:
  fixes Eq_rep Eq_abs T Abs Rep
  assumes axiom: "lifting Eq_rep Eq_abs T Abs Rep"
    and y: "Eq_abs y1 y2"
  shows "T (Rep y1) y2" "Eq_abs (Abs (Rep y1)) y2" "Eq_rep (Rep y1) (Rep y2)" "Eq_abs y1 y1"  "in_abs Eq_abs y1"
  using axiom y
  unfolding lifting_unfold in_abs_def
  by metis+

lemma lifting_in_rep:
  fixes Eq_rep Eq_abs T Abs Rep
  assumes axiom: "lifting Eq_rep Eq_abs T Abs Rep"
    and in_rep: "in_rep Eq_rep x"
  shows "in_abs Eq_abs (Abs x)" "Eq_rep x x" "T x (Abs x)"
  using axiom in_rep
  unfolding lifting_unfold in_rep_def in_abs_def
  by blast+

lemma lifting_in_abs:
  fixes Eq_rep Eq_abs T Abs Rep
  assumes axiom: "lifting Eq_rep Eq_abs T Abs Rep"
    and in_abs: "in_abs Eq_abs y"
  shows "in_rep Eq_rep (Rep y)" "Eq_abs y y" "T (Rep y) y"
  using axiom in_abs
  unfolding lifting_unfold in_rep_def in_abs_def
  by blast+

(* lifting set extensions *)

definition "Ext_Rel def Rep x y \<equiv> y \<in> def \<and> Rep y = x"

definition "eq A x y \<equiv> x \<in> A \<and> x = y"

lemma eq_symmetric: "symmetric (eq A)"
  unfolding symmetric_def eq_def
  by blast

definition "elem A x \<equiv> x \<in> A"

lemma eq_is_per: "is_equality_set p R \<Longrightarrow> partial_equivalence R"
  unfolding is_equality_set_def partial_equivalence_unfold
  by blast

lemma lifting_Abs_swap: "lifting eq_rep eq_abs T Abs Rep \<Longrightarrow> eq_rep y y \<Longrightarrow> T x (Abs y) \<Longrightarrow> T y (Abs x)"
  unfolding lifting_unfold
  by metis

(* restricted equalities as isomorphic relations *)

definition "Eq_Rel A \<equiv> Ext_Rel A id"

lemma equality_lifting:
  fixes A
  assumes T_def: "T \<equiv> Eq_Rel A"
  shows "lifting (eq A) (eq A) T (\<lambda>x. x) (\<lambda>x. x)" "is_equality_set (in_rep (eq A)) (eq A)" "is_equality_set (in_abs (eq A)) (eq A)"
  unfolding lifting_unfold T_def Eq_Rel_def Ext_Rel_def eq_def is_equality_set_def in_rep_def in_abs_def
  by auto

lemma fun_lifting:
  assumes "lifting Eq_rep1 Eq_abs1 T1 Abs1 Rep1" and "lifting Eq_rep2 Eq_abs2 T2 Abs2 Rep2"
  shows "lifting (Eq_rep1 ===> Eq_rep2) (Eq_abs1 ===> Eq_abs2) (T1 ===> T2) (\<lambda>f x. Abs2 (f (Rep1 x))) (\<lambda>f x. Rep2 (f (Abs1 x)))"
proof ((subst lifting_unfold rel_fun_def)+, (rule conjI)?; (rule conjI)?; (rule conjI)?; (rule conjI)?; (rule conjI)?; (rule conjI)?; (rule conjI)?; (rule conjI)?; (rule allI)+)
  show
    "\<And>x y. (\<forall>xa ya. Eq_rep1 xa ya \<longrightarrow> Eq_rep2 (x xa) (y ya)) \<longrightarrow>
      (\<forall>xa ya. Eq_rep1 xa ya \<longrightarrow> Eq_rep2 (y xa) (x ya))"
    using assms[unfolded lifting_unfold] by meson
next
  show
    "\<And>x y z.
      (\<forall>xa ya. Eq_rep1 xa ya \<longrightarrow> Eq_rep2 (x xa) (y ya)) \<and>
      (\<forall>x ya. Eq_rep1 x ya \<longrightarrow> Eq_rep2 (y x) (z ya)) \<longrightarrow>
      (\<forall>xa y. Eq_rep1 xa y \<longrightarrow> Eq_rep2 (x xa) (z y))"
    using assms[unfolded lifting_unfold] by meson
next
  show
    "\<And>x y. (\<forall>xa ya. Eq_abs1 xa ya \<longrightarrow> Eq_abs2 (x xa) (y ya)) \<longrightarrow>
      (\<forall>xa ya. Eq_abs1 xa ya \<longrightarrow> Eq_abs2 (y xa) (x ya))"
    using assms[unfolded lifting_unfold] by meson
next
  show
    "\<And>x y z.
      (\<forall>xa ya. Eq_abs1 xa ya \<longrightarrow> Eq_abs2 (x xa) (y ya)) \<and>
      (\<forall>x ya. Eq_abs1 x ya \<longrightarrow> Eq_abs2 (y x) (z ya)) \<longrightarrow>
      (\<forall>xa y. Eq_abs1 xa y \<longrightarrow> Eq_abs2 (x xa) (z y))"
    using assms[unfolded lifting_unfold] by meson
next
  fix f g h
  show
    "(\<forall>x y. T1 x y \<longrightarrow> T2 (f x) (h y)) \<and> (\<forall>x y. T1 x y \<longrightarrow> T2 (g x) (h y)) \<longrightarrow>
     (\<forall>x y. Eq_rep1 x y \<longrightarrow> Eq_rep2 (f x) (g y))"
  proof (rule impI; erule conjE; atomize_rev')
    fix x y
    assume rels1: "\<And>x y. T1 x y \<Longrightarrow> T2 (f x) (h y)" "\<And>x y. T1 x y \<Longrightarrow> T2 (g x) (h y)"
      and eq: "Eq_rep1 x y"
    define z and w where "z \<equiv> Abs1 x" and "w \<equiv> Abs1 y"
    note assms' = assms[unfolded lifting_unfold]
    have param: "Eq_rep1 x x" "Eq_rep1 y y"
      using assms'(1) using eq by meson+
    have rels2: "T1 x z" "T1 y w"
      using assms'(1) z_def w_def param by metis+
    hence "Eq_abs1 z w"
      using assms'(1) rels2 eq by meson
    hence "Eq_abs2 (h z) (h w)"
      using assms' rels1 rels2 by meson
    moreover have "T2 (f x) (h z)" "T2 (g y) (h w)"
      using assms'(2) rels1 rels2 by meson+
    ultimately show "Eq_rep2 (f x) (g y)"
      using assms'(2) by meson
  qed
next
  fix f g h
  show
    "(\<forall>x y. T1 x y \<longrightarrow> T2 (f x) (g y)) \<and> (\<forall>x y. T1 x y \<longrightarrow> T2 (f x) (h y)) \<longrightarrow>
     (\<forall>x y. Eq_abs1 x y \<longrightarrow> Eq_abs2 (g x) (h y))"
  proof (rule impI; erule conjE; atomize_rev')
    fix x y
    assume rels1: "\<And>x y. T1 x y \<Longrightarrow> T2 (f x) (g y)" "\<And>x y. T1 x y \<Longrightarrow> T2 (f x) (h y)"
       and eq: "Eq_abs1 x y"
    define z and w where "z \<equiv> Rep1 x" and "w \<equiv> Rep1 y"
    note assms' = assms[unfolded lifting_unfold]
    have param: "Eq_abs1 x x" "Eq_abs1 y y"
      using assms'(1) using eq by meson+
    have rels2: "T1 z x" "T1 w y"
      using assms'(1) z_def w_def param by metis+
    hence "Eq_rep1 z w"
      using assms'(1) rels2 eq by meson
    hence "Eq_rep2 (f z) (f w)"
      using assms' rels1 rels2 by meson
    moreover have "T2 (f z) (g x)" "T2 (f w) (h y)"
      using assms'(2) rels1 rels2 by meson+
    ultimately show "Eq_abs2 (g x) (h y)"
      using assms'(2) by meson
  qed
next
  fix f g h
  show
    "(\<forall>x y. Eq_rep1 x y \<longrightarrow> Eq_rep2 (f x) (g y)) \<and> (\<forall>x y. T1 x y \<longrightarrow> T2 (f x) (h y)) \<longrightarrow>
     (\<forall>x y. T1 x y \<longrightarrow> T2 (g x) (h y))"
  proof (rule impI; erule conjE; atomize_rev')
    fix x y
    assume eq_f_g:"\<And>x y. Eq_rep1 x y \<Longrightarrow> Eq_rep2 (f x) (g y)"
       and rel_f_h: "\<And>x y. T1 x y \<Longrightarrow> T2 (f x) (h y)"
       and rel_x_y: "T1 x y"
    note assms' = assms[unfolded lifting_unfold]
    have "Eq_rep1 x x" "Eq_abs1 y y"
      using assms'(1) using rel_x_y by blast+
    hence "Eq_rep2 (f x) (g x)"
      using assms'(1) eq_f_g by metis
    thus "T2 (g x) (h y)"
      using assms'(2) rel_x_y rel_f_h by meson
  qed
next
  fix f g h
  show
    "(\<forall>x y. Eq_abs1 x y \<longrightarrow> Eq_abs2 (g x) (h y)) \<and> (\<forall>x y. T1 x y \<longrightarrow> T2 (f x) (g y)) \<longrightarrow>
     (\<forall>x y. T1 x y \<longrightarrow> T2 (f x) (h y))"
  proof (rule impI; erule conjE; atomize_rev')
    fix x y
    assume eq_g_h: "\<And>x y. Eq_abs1 x y \<Longrightarrow> Eq_abs2 (g x) (h y)"
       and rel_f_g: "\<And>x y. T1 x y \<Longrightarrow> T2 (f x) (g y)"
       and rel_x_y: "T1 x y"
    note assms' = assms[unfolded lifting_unfold]
    have "Eq_rep1 x x" "Eq_abs1 y y"
      using assms'(1) using rel_x_y by blast+
    hence "Eq_abs2 (g y) (h y)"
      using assms'(1) eq_g_h by metis
    thus "T2 (f x) (h y)"
      using assms'(2) rel_x_y rel_f_g by meson
  qed
next
  note assms' = assms[unfolded lifting_unfold]
  fix f
  show
    "(\<forall>xa y. Eq_rep1 xa y \<longrightarrow> Eq_rep2 (f xa) (f y)) \<longrightarrow>
     (\<forall>xa y. T1 xa y \<longrightarrow> T2 (f xa) (Abs2 (f (Rep1 y)))) \<and>
     (\<forall>xa y. Eq_rep1 xa y \<longrightarrow> Eq_rep2 (Rep2 (Abs2 (f (Rep1 (Abs1 xa))))) (f y))"
  proof (rule impI; rule conjI; atomize_rev')
    fix x y
    assume param: "\<And>x y. Eq_rep1 x y \<Longrightarrow> Eq_rep2 (f x) (f y)"
       and rel: "T1 x y"
    have "Eq_rep1 x (Rep1 y)"
      using assms'(1) rel by meson
    hence "Eq_rep2 (f x) (f (Rep1 y))"
      using assms' param by metis
    thus "T2 (f x) (Abs2 (f (Rep1 y)))"
      using assms' by meson
  next
    fix x y
    assume param: "\<And>x y. Eq_rep1 x y \<Longrightarrow> Eq_rep2 (f x) (f y)"
       and eq: "Eq_rep1 x y"
    have "Eq_rep1 (Rep1 (Abs1 x)) x"
      using assms'(1) eq by metis
    thus "Eq_rep2 (Rep2 (Abs2 (f (Rep1 (Abs1 x))))) (f y)"
      using param eq assms' by meson
  qed
next
  note assms' = assms[unfolded lifting_unfold]
  fix f
  show
    "(\<forall>x y. Eq_abs1 x y \<longrightarrow> Eq_abs2 (f x) (f y)) \<longrightarrow>
     (\<forall>x y. T1 x y \<longrightarrow> T2 (Rep2 (f (Abs1 x))) (f y)) \<and>
     (\<forall>x y. Eq_abs1 x y \<longrightarrow> Eq_abs2 (Abs2 (Rep2 (f (Abs1 (Rep1 x))))) (f y))"
  proof (rule impI; rule conjI; atomize_rev')
    fix x y
    assume param: "\<And>x y. Eq_abs1 x y \<Longrightarrow> Eq_abs2 (f x) (f y)"
       and rel: "T1 x y"
    have "Eq_abs1 (Abs1 x) y"
      using assms' rel by meson
    hence "Eq_abs2 (f (Abs1 x)) (f y)"
      using param by blast
    thus "T2 (Rep2 (f (Abs1 x))) (f y)"
      using assms' by meson
  next
    fix x y
    assume param: "\<And>x y. Eq_abs1 x y \<Longrightarrow> Eq_abs2 (f x) (f y)"
       and eq: "Eq_abs1 x y"
    have "Eq_abs1 (Abs1 (Rep1 x)) x"
      using assms' eq by metis
    thus "Eq_abs2 (Abs2 (Rep2 (f (Abs1 (Rep1 x))))) (f y)"
      using assms' param eq by meson
  qed
next
  note assms' = assms[unfolded lifting_unfold]
  fix f g
  show
    "(\<forall>x y. T1 x y \<longrightarrow> T2 (f x) (g y)) \<longrightarrow>
    (\<forall>x y. Eq_rep1 x y \<longrightarrow> Eq_rep2 (f x) (f y)) \<and>
    (\<forall>x y. Eq_abs1 x y \<longrightarrow> Eq_abs2 (g x) (g y))"
  proof (rule impI; rule conjI; (rule conjI)?; (rule conjI)?; atomize_rev')
    fix x y
    assume rel: "\<And>x y. T1 x y \<Longrightarrow> T2 (f x) (g y)"
       and eq: "Eq_rep1 x y"
    have "\<And>x y. Eq_rep1 x y \<Longrightarrow> T1 x (Abs1 y)"
      using assms' by meson
    hence "\<And>x y. Eq_rep1 x y \<Longrightarrow> Eq_rep2 (f x) (f y)"
      using assms' rel by meson
    thus "Eq_rep2 (f x) (f y)"
      using assms' eq by metis
  next
    fix x y
    assume rel: "\<And>x y. T1 x y \<Longrightarrow> T2 (f x) (g y)"
       and eq: "Eq_abs1 x y"
    have "\<And>x y. Eq_abs1 x y \<Longrightarrow> T1 (Rep1 x) y"
      using assms' by meson
    hence "\<And>x y. Eq_abs1 x y \<Longrightarrow> Eq_abs2 (g x) (g y)"
      using assms' rel by meson
    thus "Eq_abs2 (g x) (g y)"
      using assms' eq by metis
  qed
qed

lemma fun_lifting':
  assumes "lifting Eq_rep1 Eq_abs1 T1 Abs1 Rep1" and "lifting Eq_rep2 Eq_abs2 T2 Abs2 Rep2"
  shows "lifting (Eq_rep1 ===> Eq_rep2) (Eq_abs1 ===> Eq_abs2) (T1 ===> T2) (map_fun Rep1 Abs2) (map_fun Abs1 Rep2)"
  unfolding map_fun_def comp_def
  using assms fun_lifting
  by blast


lemma lifting_eq_per:
  assumes "lifting Eq_A Eq_B T Abs Rep"
  shows "partial_equivalence Eq_A" "partial_equivalence Eq_B"
  using assms
  unfolding lifting_unfold partial_equivalence_unfold
  by metis+

lemma lifting_in_abs': "lifting Eq_A Eq_B T Abs Rep \<Longrightarrow> in_abs Eq_B y \<Longrightarrow> (\<And>x. T x y \<Longrightarrow> P) \<Longrightarrow> P"
  using lifting_in_abs(3) by metis

thm lifting_in_abs(3)
thm lifting_rel(4)



lemma lifting_fun_comp:
  assumes lifting1: "lifting Eq_rep1 Eq_abs1 T1 abs1 rep1"
      and lifting2: "lifting Eq_rep2 Eq_abs2 T2 abs2 rep2"
      and lifting3: "lifting Eq_rep3 Eq_abs3 T3 abs3 rep3"
      and lifting4: "lifting Eq_rep4 Eq_abs4 T4 abs4 rep4"
      and rel_f: "(T1 ===> T2) f f'"
      and rel_g: "(T3 ===> T4) g g'"
      and subrel: "\<And>x x'. T2 x x' \<Longrightarrow> T3 x x'"
    shows "(T1 ===> T4) (g \<circ> f) (g' \<circ> f')"
  using assms[unfolded lifting_unfold]
  unfolding rel_fun_def comp_def
  by metis

end