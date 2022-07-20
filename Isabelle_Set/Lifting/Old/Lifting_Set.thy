theory Lifting_Set
  imports
    Isabelle_Set.Set_Extension
    Isabelle_Set.TCoproduct
    HOL.BNF_Def
    HOL.Sledgehammer
    Atomize
    Dep_Rel
begin

no_syntax "_Bex" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>(_/\<in>_)./ _)" [0, 0, 10] 10)
no_notation Set.member ("(_/ : _)" [51, 51] 50)
no_notation Set.member  ("'(\<in>')")
no_notation Set.member ("(_/ \<in> _)" [51, 51] 50)
no_notation Set.empty ("{}")
no_syntax "_Finset" :: "args \<Rightarrow> 'a set" ("{(_)}")
no_syntax "_UNION" :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 0, 10] 10)
no_notation BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")
no_notation Product_Type.Times (infixr "\<times>" 80)
no_notation Nat.Nats ("\<nat>")
no_notation Int.ring_1_class.Ints ("\<int>")
no_notation Groups.plus_class.plus (infixl "+" 65)
no_notation Groups.zero_class.zero ("0")
hide_fact sumE
hide_const fst snd
hide_const Nat nat
hide_const abs
hide_type Set.set
notation rel_fun  (infixr "===>" 55)

(* specialized elimination and introduction rules *)
lemma Fun_typeE: "x : A \<Longrightarrow> f : A \<Rightarrow> B \<Longrightarrow> f x : B"
  by discharge_types

lemma Fun_typeE': "x \<in> A \<Longrightarrow> f : Element A \<Rightarrow> Element B \<Longrightarrow> f x \<in> B"
  by discharge_types

lemma Fun_typeE'': "(\<And>x. x : A \<Longrightarrow> f x : B) \<Longrightarrow> (\<lambda>x. f x) : A \<Rightarrow> B"
  by discharge_types

lemma dep_fun_typeE: "x : A \<Longrightarrow> f : (y: A) \<Rightarrow> B y \<Longrightarrow> f x : B x"
  by discharge_types

lemma dep_fun_typeI: "(\<And>x. x : A \<Longrightarrow> f x : B x) \<Longrightarrow> f : (y: A) \<Rightarrow> B y"
  by discharge_types

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

(* set-based versions of function properties *)

definition injective_set :: "set type \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
  where "injective_set A f \<equiv> (\<forall>x y : A. f x = f y \<longrightarrow> x = y)"

definition surjective_set :: "set type \<Rightarrow> set type \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
  where "surjective_set A B f \<equiv> (\<forall>y : B. \<exists>x : A. f x = y)"

definition bijective_set :: "set type \<Rightarrow> set type \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
  where "bijective_set A B f \<equiv> injective_set A f \<and> surjective_set A B f"

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

lemma set_extension_lifting:
  fixes A rep f
  defines "Rep \<equiv> set_extension.Rep A f"
    and "Abs \<equiv> set_extension.Abs A f"
    and "abs \<equiv> set_extension.abs_image A rep f"
  defines "R \<equiv> Ext_Rel abs Rep"
  assumes axioms: "set_extension A rep f"
  shows
    "lifting (eq rep) (eq abs) R Abs Rep"
    "is_equality_set (in_rep (eq rep)) (eq rep)"
    "is_equality_set (in_abs (eq abs)) (eq abs)"
  unfolding lifting_unfold bi_unique_set_def left_unique_set_def right_unique_set_def eq_def
    R_def Ext_Rel_def Rep_def abs_def is_equality_set_def in_rep_def in_abs_def
  apply ((rule conjI)?; (rule conjI)?; (rule conjI)?; (rule conjI)?)
  using axioms Abs_def Fun_typeE'
    set_extension.Rep_type set_extension.Abs_type set_extension.Abs_Rep_inv set_extension.Rep_Abs_inv
  apply metis+
  done

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

(* lemmas to obtain types from transfer rules *)

lemma type_from_rel_type: "R x y \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> P y) \<Longrightarrow> y : type P"
  by unfold_types

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
  shows "lifting (Eq_rep1 ===> Eq_rep2) (Eq_abs1 ===> Eq_abs2) (T1 ===> T2) (fun_map Rep1 Abs2) (fun_map Abs1 Rep2)"
  unfolding fun_map_def comp_def
  using assms fun_lifting
  by blast

definition "Param_Ext_Rel def Rep Eq A R x y \<equiv> y \<in> def A \<and> Eq R x (Rep A y)"

lemma param_set_extension_lifting:
  fixes A rep f B
  defines "Rep \<equiv> set_extension.Rep A f"
    and "Abs \<equiv> set_extension.Abs A f"
    and "abs \<equiv> set_extension.abs_image A rep f"
  defines "R \<equiv> Ext_Rel abs Rep"
  assumes axioms: "set_extension A rep f"
  shows
    "lifting (eq rep) (eq abs) R Abs Rep"
    "is_equality_set (in_rep (eq rep)) (eq rep)"
    "is_equality_set (in_abs (eq abs)) (eq abs)"
  unfolding lifting_unfold bi_unique_set_def left_unique_set_def right_unique_set_def eq_def
    R_def Ext_Rel_def Rep_def abs_def is_equality_set_def in_rep_def in_abs_def
  apply ((rule conjI)?; (rule conjI)?; (rule conjI)?; (rule conjI)?)
  using axioms Abs_def Fun_typeE'
    set_extension.Rep_type set_extension.Abs_type set_extension.Abs_Rep_inv set_extension.Rep_Abs_inv
  apply metis+
  done


lemma type_in_rep_iff: "x : Element A \<equiv> in_rep (eq A) x"
  apply unfold_types
  unfolding in_rep_def eq_def
  by simp

lemma type_in_abs_iff: "x : Element A \<equiv> in_abs (eq A) x"
  apply unfold_types
  unfolding in_abs_def eq_def
  by simp

lemma type_in_rep_fun_iff:
  assumes "(\<And>x. x : A \<equiv> in_rep (eq X) x)"
     and "(\<And>x. x : B \<equiv> in_rep (eq Y) x)"
   shows "(x : A \<Rightarrow> B \<equiv> in_rep (eq X ===> eq Y) x)"
  apply (insert assms)
  apply unfold_types
  unfolding in_rep_def eq_def rel_fun_def
  by simp

lemma type_from_rel_elem: "R = Ext_Rel A f \<Longrightarrow> R x y \<Longrightarrow> y : Element A"
  apply unfold_types
  unfolding Ext_Rel_def
  by blast

(* do I need this anywhere? *)
lemma type_from_rel_ext1: "set_extension A B f \<Longrightarrow> R = Ext_Rel (set_extension.abs_image A B f) (set_extension.Rep A f) \<Longrightarrow> R x y \<Longrightarrow> x : Element B"
  apply unfold_types
  unfolding Ext_Rel_def
  using Fun_typeE' set_extension.Rep_type
  by blast

lemma rel_from_type_elem: "y : Element A \<Longrightarrow> R = Ext_Rel A f \<Longrightarrow> \<exists>x. R x y"
  apply unfold_types
  unfolding Ext_Rel_def
  by blast

lemma rel_from_type_elem': "y : Element A \<Longrightarrow> R = Ext_Rel A f \<Longrightarrow> (\<And>x. R x y \<Longrightarrow> Q) \<Longrightarrow> Q"
  apply unfold_types
  unfolding Ext_Rel_def
  by blast

lemma type_from_rel_fun: "(R ===> S) f g \<Longrightarrow> (\<And>y. y : A \<Longrightarrow> \<exists>x. R x y) \<Longrightarrow> (\<And>x y. S (f x) (g y) \<Longrightarrow> g y : B) \<Longrightarrow> g : A \<Rightarrow> B"
  apply unfold_types
  unfolding rel_fun_def
  by blast

lemma type_from_rel_fun1: "(R ===> S) f g \<Longrightarrow> (\<And>x. x : A \<Longrightarrow> \<exists>y. R x y) \<Longrightarrow> (\<And>x y. S (f x) (g y) \<Longrightarrow> f x : B) \<Longrightarrow> f : A \<Rightarrow> B"
  apply unfold_types
  unfolding rel_fun_def
  by blast

lemma type_from_rel_fun1':
  assumes axiom1: "lifting Eq_A1 Eq_B1 T1 Abs1 Rep1"
      and axiom2: "lifting Eq_A2 Eq_B2 T2 Abs2 Rep2"
      and rel: "(T1 ===> T2) f g"
      and prem_neg: "\<And>x. x : A \<Longrightarrow> in_rep Eq_A1 x"
      and prem_pos: "\<And>x. in_rep Eq_A2 (f x) \<Longrightarrow> f x : B"
  shows "f : A \<Rightarrow> B"
proof (unfold_types)
  fix x
  assume assm: "x : A"
  note in_rep_x = prem_neg[OF assm]
  obtain y where rel1: "T1 x y"
    using lifting_in_rep(3)[OF axiom1 in_rep_x] by blast
  note rel2 = rel_funE'[OF rel rel1]
  note in_rep_f_x = lifting_rel(3)[OF axiom2 rel2]
  show "f x : B" by (fact prem_pos[OF in_rep_f_x])
qed

lemma type_from_rel_fun2':
  assumes axiom1: "lifting Eq_A1 Eq_B1 T1 Abs1 Rep1"
      and axiom2: "lifting Eq_A2 Eq_B2 T2 Abs2 Rep2"
      and rel: "(T1 ===> T2) f g"
      and prem_neg: "\<And>x. x : A \<Longrightarrow> in_abs Eq_B1 x"
      and prem_pos: "\<And>x. in_abs Eq_B2 (g x) \<Longrightarrow> g x : B"
  shows "g : A \<Rightarrow> B"
proof (unfold_types)
  fix y
  assume assm: "y : A"
  note in_abs_y = prem_neg[OF assm]
  obtain x where rel1: "T1 x y"
    using lifting_in_abs(3)[OF axiom1 in_abs_y] by blast
  note rel2 = rel_funE'[OF rel rel1]
  note in_abs_g_y = lifting_rel(4)[OF axiom2 rel2]
  show "g y : B" by (fact prem_pos[OF in_abs_g_y])
qed

lemma type_from_in_abs_fun:
  assumes axiom1: "lifting Eq_A1 Eq_B1 T1 Abs1 Rep1"
      and axiom2: "lifting Eq_A2 Eq_B2 T2 Abs2 Rep2"
      and in_abs: "in_abs (Eq_B1 ===> Eq_B2) g"
      and prem_neg: "\<And>x. x : t1 \<Longrightarrow> in_abs Eq_B1 x"
      and prem_pos: "\<And>x. in_abs Eq_B2 x \<Longrightarrow> x : t2"
    shows "g : t1 \<Rightarrow> t2"
proof (unfold_types)
  fix x
  assume assm: "x : t1"
  have in_abs_g_x: "in_abs Eq_B2 (g x)"
    using prem_neg[OF assm] in_abs
    unfolding in_abs_def rel_fun_def
    by simp
  show "g x : t2" by (fact prem_pos[OF in_abs_g_x])
qed

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

lemma
  assumes axiom1: "lifting Eq_A1 Eq_B1 T1 Abs1 Rep1"
      and axiom2: "lifting Eq_A2 Eq_B2 T2 Abs2 Rep2"
      and rel: "g : t1 \<Rightarrow> t2"
      and prem_neg: "\<And>x. in_abs Eq_B1 x \<Longrightarrow> x : t1"
      and prem_pos: "\<And>x. x : t2 \<Longrightarrow> in_abs Eq_B2 x"
    shows "in_abs (Eq_B1 ===> Eq_B2) g"

lemma in_abs_from_type_fun:
  assumes axiom1: "lifting Eq_A1 Eq_B1 T1 Abs1 Rep1"
      and axiom2: "lifting Eq_A2 Eq_B2 T2 Abs2 Rep2"
      and type: "g : t1 \<Rightarrow> t2"
      and prem_neg: "\<And>x. in_abs Eq_B1 x \<Longrightarrow> x : t1"
      and prem_pos: "\<And>x. x : t2 \<Longrightarrow> in_abs Eq_B2 x"
    shows "in_abs (Eq_B1 ===> Eq_B2) g"
proof -
  note lifting3 = fun_lifting[OF axiom1 axiom2]
  note lifting_rel(4)[OF lifting3]
  { fix x
    assume in_abs_x: "in_abs Eq_B1 x"
    have "in_abs Eq_B2 (g x)"
      apply (rule prem_pos)
      apply (rule Fun_typeE[OF _ type])
      apply (rule prem_neg)
      apply (fact in_abs_x)
      done
  }
  note 1 = this
  { fix x y
    assume rel: "T1 x y"
    have 2: "in_abs Eq_B1 y"
      using rel axiom1 unfolding lifting_unfold in_abs_def
      by blast
    have a: "in_rep Eq_A1 x"
      using rel axiom1 unfolding lifting_unfold in_rep_def
      by blast
    have b: "in_abs Eq_B1 (Abs1 x)"
      using a axiom1 rel unfolding lifting_unfold in_abs_def by metis
    note c = 1[OF b]
    have e: "Eq_B1 (Abs1 x) y"
      using axiom1 lifting_rel(2) rel
      by metis
    have f: "Eq_B2 (g (Abs1 x)) (g y)"
      using axiom1 e 1 unfolding lifting_unfold
    have d: "in_rep Eq_A2 (Rep2 (g (Abs1 x)))"
      using c axiom2 lifting_in_abs(1) sorry
    have "T2 (Rep2 (g (Abs1 x))) (g y)"
      using 1 d
      sorry
  }
  note 3 = this
  have 2: "\<exists>f. \<forall>x y. T1 x y \<longrightarrow> T2 (f x) (g y)"
      using 3 by fast
  have 4: "\<exists>f. (T1 ===> T2) f g"
    unfolding rel_fun_def
    using 2 by blast
  have 3: "(T1 ===> T2) (\<lambda>x. Rep2 (g (Abs1 x))) g"
    using 2
    sorry
  thm lifting_rel(4)[OF lifting3, OF 3]
  have "in_abs (Eq_B1 ===> Eq_B2) g"
    using lifting_rel(4)[OF lifting3] 4
    by blast
  show "in_abs (Eq_B1 ===> Eq_B2) g"
    apply (rule lifting_rel(4)[OF lifting3])
    unfolding rel_fun_def
    apply atomize_rev'
    apply (rule lifting_in_abs'[OF axiom2])
     apply (drule lifting_rel(4)[OF axiom1])
     apply (rule prem_pos)
     apply (rule Fun_typeE[OF _ type])
     apply (rule prem_neg)
     apply assumption

    using lifting_rel(4)[OF axiom1]
    using lifting_in_abs'[OF axiom1]
    sorry
qed

lemma in_abs_from_type_fun:
  assumes axiom1: "lifting Eq_A1 Eq_B1 T1 Abs1 Rep1"
      and axiom2: "lifting Eq_A2 Eq_B2 T2 Abs2 Rep2"
      and type: "g : t1 \<Rightarrow> t2"
      and prem_neg: "\<And>x. in_abs Eq_B1 x \<Longrightarrow> x : t1"
      and prem_pos: "\<And>x. x : t2 \<Longrightarrow> in_abs Eq_B2 x"
    shows "in_abs (Eq_B1 ===> Eq_B2) g"
proof (subst in_abs_def, subst rel_fun_def, atomize_rev')
  fix x y
  assume assm: "Eq_B1 x y"
  have in_abs_x: "in_abs Eq_B1 x"
    using lifting_Eq_abs(5)[OF axiom1 assm] by simp
  note type_x = prem_neg[OF in_abs_x]
  note type_g_x = Fun_typeE[OF type_x type]
  note in_abs_g_x = prem_pos[OF type_g_x]
  show "Eq_B2 (g x) (g y)"
    using lifting_in_abs' in_abs_g_x[unfolded in_abs_def]

    oops

lemma type_from_rel_fun_adj: "([x x' \<Colon> R | P x x'] \<Rrightarrow> S) f g \<Longrightarrow> (\<And>x'. x' : A \<and> Q x' \<Longrightarrow> \<exists>x. R x x' \<and> P x x') \<Longrightarrow> (\<And>x x'. S (f x) (g x') \<Longrightarrow> g x' : B) \<Longrightarrow> g : (Q \<sqdot> A) \<Rightarrow> B"
  apply unfold_types
  unfolding dep_rel_fun_def rel_adj_def
  by blast

lemma type_from_rel_fun_dep:
  "(\<And>x y. R x y \<Longrightarrow> S x y (f x) (g y)) \<Longrightarrow> (\<And>y. y : A \<Longrightarrow> \<exists>x. R x y) \<Longrightarrow> (\<And>x y. S x y (f x) (g y) \<Longrightarrow>
    g y : B y) \<Longrightarrow> g : (x: A) \<Rightarrow> (B x)"
  apply unfold_types
  unfolding rel_fun_def
  by blast

lemma type_from_rel_fun_dep':
  "([x x' \<Colon> R] \<Rrightarrow> S x x') f g \<Longrightarrow> (\<And>x'. x' : A \<Longrightarrow> \<exists>x. R x x') \<Longrightarrow> (\<And>x x'. S x x' (f x) (g x') \<Longrightarrow>
    g x' : B x') \<Longrightarrow> g : (x : A) \<Rightarrow> (B x)"
  apply unfold_types
  unfolding dep_rel_fun_def rel_adj_def
  by blast

lemma conj_exD2: "P \<and> (\<exists>x. Q x) \<Longrightarrow> (\<exists>x. Q x \<and> P)"
  by blast


definition "Bool_set \<equiv> coprod {\<emptyset>} {\<emptyset>}"
definition "True_set \<equiv> inl \<emptyset>"
definition "False_set \<equiv> inr \<emptyset>"

lemma True_type: "True_set : Element Bool_set"
  apply unfold_types
  unfolding Bool_set_def True_set_def
  by simp

lemma False_type: "False_set : Element Bool_set"
  apply unfold_types
  unfolding Bool_set_def False_set_def
  by simp

definition "bool_set_case t f \<equiv> coprod_rec (\<lambda>_. t) (\<lambda>_. f)"

lemma bool_set_case_type: "bool_set_case : A \<Rightarrow> A \<Rightarrow> Element Bool_set \<Rightarrow> A"
  apply (intro Dep_fun_typeI)
  unfolding bool_set_case_def
  apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ coprod_rec_type]]])
  unfolding Bool_set_def
  apply (auto iff: Element_coprod_iff_Coprod)
  done

definition "and_set a b \<equiv> bool_set_case True_set b a"

lemma and_set_type: "and_set : Element Bool_set \<Rightarrow> Element Bool_set \<Rightarrow> Element Bool_set"
  apply (intro Dep_fun_typeI)
  unfolding and_set_def
  apply (rule Fun_typeE[OF _ Fun_typeE[OF _ Fun_typeE[OF _ bool_set_case_type]]])
    apply (simp add: True_type)+
  done

definition "not_set a \<equiv> if a = True_set then False_set else True_set"

definition "to_HOL a \<equiv> a = True_set"

end