theory Lifting_Group
  imports
    Isabelle_Set.Rewrite
    Lifting_Set
begin

definition "rel_comp' R S x y \<equiv> (\<exists>z. S x z \<and> R z y)"
definition "rel_inv R x y \<equiv> R y x"

lemma per_idemp: "partial_equivalence Eq \<Longrightarrow> Eq = rel_comp' Eq Eq"
  unfolding partial_equivalence_unfold rel_comp'_def
  by blast

lemma per_inv: "partial_equivalence Eq \<Longrightarrow> Eq = rel_inv Eq"
  unfolding partial_equivalence_unfold rel_inv_def
  by blast

lemma per_sym: "partial_equivalence R \<Longrightarrow> R x y \<Longrightarrow> R y x"
  unfolding partial_equivalence_unfold
  by blast

lemma per_trans: "partial_equivalence R \<Longrightarrow> R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  unfolding partial_equivalence_unfold
  by blast

lemma rel_comp'I: "R x y \<Longrightarrow> S y z \<Longrightarrow> rel_comp' S R x z"
  unfolding rel_comp'_def
  by blast

lemma rel_invI: "R x y \<Longrightarrow> rel_inv R y x"
  unfolding rel_inv_def .

lemma lifting_rel_comp:
  assumes assm: "lifting Eq_rep Eq_abs T abs rep"
  shows "rel_comp' T (rel_inv T) = Eq_abs" "rel_comp' (rel_inv T) T = Eq_rep"
proof -
  show "rel_comp' T (rel_inv T) = Eq_abs"
  proof ((rule ext)+, rule iffI)
    fix x y
    assume prems: "rel_comp' T (rel_inv T) x y"
    show "Eq_abs x y"
      using assm prems
      unfolding lifting_unfold rel_comp'_def rel_inv_def
      by metis
  next
    fix x y
    assume prem: "Eq_abs x y"
    show "rel_comp' T (rel_inv T) x y"
      using assm prem
      unfolding lifting_unfold rel_comp'_def rel_inv_def
      by metis
  qed
next
  show "rel_comp' (rel_inv T) T = Eq_rep"
  proof ((rule ext)+, rule iffI)
    fix x y
    assume prems: "rel_comp' (rel_inv T) T x y"
    show "Eq_rep x y"
      using assm prems
      unfolding lifting_unfold rel_comp'_def rel_inv_def
      by metis
  next
    fix x y
    assume prem: "Eq_rep x y"
    show "rel_comp' (rel_inv T) T x y"
      using assm prem
      unfolding lifting_unfold rel_comp'_def rel_inv_def
      by metis
  qed
qed

lemma inv_lifting:
  assumes "lifting Eq_rep Eq_abs T abs rep"
  shows "lifting Eq_abs Eq_rep (rel_inv T) rep abs"
  apply (
    (subst lifting_unfold rel_fun_def)+,
    (rule conjI)?; (rule conjI)?; (rule conjI)?; (rule conjI)?; (rule conjI)?)
  using assms[unfolded lifting_unfold] rel_inv_def
  by metis+

lemma
  assumes "partial_equivalence R" "partial_equivalence S" "R x x" "S x x" "R y y" "S y y"
  shows "rel_comp' R S x y = rel_comp' S R x y"
proof (rule iffI)
  fix x y
  assume prem: "rel_comp' R S x y"
  obtain z where z: "S x z" "R z y"
    using prem unfolding rel_comp'_def by blast
  have 1: "S z x" "R y z"
    using z assms unfolding partial_equivalence_unfold by blast+
  show "rel_comp' S R x y"
    using z unfolding rel_comp'_def
    oops

lemma
  assumes "partial_equivalence R" "partial_equivalence S"
  shows "rel_comp' R S = rel_comp' S R"
proof ((rule ext)+, rule iffI)
  fix x y
  assume prem: "rel_comp' R S x y"
  obtain z where z: "S x z" "R z y"
    using prem unfolding rel_comp'_def by blast
  have 1: "S z x" "R y z"
    using z assms unfolding partial_equivalence_unfold by blast+
  show "rel_comp' S R x y"
    using z unfolding rel_comp'_def

    oops

term "int_rep list_rep \<longrightarrow> int_abs list_rep \<longrightarrow> int_abs list_abs"
term "(list_relator Eq_int_abs, Eq_list_rep )"
term "Cons_rep 1_abs Nil_rep \<equiv> Cons_rep 1_abs' Nil_rep"
term "Cons_rep 1_abs Nil_rep \<equiv> Cons_rep' 1_abs Nil_rep'"


lemma comp_lifting':
  assumes "lifting Eq_rep1 Eq_abs1 T1 abs1 rep1"
      and "lifting Eq_rep2 Eq_abs2 T2 abs2 rep2"
    shows "lifting
      (rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2))
      (rel_comp' T2 (rel_comp' Eq_abs1 (rel_inv T2)))
      (rel_comp' T2 T1) (comp abs2 abs1) (comp rep1 rep2)"
proof (rule liftingI)
  show "\<And>x y. rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2) x y \<Longrightarrow>
           rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2) y x"
  proof -
    fix x y
    assume prem: "rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2) x y"
    obtain v where v: "rel_comp' Eq_rep1 T2 x v" "rel_inv T2 v y"
      using prem unfolding rel_comp'_def by blast
    obtain w where w: "T2 x w" "Eq_rep1 w v"
      using v(1) unfolding rel_comp'_def by blast
    have 1: "Eq_rep1 v w"
      using w(2) assms(1) unfolding lifting_unfold by metis
    have 2: "T2 y v"
      using v(2) unfolding rel_inv_def .
    have 3: "(rel_inv T2) w x"
      using w(1) unfolding rel_inv_def .
    show "rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2) y x"
      using 2 1 3
      unfolding rel_comp'_def rel_inv_def by blast
  qed
next
  show "\<And>x y z.
       rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2) x y \<Longrightarrow>
       rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2) y z \<Longrightarrow>
       rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2) x z"
  proof -
    fix x y z
    assume prems:
      "rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2) x y"
      "rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2) y z"
    obtain a where a: "rel_comp' Eq_rep1 T2 x a" "rel_inv T2 a y"
      using prems(1) unfolding rel_comp'_def by blast
    obtain b where b: "T2 x b" "Eq_rep1 b a"
      using a(1) unfolding rel_comp'_def by blast
    obtain c where c: "rel_comp' Eq_rep1 T2 y c" "rel_inv T2 c z"
      using prems(2) unfolding rel_comp'_def by blast
    obtain d where d: "T2 y d" "Eq_rep1 d c"
      using c(1) unfolding rel_comp'_def by blast
    have 1: "Eq_abs2 a d" using a(2) d(1)  assms(2) unfolding rel_inv_def lifting_unfold
      by metis
    show "rel_comp' (rel_inv T2) (rel_comp' Eq_rep1 T2) x z"
      unfolding rel_comp'_def
      (* using b a(2) d c(2)*)
      using b 1 d(2) c(2)

      oops

lemma comp_lifting:
  assumes "lifting Eq_rep1 Eq_int T1 abs1 rep1"
      and "lifting Eq_int Eq_abs2 T2 abs2 rep2"
    shows "lifting Eq_rep1 Eq_abs2 (rel_comp' T2 T1) (comp abs2 abs1) (comp rep1 rep2)"
proof (rule liftingI)
  show "\<And>x y. Eq_rep1 x y \<Longrightarrow> Eq_rep1 y x"
    using assms[unfolded lifting_unfold]
    by metis
next
  show "\<And>x y. Eq_abs2 x y \<Longrightarrow> Eq_abs2 y x"
  using assms[unfolded lifting_unfold]
  by metis
next
  show "\<And>x y z. Eq_rep1 x y \<Longrightarrow> Eq_rep1 y z \<Longrightarrow> Eq_rep1 x z"
  using assms[unfolded lifting_unfold]
  by metis
next
  show "\<And>x y z. Eq_abs2 x y \<Longrightarrow> Eq_abs2 y z \<Longrightarrow> Eq_abs2 x z"
  using assms[unfolded lifting_unfold]
  by metis
next
  fix x y z
  assume prems:
    "rel_comp' T2 T1 x z"
    "rel_comp' T2 T1 y z"
  obtain v where 1: "T1 x v" "T2 v z"
    using prems(1) rel_comp'_def
    by metis
  obtain w where 2: "T1 y w" "T2 w z"
    using prems(2) rel_comp'_def
    by metis
  have "Eq_int v w"
    using 1(2) 2(2) assms[unfolded lifting_unfold]
    by metis
  thus "Eq_rep1 x y"
    using 1(1) 2(1) assms[unfolded lifting_unfold]
    by metis
next
  fix x y z
  assume prems:
    "rel_comp' T2 T1 x y"
    "rel_comp' T2 T1 x z"
  obtain v where 1: "T1 x v" "T2 v y"
    using prems(1) rel_comp'_def
    by metis
  obtain w where 2: "T1 x w" "T2 w z"
    using prems(2) rel_comp'_def
    by metis
  have "Eq_int v w"
    using 1(1) 2(1) assms[unfolded lifting_unfold]
    by metis
  thus "Eq_abs2 y z"
    using 1(2) 2(2) assms[unfolded lifting_unfold]
    by metis
next
  fix x y z
  assume prems:
    "Eq_rep1 x y"
    "rel_comp' T2 T1 x z"
  obtain v where 1: "T1 x v" "T2 v z"
    using prems(2) rel_comp'_def
    by metis
  have 2: "T1 y v"
    using 1(1) prems(1) assms[unfolded lifting_unfold]
    by metis
  show "rel_comp' T2 T1 y z"
    using 2 1(2) rel_comp'_def
    by metis
next
  fix x y z
  assume prems:
    "Eq_abs2 y z"
    "rel_comp' T2 T1 x y"
  obtain v where 1: "T1 x v" "T2 v y"
    using prems(2) rel_comp'_def
    by metis
  have 2: "T2 v z"
    using 1(2) prems(1) assms[unfolded lifting_unfold]
    by metis
  show "rel_comp' T2 T1 x z"
    using 2 1(1) rel_comp'_def
    by metis
next
  fix x
  assume prem: "Eq_rep1 x x"
  have 1: "T1 x (abs1 x)"
    using prem assms(1)[unfolded lifting_unfold]
    by metis
  hence "Eq_int (abs1 x) (abs1 x)"
    using assms(1)[unfolded lifting_unfold]
    by metis
  hence "T2 (abs1 x) (abs2 (abs1 x))"
    using assms(2)[unfolded lifting_unfold]
    by metis
  thus "rel_comp' T2 T1 x ((abs2 \<circ> abs1) x)"
    unfolding rel_comp'_def
    using 1 by auto
next
  fix y
  assume prem: "Eq_abs2 y y"
  have 1: "T2 (rep2 y) y"
    using prem assms(2)[unfolded lifting_unfold]
    by metis
  hence "Eq_int (rep2 y) (rep2 y)"
    using assms(2)[unfolded lifting_unfold]
    by metis
  hence "T1 (rep1 (rep2 y)) (rep2 y)"
    using assms(1)[unfolded lifting_unfold]
    by metis
  thus "rel_comp' T2 T1 ((rep1 \<circ> rep2) y) y"
    unfolding rel_comp'_def
    using 1 by auto
qed

lemma
  assumes
    "Eq_rep = rel_comp' (rel_inv T) T" (* 1. condition unchanged *)
    "Eq_abs = rel_comp' T (rel_inv T)" (* new because there was no Eq_abs before *)
    "rel_comp' T Eq_rep = T"           (* new because T\<^sup>-\<^sup>1 \<circ> T may not be transitive if T is not right-unique *)
    "\<And>x y. T x y \<Longrightarrow> Eq_abs (abs x) y" (* 2. condition with equality replaced by Eq_abs *)
    "\<And>y. Eq_abs y y \<Longrightarrow> T (rep y) y"   (* 3. condition weakened because T is not right-total anymore *)
  shows "lifting Eq_rep Eq_abs T abs rep"
proof (rule liftingI)
  fix x y
  assume "Eq_rep x y"
  then obtain z where "T x z" "T y z"
    unfolding assms(1) rel_comp'_def rel_inv_def
    by blast
  thus "Eq_rep y x"
    unfolding assms(1) rel_comp'_def rel_inv_def
    by blast
next
  fix x y z
  assume prems:
    "Eq_rep x y"
    "Eq_rep y z"
  obtain v where v: "T x v" "T y v"
    using prems(1)
    unfolding assms(1) rel_comp'_def rel_inv_def
    by blast
  obtain w where w: "T y w" "T z w"
    using prems(2)
    unfolding assms(1) rel_comp'_def rel_inv_def
    by blast
  have "T x w"
    apply (rewrite assms(3)[symmetric])
    unfolding assms(1) rel_comp'_def rel_inv_def
    using v w(1)
    by blast
  thus "Eq_rep x z"
    unfolding assms(1) rel_comp'_def rel_inv_def
    using w(2)
    by blast
next
  fix x y
  assume "Eq_abs x y"
  then obtain z where "T z x" "T z y"
    unfolding assms(2) rel_comp'_def rel_inv_def
    by blast
  thus "Eq_abs y x"
    unfolding assms(2) rel_comp'_def rel_inv_def
    by blast
next
  fix x y z
  assume prems:
    "Eq_abs x y"
    "Eq_abs y z"
  obtain v where v: "T v x" "T v y"
    using prems(1)
    unfolding assms(2) rel_comp'_def rel_inv_def
    by blast
  obtain w where w: "T w y" "T w z"
    using prems(2)
    unfolding assms(2) rel_comp'_def rel_inv_def
    by blast
  have "T w x"
    apply (rewrite assms(3)[symmetric])
    unfolding assms(1) rel_comp'_def rel_inv_def
    using v w(1)
    by blast
  thus "Eq_abs x z"
    unfolding assms(2) rel_comp'_def rel_inv_def
    using w(2)
    by blast
next
  fix x y z
  assume prems:
    "T x z"
    "T y z"
  show "Eq_rep x y"
    unfolding assms(1) rel_comp'_def rel_inv_def
    using prems
    by blast
next
  fix x y z
  assume prems:
    "T x y"
    "T x z"
  show "Eq_abs y z"
    unfolding assms(2) rel_comp'_def rel_inv_def
    using prems
    by blast
next
  fix x y z
  assume prems:
    "Eq_rep x y"
    "T x z"
  obtain v where v: "T x v" "T y v"
    using prems(1)
    unfolding assms(1) rel_comp'_def rel_inv_def
    by blast
  show "T y z"
    apply (rewrite assms(3)[symmetric])
    unfolding assms(1) rel_comp'_def rel_inv_def
    using v(2, 1) prems(2)
    by blast
next
  fix x y z
  assume prems:
    "Eq_abs y z"
    "T x y"
  obtain v where v: "T v y" "T v z"
    using prems(1)
    unfolding assms(2) rel_comp'_def rel_inv_def
    by blast
  show "T x z"
    apply (rewrite assms(3)[symmetric])
    unfolding assms(1) rel_comp'_def rel_inv_def
    using v(2, 1) prems(2)
    by blast
next
  fix x
  assume prem: "Eq_rep x x"
  obtain y where y: "T x y"
    using prem unfolding assms(1) rel_comp'_def rel_inv_def
    by blast
  hence 1: "Eq_abs (abs x) y"
    using assms(4)
    by blast
  have Eq_abs_T: "T = rel_comp' Eq_abs T"
  proof ((rule ext)+, rule iffI)
    fix x y
    assume prem: "T x y"
    obtain v w where "T x v" "T w v" "T w y"
      using assms(3) prem
      unfolding assms(1) rel_comp'_def rel_inv_def
      by blast
    thus "rel_comp' Eq_abs T x y"
      unfolding assms(2) rel_comp'_def rel_inv_def
      by blast
  next
    fix x y
    assume prem: "rel_comp' Eq_abs T x y"
    obtain v w where "T x v" "T w v" "T w y"
      using prem
      unfolding assms(2) rel_comp'_def rel_inv_def
      by blast
    thus "T x y"
      apply (rewrite assms(3)[symmetric])
      unfolding rel_comp'_def rel_inv_def assms(1)
      by blast
  qed
  show "T x (abs x)"
    apply (rewrite Eq_abs_T)
    using y 1
    unfolding assms(2) rel_comp'_def rel_inv_def
    by blast
next
  fix y
  assume prem: "Eq_abs y y"
  show "T (rep y) y"
    using prem assms(5)
    by blast
qed

term "T x y \<Longrightarrow> Eq_abs (Abs x) y"
term "T x y \<Longrightarrow> Eq_rep x (Rep y)"

term "Eq_abs y y \<Longrightarrow> T (Rep y) y"
term "Eq_rep x x \<Longrightarrow> T x (Abs x)"
term "T x y \<Longrightarrow> T x (Abs x)"

term "Eq_abs x x \<Longrightarrow> Eq_abs (abs (rep x))  x"

term "T a b \<Longrightarrow> T a (Abs a)"

term "T a b \<Longrightarrow> R a (Rep b)"
term "T a b \<Longrightarrow> (T \<circ> T^-1) a (Rep b)"
term "T a b \<Longrightarrow> \<exists>c. T a c \<and> T (Rep b) c"
term "T a b \<Longrightarrow> T a b \<and> T (Rep b) b"

end