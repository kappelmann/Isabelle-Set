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

lemma lifting_comp_Eq_abs_T: "lifting Eq_rep Eq_abs T abs rep \<Longrightarrow> rel_comp' Eq_abs T = T"
  unfolding lifting_unfold rel_comp'_def
  by fast

lemma lifting_comp_T_Eq_rep: "lifting Eq_rep Eq_abs T abs rep \<Longrightarrow> rel_comp' T Eq_rep = T"
  unfolding lifting_unfold rel_comp'_def
  by fast

lemma comp_lifting':
  assumes "lifting Eq_rep1 Eq_abs1 T1 abs1 rep1"
      and "lifting Eq_rep2 Eq_abs2 T2 abs2 rep2"
      and "rel_comp' Eq_abs1 Eq_rep2 = rel_comp' Eq_rep2 Eq_abs1"
    shows "lifting
      (rel_comp' (rel_inv T1) (rel_comp' Eq_rep2 T1))
      (rel_comp' T2 (rel_comp' Eq_abs1 (rel_inv T2)))
      (rel_comp' T2 T1) (comp abs2 abs1) (comp rep1 rep2)"
proof (rule liftingI)
  fix x y
  assume prem: "rel_comp' (rel_inv T1) (rel_comp' Eq_rep2 T1) x y"
  obtain v where v: "rel_comp' Eq_rep2 T1 x v" "rel_inv T1 v y"
    using prem unfolding rel_comp'_def by blast
  obtain w where w: "T1 x w" "Eq_rep2 w v"
    using v(1) unfolding rel_comp'_def by blast
  have "rel_inv T1 w x"
    unfolding rel_inv_def
    using w(1) .
  moreover have "Eq_rep2 v w"
    using w(2) assms(2)[unfolded lifting_unfold]
    by metis
  moreover have "T1 y v"
    using v(2)[unfolded rel_inv_def] .
  ultimately show "rel_comp' (rel_inv T1) (rel_comp' Eq_rep2 T1) y x"
    unfolding rel_comp'_def rel_inv_def
    by blast
next
  fix x y z
  assume prems:
    "rel_comp' (rel_inv T1) (rel_comp' Eq_rep2 T1) x y"
    "rel_comp' (rel_inv T1) (rel_comp' Eq_rep2 T1) y z"
  obtain a where a: "rel_comp' Eq_rep2 T1 x a" "rel_inv T1 a y"
    using prems(1) unfolding rel_comp'_def by blast
  obtain b where b: "T1 x b" "Eq_rep2 b a"
    using a(1) unfolding rel_comp'_def by blast
  obtain c where c: "rel_comp' Eq_rep2 T1 y c" "rel_inv T1 c z"
    using prems(2) unfolding rel_comp'_def by blast
  obtain d where d: "T1 y d" "Eq_rep2 d c"
    using c(1) unfolding rel_comp'_def by blast
  have 1: "Eq_abs1 a d" using a(2) d(1) assms(1) unfolding rel_inv_def lifting_unfold
    by metis
  obtain e where e: "Eq_abs1 b e" "Eq_rep2 e d"
    using b(2) 1 assms(3) unfolding rel_comp'_def
    by metis
  have 2: "T1 x e"
    apply (subst lifting_comp_Eq_abs_T[OF assms(1), symmetric], rule rel_comp'I)
    using b(1) e(1) .
  have 3: "Eq_rep2 e c"
    using e(2) d(2) assms(2) unfolding lifting_unfold
    by metis
  show "rel_comp' (rel_inv T1) (rel_comp' Eq_rep2 T1) x z"
    unfolding rel_comp'_def
    using b a(2) d c(2)
    by blast
next
  fix x y
  assume prem: "rel_comp' T2 (rel_comp' Eq_abs1 (rel_inv T2)) x y"
  obtain v where v: "rel_comp' Eq_abs1 (rel_inv T2) x v" "T2 v y"
    using prem unfolding rel_comp'_def by blast
  obtain w where w: "(rel_inv T2) x w" "Eq_abs1 w v"
    using v(1) unfolding rel_comp'_def by blast
  have "rel_inv T2 y v"
    unfolding rel_inv_def
    using v(2) .
  moreover have "Eq_abs1 v w"
    using w(2) assms(1)
    unfolding lifting_unfold
    by metis
  moreover have "T2 w x"
    using w(1)[unfolded rel_inv_def] .
  ultimately show "rel_comp' T2 (rel_comp' Eq_abs1 (rel_inv T2)) y x"
    unfolding rel_comp'_def rel_inv_def by blast
next
  fix x y z
  assume prems:
    "rel_comp' T2 (rel_comp' Eq_abs1 (rel_inv T2)) x y"
    "rel_comp' T2 (rel_comp' Eq_abs1 (rel_inv T2)) y z"
  obtain a where a: "rel_comp' Eq_abs1 (rel_inv T2) x a" "T2 a y"
    using prems(1) unfolding rel_comp'_def by blast
  obtain b where b: "rel_inv T2 x b" "Eq_abs1 b a"
    using a(1) unfolding rel_comp'_def by blast
  obtain c where c: "rel_comp' Eq_abs1 (rel_inv T2) y c" "T2 c z"
    using prems(2) unfolding rel_comp'_def by blast
  obtain d where d: "rel_inv T2 y d" "Eq_abs1 d c"
    using c(1) unfolding rel_comp'_def by blast
  have 1: "Eq_rep2 a d" using a(2) d(1) assms(2) unfolding rel_inv_def lifting_unfold
    by metis
  obtain e where e: "Eq_rep2 b e" "Eq_abs1 e d"
    using b(2) 1 assms(3) unfolding rel_comp'_def
    by metis
  have 2: "rel_inv T2 x e"
    apply (subst rel_inv_def)
    apply (subst lifting_comp_T_Eq_rep[OF assms(2), symmetric], rule rel_comp'I)
    using e(1) b(1)[unfolded rel_inv_def] assms(2)[unfolded lifting_unfold]
    by blast+
  have 3: "Eq_abs1 e c"
    using e(2) d(2) assms(1) unfolding lifting_unfold
    by metis
  show "rel_comp' T2 (rel_comp' Eq_abs1 (rel_inv T2)) x z"
    unfolding rel_comp'_def
    using 2 3 c(2)
    by blast
next
  fix x y z
  assume prems:
    "rel_comp' T2 T1 x z"
    "rel_comp' T2 T1 y z"
  obtain v where v: "T1 x v" "T2 v z"
    using prems(1)[unfolded rel_comp'_def]
    by blast
  obtain w where w: "T1 y w" "T2 w z"
    using prems(2)[unfolded rel_comp'_def]
    by blast
  have "Eq_rep2 v w"
    using v(2) w(2) assms(2)[unfolded lifting_unfold]
    by metis
  thus "rel_comp' (rel_inv T1) (rel_comp' Eq_rep2 T1) x y"
    unfolding rel_comp'_def rel_inv_def
    using v(1) w(1)
    by blast
next
  fix x y z
  assume prems:
    "rel_comp' T2 T1 x y"
    "rel_comp' T2 T1 x z"
  obtain v where v: "T1 x v" "T2 v y"
    using prems(1)[unfolded rel_comp'_def]
    by blast
  obtain w where w: "T1 x w" "T2 w z"
    using prems(2)[unfolded rel_comp'_def]
    by blast
  have "Eq_abs1 v w"
    using v(1) w(1) assms(1)[unfolded lifting_unfold]
    by metis
  thus "rel_comp' T2 (rel_comp' Eq_abs1 (rel_inv T2)) y z"
    unfolding rel_comp'_def rel_inv_def
    using v(2) w(2)
    by blast
next
  fix x y z
  assume prems:
    "rel_comp' (rel_inv T1) (rel_comp' Eq_rep2 T1) x y"
    "rel_comp' T2 T1 x z"
  obtain a where a: "rel_comp' Eq_rep2 T1 x a" "T1 y a"
    using prems(1)
    unfolding rel_comp'_def rel_inv_def
    by blast
  obtain b where b: "T1 x b" "Eq_rep2 b a"
    using a(1)
    unfolding rel_comp'_def
    by blast
  obtain c where c: "T1 x c" "T2 c z"
    using prems(2)[unfolded rel_comp'_def]
    by blast
  have "Eq_rep2 a b"
    using b(2) assms(2)[unfolded lifting_unfold]
    by metis
  moreover have "Eq_abs1 b c"
    using b(1) c(1) assms(1)[unfolded lifting_unfold]
    by metis
  ultimately obtain d where d: "Eq_abs1 a d" "Eq_rep2 d c"
    using assms(3)[unfolded rel_comp'_def]
    by metis
  have "T1 y d"
    using a(2) d(1) assms(1)[unfolded lifting_unfold]
    by metis
  moreover have "T2 d z"
    using d(2) c(2) assms(2)[unfolded lifting_unfold]
    by metis
  ultimately show "rel_comp' T2 T1 y z"
    unfolding rel_comp'_def
    by blast
next
  fix x y z
  assume prems:
    "rel_comp' T2 (rel_comp' Eq_abs1 (rel_inv T2)) y z"
    "rel_comp' T2 T1 x y"
  obtain a where a: "rel_comp' Eq_abs1 (rel_inv T2) y a" "T2 a z"
    using prems(1)
    unfolding rel_comp'_def
    by blast
  obtain b where b: "T2 b y" "Eq_abs1 b a"
    using a(1)
    unfolding rel_comp'_def rel_inv_def
    by blast
  obtain c where c: "T1 x c" "T2 c y"
    using prems(2)[unfolded rel_comp'_def]
    by blast
  have "Eq_rep2 c b"
    using c(2) b(1) assms(2)[unfolded lifting_unfold]
    by metis
  then obtain d where d: "Eq_abs1 c d" "Eq_rep2 d a"
    using b(2) assms(3)[unfolded rel_comp'_def]
    by metis
  have "T1 x d"
    using c(1) d(1) assms(1)[unfolded lifting_unfold]
    by metis
  moreover have "T2 d z"
    using d(2) a(2) assms(2)[unfolded lifting_unfold]
    by metis
  ultimately show "rel_comp' T2 T1 x z"
    unfolding rel_comp'_def
    by blast
next
  fix x
  assume prem: "rel_comp' (rel_inv T1) (rel_comp' Eq_rep2 T1) x x"
  obtain y where y: "rel_comp' Eq_rep2 T1 x y" "T1 x y"
    using prem
    unfolding rel_comp'_def rel_inv_def
    by blast
  obtain z where z: "Eq_rep2 z y"
    using y(1)[unfolded rel_comp'_def]
    by blast
  from y(2) have 1: "T1 x (abs1 x)"
    using assms(1)[unfolded lifting_unfold]
    by metis
  with y(2) have "Eq_abs1 (abs1 x) y"
    using assms(1)[unfolded lifting_unfold]
    by metis
  moreover from z have "Eq_rep2 y z"
    using assms(2)[unfolded lifting_unfold]
    by metis
  ultimately obtain a where "Eq_rep2 (abs1 x) a"
    using assms(3)[unfolded lifting_unfold rel_comp'_def]
    by metis
  hence "T2 (abs1 x) (abs2 (abs1 x))"
    using assms(2)[unfolded lifting_unfold]
    by metis
  with 1 show "rel_comp' T2 T1 x ((abs2 \<circ> abs1) x)"
    unfolding rel_comp'_def comp_def
    by blast
next
  fix y
  assume prem: "rel_comp' T2 (rel_comp' Eq_abs1 (rel_inv T2)) y y"
  obtain x where x: "rel_comp' Eq_abs1 (rel_inv T2) y x" "T2 x y"
    using prem(1)
    unfolding rel_comp'_def
    by blast
  obtain z where z: "Eq_abs1 z x"
    using x(1)[unfolded rel_comp'_def rel_inv_def]
    by blast
  from x(2) have 1: "T2 (rep2 y) y"
    using assms(2)[unfolded lifting_unfold]
    by metis
  with x(2) have "Eq_rep2 (rep2 y) x"
    using assms(2)[unfolded lifting_unfold]
    by metis
  moreover from z have "Eq_abs1 x z"
    using assms(1)[unfolded lifting_unfold]
    by metis
  ultimately obtain a where "Eq_abs1 (rep2 y) a"
    using assms(3)[unfolded rel_comp'_def]
    by metis
  hence "T1 (rep1 (rep2 y)) (rep2 y)"
    using assms(1)[unfolded lifting_unfold]
    by metis
  with 1 show "rel_comp' T2 T1 ((rep1 \<circ> rep2) y) y"
    unfolding rel_comp'_def comp_def
    by blast
qed

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


end