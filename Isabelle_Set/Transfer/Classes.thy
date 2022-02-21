theory Classes
  imports
    (* Lifting_Set_a *)
    Isabelle_Set.Monoids
    HOL.BNF_Def
    HOL.Sledgehammer
begin

no_notation Groups.zero_class.zero ("0")
no_notation Groups.plus_class.plus (infixl "+" 65)
no_notation Groups.minus_class.minus (infixl "-" 65)
no_notation Groups.uminus_class.uminus ("- _" [81] 80)
no_notation Groups.times_class.times (infixl "*" 70)

no_notation
  Set.member  ("'(\<in>')") and
  Set.member  ("(_/ \<in> _)" [51, 51] 50)

notation rel_fun  (infixr "===>" 55)

definition "sup_dom R A \<equiv> (\<forall>x y. R x y \<longrightarrow> x \<in> A)"
definition "sup_rng R A \<equiv> (\<forall>x y. R x y \<longrightarrow> y \<in> A)"

lemma sup_domE: "sup_dom R A \<Longrightarrow> R x y \<Longrightarrow> x \<in> A"
  unfolding sup_dom_def by blast

lemma sup_rngE: "sup_rng R A \<Longrightarrow> R x y \<Longrightarrow> y \<in> A"
  unfolding sup_rng_def by blast

definition "monoid_rel R M N \<equiv>
  (\<exists>A. M : Monoid (Element A) \<and> sup_dom R A) \<and> (\<exists>B. N : Monoid (Element B) \<and> sup_rng R B) \<and>
  R (zero M) (zero N) \<and> (R ===> R ===> R) (add M) (add N)"

lemma "(monoid_rel R ===> R ===> R ===> R) add add"
  unfolding rel_fun_def monoid_rel_def
  by simp

lemma "monoid_rel R A B \<Longrightarrow> (R ===> R ===> R) (add A) (add B)"
  unfolding rel_fun_def monoid_rel_def
  by simp

definition "monoid_hom R \<equiv> R 0 0 \<and> (R ===> R ===> R) (+) (+)"

lemma "monoid_hom R \<Longrightarrow> (R ===> R ===> R) (+) (+)"
  unfolding monoid_hom_def rel_fun_def
  by blast

(* types *)
(* int_add             : \<int> \<Rightarrow> \<int> \<Rightarrow> \<int> *)
(* monoid_add          : Monoid A \<Rightarrow> A \<Rightarrow> A \<Rightarrow> A  *)
(* monoid_add_implicit : (\<exists>M. M : Monoid A) \<Longrightarrow> A \<Rightarrow> A \<Rightarrow> A  *)

(* relations *)
(* Int_Rel_add             : Int_Rel \<Rrightarrow> Int_Rel \<Rrightarrow> Int_Rel *)
(* Monoid_Rel_add          : Monoid_Rel R \<Rrightarrow> R \<Rrightarrow> R \<Rrightarrow> R *)
(* Monoid_Rel_add_implicit : (\<exists>M N. Monoid_Rel R M N) \<Longrightarrow> R \<Rrightarrow> R \<Rrightarrow> R *)

lemma "monoid_rel R A B \<Longrightarrow> (R ===> R) (\<lambda>x. x + x) (\<lambda>y. y + y)"
proof
  fix x y
  assume monoid_rel_A_B: "monoid_rel R A B" and R_x_y: "R x y"
  obtain S where A_type [type]: "A : Monoid (Element S)" and S_sup_R_dom: "sup_dom R S"
    using monoid_rel_A_B unfolding monoid_rel_def by blast
  obtain T where B_type: "B : Monoid (Element T)" and T_sup_R_rng: "sup_rng R T"
    using monoid_rel_A_B unfolding monoid_rel_def by blast
  have R_zero: "R (zero A) (zero B)"
    using monoid_rel_A_B unfolding monoid_rel_def by blast
  have R_add: "(R ===> R ===> R) (add A) (add B)"
    using monoid_rel_A_B unfolding monoid_rel_def by blast
  hence R_add': "\<And>x y x' y'. R x x' \<Longrightarrow> R y y' \<Longrightarrow> R (add A x y) (add B x' y')"
    unfolding rel_fun_def by blast
  have x_type [type]: "x : Element S"
    using sup_domE[OF S_sup_R_dom R_x_y] by simp
  have y_type [type]: "y : Element T"
    using sup_rngE[OF T_sup_R_rng R_x_y] by simp
  have "x + x = add A x x"
    using A_type x_type
    sorry
  show "R (x + x) (y + y)"
    using R_add'[OF R_x_y R_x_y]
      sup_domE[OF S_sup_R_dom R_x_y]
      sup_rngE[OF T_sup_R_rng R_x_y]
      A_type B_type
    sorry
qed

lemma "monoid_hom R \<Longrightarrow> (R ===> R) (\<lambda>x. x + x) (\<lambda>y. y + y)"
  unfolding monoid_hom_def rel_fun_def
  by blast

no_notation convol ("\<langle>(_,/ _)\<rangle>")

term "\<langle>a, b\<rangle>"

definition "lift_monoid Def Rep Abs M \<equiv> object ({
  \<langle>@zero, Abs (zero M)\<rangle>,
  \<langle>@add, (\<lambda>x y \<in> Def. Abs (add M (Rep x) (Rep y)))\<rangle>
} :: Axioms.set)"
term "add M a b"
term "a + b"
lemma "isomorphism A Def R Abs Rep \<Longrightarrow> M : Monoid A \<Longrightarrow> monoid_rel R M (lift_monoid Def Rep Abs M)"
  unfolding monoid_rel_def
  oops
end