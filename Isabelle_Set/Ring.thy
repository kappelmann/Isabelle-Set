chapter \<open>Rings\<close>

theory Ring
imports Monoid

begin

definition [typeclass]: "Ring A = Comm_Group A \<bar> Mul_Monoid A \<bar>
  type (\<lambda>R.
    (\<forall>x y z \<in> A. mul R x (add R y z) = add R (mul R x y) (mul R x z)) \<and>
    (\<forall>x y z \<in> A. mul R (add R x y) z = add R (mul R x z) (mul R y z))
  )"

lemma RingI [typeI]:
  assumes "R : Comm_Group A"
  and "R : Mul_Monoid A"
  and "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow> mul R x (add R y z) = add R (mul R x y) (mul R x z)"
  and "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow> mul R (add R x y) z = add R (mul R x z) (mul R y z)"
  shows "R : Ring A"
  using assms unfolding Ring_def by (auto intro: has_type_typeI)

lemma
  shows Ring_Comm_Group [derive]: "R : Ring A \<Longrightarrow> R : Comm_Group A"
  and Ring_Mul_Monoid [derive]: "R : Ring A \<Longrightarrow> R : Mul_Monoid A"
  and mul_add: "\<And>x y z. \<lbrakk>R : Ring A; x \<in> A; y \<in> A; z \<in> A\<rbrakk>
    \<Longrightarrow> mul R x (add R y z) = add R (mul R x y) (mul R x z)"
  and add_mul: "\<And>x y z. \<lbrakk>R : Ring A; x \<in> A; y \<in> A; z \<in> A\<rbrakk>
    \<Longrightarrow> mul R (add R x y) z = add R (mul R x z) (mul R y z)"
  unfolding Ring_def
  subgoal by (drule Int_typeE1, drule Int_typeE1)
  subgoal by (drule Int_typeE1, drule Int_typeE2)
  subgoal by (drule Int_typeE2, drule has_type_typeE) blast
  subgoal by (drule Int_typeE2, drule has_type_typeE) blast
  done

end