chapter \<open>Rings\<close>

theory Rings
imports Monoids
begin

definition [typeclass]: "Ring A \<equiv> Comm_Group A \<bar> Mul_Monoid A \<bar>
  type (\<lambda>R.
    (\<forall>x y z \<in> A. mul R x (add R y z) = add R (mul R x y) (mul R x z)) \<and>
    (\<forall>x y z \<in> A. mul R (add R x y) z = add R (mul R x z) (mul R y z)))"

lemma RingI:
  assumes "R : Comm_Group A" "R : Mul_Monoid A"
  and "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow>
    mul R x (add R y z) = add R (mul R x y) (mul R x z)"
  and "\<And>x y z. \<lbrakk>x \<in> A; y \<in> A; z \<in> A\<rbrakk> \<Longrightarrow>
    mul R (add R x y) z = add R (mul R x z) (mul R y z)"
  shows "R : Ring A"
  unfolding Ring_def by (auto intro: has_typeI assms)

lemma
  shows Ring_Comm_Group [derive]: "R : Ring A \<Longrightarrow> R : Comm_Group A"
  and Ring_Mul_Monoid [derive]: "R : Ring A \<Longrightarrow> R : Mul_Monoid A"
  and Ring_mul_add_eq: "\<And>x y z. \<lbrakk>R : Ring A; x \<in> A; y \<in> A; z \<in> A\<rbrakk>
    \<Longrightarrow> mul R x (add R y z) = add R (mul R x y) (mul R x z)"
  and Ring_add_mul_eq: "\<And>x y z. \<lbrakk>R : Ring A; x \<in> A; y \<in> A; z \<in> A\<rbrakk>
    \<Longrightarrow> mul R (add R x y) z = add R (mul R x z) (mul R y z)"
  unfolding Ring_def
  by (auto dest!: Int_typeD1 Int_typeD2 has_typeD)[4] fast

end