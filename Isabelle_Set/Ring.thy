chapter \<open>Rings\<close>

theory Ring
imports Monoid

begin

definition [typeclass]: "Ring A = Comm_Group A \<bar> Mul_Monoid A \<bar>
  type (\<lambda>R.
    (\<forall>x y z \<in> A. mul R x (add R y z) = add R (mul R x y) (mul R x z)) \<and>
    (\<forall>x y z \<in> A. mul R (add R y z) x = add R (mul R y x) (mul R z x))
  )"


end