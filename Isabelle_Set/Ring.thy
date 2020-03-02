chapter \<open>Rings\<close>

theory Ring
imports Monoid

begin

definition [typeclass]: "Ring A = Comm_Group A \<bar> Mul_Monoid A \<bar>
  type (\<lambda>R.
    (\<forall>x y z \<in> A. times R x (plus R y z) = plus R (times R x y) (times R x z)) \<and>
    (\<forall>x y z \<in> A. times R (plus R y z) x = plus R (times R y x) (times R z x))
  )"


end