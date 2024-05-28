\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Rings\<close>
theory TSRings
  imports TSMonoids
begin

definition [typeclass]: "Ring A \<equiv> Comm_Group A & Mul_Monoid A &
  type (\<lambda>R.
    (\<forall>x y z : A. mul R x (add R y z) = add R (mul R x y) (mul R x z)) \<and>
    (\<forall>x y z : A. mul R (add R x y) z = add R (mul R x z) (mul R y z)))"

lemma RingI:
  assumes "R \<Ztypecolon> Comm_Group A" "R \<Ztypecolon> Mul_Monoid A"
  and "\<And>x y z. \<lbrakk>x \<Ztypecolon> A; y \<Ztypecolon> A; z \<Ztypecolon> A\<rbrakk> \<Longrightarrow>
    mul R x (add R y z) = add R (mul R x y) (mul R x z)"
  and "\<And>x y z. \<lbrakk>x \<Ztypecolon> A; y \<Ztypecolon> A; z \<Ztypecolon> A\<rbrakk> \<Longrightarrow>
    mul R (add R x y) z = add R (mul R x z) (mul R y z)"
  shows "R \<Ztypecolon> Ring A"
  unfolding Ring_def by (auto intro: type_of_typeI assms)

lemma
  shows Ring_Comm_Group [derive]: "R \<Ztypecolon> Ring A \<Longrightarrow> R \<Ztypecolon> Comm_Group A"
  and Ring_Mul_Monoid [derive]: "R \<Ztypecolon> Ring A \<Longrightarrow> R \<Ztypecolon> Mul_Monoid A"
  and Ring_mul_add_eq: "\<And>x y z. \<lbrakk>R \<Ztypecolon> Ring A; x \<Ztypecolon> A; y \<Ztypecolon> A; z \<Ztypecolon> A\<rbrakk>
    \<Longrightarrow> mul R x (add R y z) = add R (mul R x y) (mul R x z)"
  and Ring_add_mul_eq: "\<And>x y z. \<lbrakk>R \<Ztypecolon> Ring A; x \<Ztypecolon> A; y \<Ztypecolon> A; z \<Ztypecolon> A\<rbrakk>
    \<Longrightarrow> mul R (add R x y) z = add R (mul R x z) (mul R y z)"
  unfolding Ring_def by (auto 0 3 dest!: InterD1 InterD2 type_of_typeD)


end