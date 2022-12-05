\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Algebra\<close>
theory Nat_Algebra
imports
  Monoids
  Nat_Add
  Nat_Sub
  Nat_Mul
  Nat_Inequalities
begin

(*TODO: multiple notations are unbundled here; this is not optimal*)
unbundle no_isa_set_add_implicit_syntax no_isa_set_mul_implicit_syntax
  no_isa_set_zero_implicit_syntax no_isa_set_one_implicit_syntax


subsubsection \<open>Algebraic Structures\<close>

definition "nat_Monoid \<equiv> object {\<langle>@zero, 0\<rangle>, \<langle>@add, \<lambda>m n \<in> \<nat>. nat_add m n\<rangle>}"

bundle isa_set_nat_Monoid_syntax
begin notation nat_Monoid ("'(\<nat>, +')") end
bundle no_isa_set_nat_Monoid_syntax
begin no_notation nat_Monoid ("'(\<nat>, +')") end

unbundle isa_set_nat_Monoid_syntax

(*TODO: The following should be automatically generated*)
lemma nat_Monoid_simps [simp]:
  "(\<nat>, +) @@ zero = 0"
  "(\<nat>, +) @@ add = \<lambda>x y \<in> \<nat>. nat_add x y"
  unfolding nat_Monoid_def by simp_all

lemma nat_Monoid: "(\<nat>, +) : Monoid Nat"
proof (rule MonoidI)
  show "(\<nat>, +) : Zero Nat" by (rule ZeroI) simp
  show "(\<nat>, +) : Add Nat"
  (*TODO: object selector simplifier not working properly*)
  (* unfolding nat_Monoid_def by (rule AddI) simp *)
  proof (rule AddI)
    have select_add_eq: "(\<nat>, +)@@add = \<lambda>m n \<in> \<nat>. nat_add m n" by simp
    have "(\<nat>, +)@@add : Nat \<rightarrow>c Nat \<rightarrow>c Nat"
      by (subst select_add_eq) discharge_types
    then show "(\<nat>, +)@@add : Nat \<rightarrow> Nat \<rightarrow> Nat"
      using Dep_Function_covariant_codom by auto
  qed
next
  fix x assume "x : Nat"
  show "add (\<nat>, +) (zero (\<nat>, +)) x = x" and "add (\<nat>, +) x (zero (\<nat>, +)) = x"
    \<comment>\<open>Very low-level; lots of unfolding.\<close>
    unfolding add_def zero_def by auto

  fix y z assume "y : Nat" "z : Nat"
  show "add (\<nat>, +) (add (\<nat>, +) x y) z = add (\<nat>, +) x (add (\<nat>, +) y z)"
    unfolding add_def by (simp add: Nat_add_assoc)
qed

definition "nat_Mul_Monoid \<equiv> object {\<langle>@one, 1\<rangle>, \<langle>@mul, \<lambda>m n \<in> \<nat>. nat_mul m n\<rangle>}"

bundle isa_set_nat_Mul_Monoid_syntax
begin notation nat_Mul_Monoid ("'(\<nat>, *')") end
bundle no_isa_set_nat_Mul_Monoid_syntax
begin no_notation nat_Mul_Monoid ("'(\<nat>, *')") end

unbundle isa_set_nat_Mul_Monoid_syntax

lemma nat_Mul_Monoid: "(\<nat>, *) : Mul_Monoid Nat"
proof (rule Mul_MonoidI)
  show "(\<nat>, *) : One Nat"
    by (rule OneI) (simp add: nat_Mul_Monoid_def)
  show "(\<nat>, *) : Mul Nat"
  (*TODO: object selector simplifier not working properly*)
  (* unfolding nat_Monoid_def by (rule AddI) simp *)
  proof (rule MulI)
    have select_mul_eq: "(\<nat>, *)@@mul = \<lambda>m n \<in> \<nat>. nat_mul m n"
      unfolding nat_Mul_Monoid_def by simp
    have "(\<nat>, *)@@mul : Nat \<rightarrow>c Nat \<rightarrow>c Nat"
      by (subst select_mul_eq) discharge_types
    show "(\<nat>, *)@@mul : Nat \<rightarrow> Nat \<rightarrow> Nat"
      using Dep_Function_covariant_codom by auto
  qed
next
  fix x assume "x : Nat"
  show "mul (\<nat>, *) (one (\<nat>, *)) x = x" and "mul (\<nat>, *) x (one (\<nat>, *)) = x"
    unfolding nat_Mul_Monoid_def mul_def one_def by auto

  fix y z assume "y : Nat" "z : Nat"
  show "mul (\<nat>, *) (mul (\<nat>, *) x y) z = mul (\<nat>, *) x (mul (\<nat>, *) y z)"
    unfolding nat_Mul_Monoid_def mul_def by (simp add: Nat_mul_assoc)
qed


end

