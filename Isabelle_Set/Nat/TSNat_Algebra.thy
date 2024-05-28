\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Algebra\<close>
theory TSNat_Algebra
imports
  TSNat_Add
  TSNat_Sub
  TSNat_Mul
  TSNat_Inequalities
  TSMonoids
begin

unbundle no_HOL_groups_syntax

subsubsection \<open>Algebraic Structures\<close>

definition "nat_Monoid \<equiv> object {\<langle>$zero, 0\<rangle>, \<langle>$add, \<lambda>m n : \<nat>. nat_add m n\<rangle>}"

bundle isa_set_nat_Monoid_syntax
begin notation nat_Monoid ("'(\<nat>, +')") end
bundle no_isa_set_nat_Monoid_syntax
begin no_notation nat_Monoid ("'(\<nat>, +')") end

unbundle isa_set_nat_Monoid_syntax

(*TODO: The following should be automatically generated*)
lemma nat_Monoid_simps [simp]:
  "(\<nat>, +)@$zero = 0"
  "(\<nat>, +)@$add = \<lambda>m n : \<nat>. nat_add m n"
  unfolding nat_Monoid_def by simp_all
term Set_crel_dep_fun
lemma nat_Monoid: "(\<nat>, +) \<Ztypecolon> Monoid Nat"
proof (rule MonoidI)
  show "(\<nat>, +) \<Ztypecolon> Zero Nat" by (rule ZeroI) simp
  show "(\<nat>, +) \<Ztypecolon> Add Nat"
  (*TODO: object selector simplifier not working properly*)
  (* unfolding nat_Monoid_def by (rule AddI) simp *)
  proof (rule AddI)
    have select_add_eq: "(\<nat>, +)@$add = \<lambda>m n : \<nat>. nat_add m n" by simp
    have "(\<nat>, +)@$add \<Ztypecolon> Nat \<rightarrow>\<^sub>c Nat \<rightarrow>\<^sub>c Nat"
      (* supply
        Set_crel_fun_iff_Set_crel_dep_fun[THEN iffD1, derive]
        Set_crel_fun_iff_Set_crel_dep_fun[THEN iffD2, derive]
      by (subst select_add_eq) discharge_types *)
      sorry
    then show "(\<nat>, +)@$add \<Ztypecolon> Nat \<rightarrow> Nat \<rightarrow> Nat" sorry
  qed
next
  fix x assume "x \<Ztypecolon> Nat"
  show "add (\<nat>, +) (zero (\<nat>, +)) x = x" and "add (\<nat>, +) x (zero (\<nat>, +)) = x"
    \<comment>\<open>Very low-level; lots of unfolding.\<close>
    unfolding add_def zero_def by auto

  fix y z assume "y \<Ztypecolon> Nat" "z \<Ztypecolon> Nat"
  show "add (\<nat>, +) (add (\<nat>, +) x y) z = add (\<nat>, +) x (add (\<nat>, +) y z)"
    unfolding add_def by (simp add: Nat_add_assoc)
qed

definition "nat_Mul_Monoid \<equiv> object {\<langle>$one, 1\<rangle>, \<langle>$mul, \<lambda>m n : \<nat>. nat_mul m n\<rangle>}"

bundle isa_set_nat_Mul_Monoid_syntax
begin notation nat_Mul_Monoid ("'(\<nat>, *')") end
bundle no_isa_set_nat_Mul_Monoid_syntax
begin no_notation nat_Mul_Monoid ("'(\<nat>, *')") end

unbundle isa_set_nat_Mul_Monoid_syntax

lemma nat_Mul_Monoid: "(\<nat>, *) \<Ztypecolon> Mul_Monoid Nat"
proof (rule Mul_MonoidI)
  show "(\<nat>, *) \<Ztypecolon> One Nat"
    by (rule OneI) (simp add: nat_Mul_Monoid_def)
  show "(\<nat>, *) \<Ztypecolon> Mul Nat"
  (*TODO: object selector simplifier not working properly*)
  (* unfolding nat_Monoid_def by (rule AddI) simp *)
  proof (rule MulI)
    have select_mul_eq: "(\<nat>, *)@$mul = \<lambda>m n : \<nat>. nat_mul m n"
      unfolding nat_Mul_Monoid_def by simp
    have "(\<nat>, *)@$mul \<Ztypecolon> Nat \<rightarrow>\<^sub>c Nat \<rightarrow>\<^sub>c Nat"
      (* by (subst select_mul_eq) discharge_types *)
      sorry
    show "(\<nat>, *)@$mul \<Ztypecolon> Nat \<rightarrow> Nat \<rightarrow> Nat" sorry
  qed
next
  fix x assume "x \<Ztypecolon> Nat"
  show "mul (\<nat>, *) (one (\<nat>, *)) x = x" and "mul (\<nat>, *) x (one (\<nat>, *)) = x"
    unfolding nat_Mul_Monoid_def mul_def one_def by auto

  fix y z assume "y \<Ztypecolon> Nat" "z \<Ztypecolon> Nat"
  show "mul (\<nat>, *) (mul (\<nat>, *) x y) z = mul (\<nat>, *) x (mul (\<nat>, *) y z)"
    unfolding nat_Mul_Monoid_def mul_def by (simp add: Nat_mul_assoc)
qed


end
