section \<open>Integers\<close>
theory Integers
imports
  Integers_Rep
begin

subsection \<open>The Integers as a Subset of the Naturals\<close>

interpretation Int : set_extension \<nat> int_rep int_rep_nonneg
  by unfold_locales auto

abbreviation "int \<equiv> Int.abs_image"

bundle isa_set_int_syntax begin notation int ("\<int>") end
bundle no_isa_set_int_syntax begin no_notation int ("\<int>") end

unbundle isa_set_int_syntax

abbreviation "Int \<equiv> Element \<int>"

lemmas nat_subset_int [simp, intro!] = Int.subset_abs_image

corollary Int_if_Nat [derive]: "n : Nat \<Longrightarrow> n : Int"
  using mem_if_mem_if_subset[OF nat_subset_int] by unfold_types


subsection \<open>Arithmetic operations lifted to Int\<close>

text \<open>We lift constants/functions from @{term "int_rep"} to @{term "\<int>"}
manually. This should be automated in the future using some technique similar
to lifting in Isabelle/HOL.\<close>

definition "int_nonneg n \<equiv> Int.Abs (int_rep_nonneg n)"
definition "int_neg n \<equiv> Int.Abs (int_rep_neg n)"
definition "int_succ i \<equiv> Int.Abs (int_rep_succ (Int.Rep i))"
definition "int_pred i \<equiv> Int.Abs (int_rep_pred (Int.Rep i))"
definition "int_inv i \<equiv> Int.Abs (int_rep_inv (Int.Rep i))"
definition "int_add i j \<equiv> Int.Abs (int_rep_add (Int.Rep i) (Int.Rep j))"
definition "int_sub i j \<equiv> Int.Abs (int_rep_sub (Int.Rep i) (Int.Rep j))"
definition "int_mul i j \<equiv> Int.Abs (int_rep_mul (Int.Rep i) (Int.Rep j))"

lemma
  shows int_nonneg_type [type]: "int_nonneg : Nat \<Rightarrow> Int"
  and int_neg_type [type]: "int_neg : Element (\<nat> \<setminus> {0}) \<Rightarrow> Int"
  and int_succ_type [type]: "int_succ : Int \<Rightarrow> Int"
  and int_pred_type [type]: "int_pred : Int \<Rightarrow> Int"
  and int_inv_type [type]: "int_inv : Int \<Rightarrow> Int"
  and int_add_type [type]: "int_add : Int \<Rightarrow> Int \<Rightarrow> Int"
  and int_sub_type [type]: "int_sub : Int \<Rightarrow> Int \<Rightarrow> Int"
  and int_mul_type [type]: "int_mul : Int \<Rightarrow> Int \<Rightarrow> Int"
  unfolding int_nonneg_def int_neg_def int_succ_def int_pred_def int_inv_def
    int_add_def int_sub_def int_mul_def
  (*TODO: should not need an increase*)
  using [[type_derivation_depth=3]]
  by discharge_types

text \<open>We need a notation package that also does inference to determine if a
number is a Nat, Int, etc. Typeclass integration here already?\<close>

bundle isa_set_int_add_syntax begin notation int_add (infixl "+" 65) end
bundle no_isa_set_int_add_syntax begin no_notation int_add (infixl "+" 65) end

bundle isa_set_int_sub_syntax begin notation int_sub (infixl "-" 65) end
bundle no_isa_set_int_sub_syntax begin no_notation int_sub (infixl "-" 65) end

bundle isa_set_int_mul_syntax begin notation int_mul (infixl "*" 70) end
bundle no_isa_set_int_mul_syntax begin no_notation int_mul (infixl "*" 70) end

unbundle
  no_isa_set_nat_add_syntax
  no_isa_set_nat_sub_syntax
  no_isa_set_nat_mul_syntax
  isa_set_int_add_syntax
  isa_set_int_sub_syntax
  isa_set_int_mul_syntax


(*TODO: no proper normal forms at the moment*)
subsubsection \<open>Examples\<close>

experiment begin

named_theorems arith
lemmas [arith] =
  int_nonneg_def int_neg_def int_add_def int_sub_def int_mul_def
  int_rep_zero_def[symmetric] int_rep_one_def[symmetric]
  int_rep_nonneg_succ_add_eq

text \<open>At some point we want to just be able to write \<open>succ n\<close> below, and
automatically infer that it has to have soft type \<open>Int\<close>.\<close>

schematic_goal
  "int_nonneg (succ 0) + int_nonneg (succ 0) + int_neg (succ 0) = ?a"
  by (simp add: arith)

schematic_goal
  "int_nonneg 0 * int_neg (succ 0) + int_nonneg (succ 0) - int_neg (succ 0) = ?a"
  by (simp add: arith)

end


subsection \<open>Algebraic Structures\<close>

text \<open>Additive group structure\<close>

definition "int_Group \<equiv> object {
    \<langle>@zero, 0\<rangle>,
    \<langle>@add, \<lambda>i j \<in> \<int>. int_add i j\<rangle>,
    \<langle>@inv, \<lambda>i \<in> \<int>. int_rep_inv i\<rangle>
  }"

bundle isa_set_int_Group_syntax
begin notation int_Group ("'(\<int>, +')") end
bundle no_isa_set_int_Monoid_syntax
begin no_notation int_Group ("'(\<int>, +')") end

unbundle isa_set_int_Group_syntax

(*TODO: The following should be automatically generated*)
lemma [simp]:
  "(\<int>, +) @@ zero = 0"
  "(\<int>, +) @@ add = \<lambda>i j \<in> \<int>. int_add i j"
  "(\<int>, +) @@ inv = \<lambda>i \<in> \<int>. int_rep_inv i"
  unfolding int_Group_def by simp_all

lemma "(\<int>, +) : Group \<int>"
(* proof (rule GroupI, rule MonoidI)
  show "(\<int>, +) : Zero \<int>" by (rule ZeroI) simp
  show "(\<int>, +) : Add \<int>"
  (*TODO: object selector simplifier not working properly*)
  (* unfolding nat_Monoid_def by (rule AddI) simp *)
  proof (rule AddI)
    have select_add_eq: "(\<int>, +)@@add = \<lambda>i j \<in> \<int>. int_add i j" by simp
    show "(\<int>, +)@@add : \<int> \<rightarrow> \<int> \<rightarrow> \<int>" by (subst select_add_eq) discharge_types
  qed
(*TODO: needs transferred theorems from representation type*)
qed (unfold add_def zero_def inv_def, auto) *)
oops


text \<open>Multiplicative monoid structure\<close>

definition "int_Mul_Monoid \<equiv> object {
    \<langle>@one, 1\<rangle>,
    \<langle>@mul, \<lambda>i j \<in> \<int>. int_mul i j\<rangle>
  }"

bundle isa_set_int_Mul_Monoid_syntax
begin notation int_Mul_Monoid ("'(\<int>, *')") end
bundle no_isa_set_int_Mul_Monoid_syntax
begin no_notation int_Mul_Monoid ("'(\<int>, *')") end

unbundle isa_set_int_Mul_Monoid_syntax

lemma int_mul_assoc:
  assumes "i : Int" "j : Int" "k : Int"
  shows "i * j * k = i * (j * k)"
  using assms int_rep_mul_assoc unfolding int_mul_def by simp

lemma "(\<int>, *) : Mul_Monoid \<int>"
\<comment> \<open>
proof (intro Mul_MonoidI)
  show "(\<int>, *) : One \<int>"
    unfolding int_Mul_Monoid_def by (rule OneI) simp
next
  show "(\<int>, *) : Mul \<int>"
    unfolding int_Mul_Monoid_def by (rule MulI) simp
next
  fix x assume "x \<in> \<int>"
  then show "mul int_Mul_Monoid (one int_Mul_Monoid) x = x" and
    "mul int_Mul_Monoid x (one int_Mul_Monoid) = x"
    unfolding int_Mul_Monoid_def mul_def one_def by auto
next
  fix x y z assume "x \<in> \<int>" "y \<in> \<int>" "z \<in> \<int>"
  show "mul int_Mul_Monoid (mul int_Mul_Monoid x y) z =
    mul int_Mul_Monoid x (mul int_Mul_Monoid y z)"
    (* using int_mul_assoc unfolding int_Mul_Monoid_def mul_def by simp *)
qed\<close>
oops

end
