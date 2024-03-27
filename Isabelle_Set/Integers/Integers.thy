section \<open>Integers\<close>
theory Integers
  imports
    Integers_Rep
    Set_Extensions
begin

unbundle no_HOL_groups_syntax no_hotg_add_syntax

subsection \<open>The Integers as a Subset of the Naturals\<close>

interpretation Int : set_extension \<nat> int_rep Int_Rep_nonneg
  by unfold_locales (auto intro: ElementI)

abbreviation "int \<equiv> Int.Abs"

bundle isa_set_int_syntax begin notation int ("\<int>") end
bundle no_isa_set_int_syntax begin no_notation int ("\<int>") end

unbundle isa_set_int_syntax

abbreviation "Int \<equiv> Element \<int>"

lemmas nat_subset_int [iff] = Int.Core_subset_Abs

corollary Int_if_Nat [derive]: "n : Nat \<Longrightarrow> n : Int"
  using subsetD[OF nat_subset_int] by unfold_types


subsection \<open>Arithmetic operations lifted to Int\<close>

text \<open>We lift constants/functions from @{term "Int_Rep"} to @{term "\<int>"}
manually. This should be automated in the future; cf. @{file Integers_Transport.thy}.\<close>

definition "int_nonneg n \<equiv> Int.l (Int_Rep_nonneg n)"
definition "int_neg n \<equiv> Int.l (Int_Rep_neg n)"
definition "int_succ i \<equiv> Int.l (Int_Rep_succ (Int.r i))"
definition "int_pred i \<equiv> Int.l (Int_Rep_pred (Int.r i))"
definition "int_inv i \<equiv> Int.l (Int_Rep_inv (Int.r i))"
definition "int_add i j \<equiv> Int.l (Int_Rep_add (Int.r i) (Int.r j))"
definition "int_sub i j \<equiv> Int.l (Int_Rep_sub (Int.r i) (Int.r j))"
definition "int_mul i j \<equiv> Int.l (Int_Rep_mul (Int.r i) (Int.r j))"

(*TODO: automatic translation between @{term "Nat \<Coprod> Element (\<nat> \<setminus> {0})"}
and @{term "Element (\<nat> \<Coprod> \<nat> \<setminus> {0})"} not working at the moment;
maybe we want to introduce extensionality for types?*)
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
oops
  (* using [[type_derivation_depth=3]] *)
  (* by auto *)

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
  Int_Rep_zero_def[symmetric] Int_Rep_one_def[symmetric]
  Int_Rep_nonneg_succ_add_eq

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
    \<langle>@inv, \<lambda>i \<in> \<int>. Int_Rep_inv i\<rangle>
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
  "(\<int>, +) @@ inv = \<lambda>i \<in> \<int>. Int_Rep_inv i"
  unfolding int_Group_def by simp_all

lemma "(\<int>, +) : Group Int"
(* proof (rule GroupI, rule MonoidI)
  show "(\<int>, +) : Zero Int" by (rule ZeroI) simp
  show "(\<int>, +) : Add Int"
  (*TODO: object selector simplifier not working properly*)
  (* unfolding nat_Monoid_def by (rule AddI) simp *)
  proof (rule AddI)
    have select_add_eq: "(\<int>, +)@@add = \<lambda>i j \<in> \<int>. int_add i j" by simp
    show "(\<int>, +)@@add : Int \<rightarrow>s Int \<rightarrow>s Int" by (subst select_add_eq) discharge_types
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

(* lemma int_mul_assoc:
  assumes "i : Int" "j : Int" "k : Int"
  shows "i * j * k = i * (j * k)"
  (* using assms Int_Rep_mul_assoc unfolding int_mul_def by simp *)
oops *)

lemma "(\<int>, *) : Mul_Monoid Int"
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
