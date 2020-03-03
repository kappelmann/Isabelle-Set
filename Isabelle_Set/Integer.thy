chapter \<open>Integers\<close>

theory Integer
  imports Nat Sum Set_Extension
begin

section \<open>Carrier of \<int>\<close>

text \<open>
  We construct the integers as a pair of a non-negative and a negative part.
  By using the set extension principle, we ensure that \<open>\<nat> \<subseteq> \<int>\<close>.
\<close>

definition "int_rep = Sum \<nat> (\<nat> \<setminus> {{}})"

\<comment> \<open>Some type derivation rule setup\<close>
lemma
  [type]: "succ: element \<nat> \<Rightarrow> element (\<nat> \<setminus> {{}})" and
  [type]: "inl : element \<nat> \<Rightarrow> element int_rep" and
  [type]: "inr : element (\<nat> \<setminus> {{}}) \<Rightarrow> element int_rep"
  unfolding int_rep_def by unfold_types auto

interpretation Int: set_extension \<nat> int_rep inl
proof
  text \<open>We must provide an injective function from \<open>\<nat>\<close> to \<open>int_rep\<close>:\<close>

  show "inl : element \<nat> \<Rightarrow> element int_rep"
    unfolding int_rep_def by (rule inl_type)

  show "\<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>. inl x = inl y \<longrightarrow> x = y" by auto
qed

abbreviation int ("\<int>") where "\<int> \<equiv> Int.def"

lemmas nat_in_int = Int.extension_subset

corollary [derive]: "n : element \<nat> \<Longrightarrow> n : element \<int>"
  apply unfold_types
  apply (rule subsetE)
  by (rule nat_in_int)


section \<open>Basic arithmetic\<close>

text \<open>
  We lift constants/functions from \<open>int_rep\<close> to \<open>\<int>\<close> manually.
  This should be automated in the future using some technique similar to
  transfer in Isabelle/HOL.
\<close>

definition "int_rep_add x y \<equiv> Sum_case
  (\<lambda>m. Sum_case
    (\<lambda>n. inl (m + n))
    (\<lambda>n. if m < n then inr (n - m) else inl (m - n))
    y)
  (\<lambda>m. Sum_case
    (\<lambda>n. if n < m then inr (m - n) else inl (n - m))
    (\<lambda>n. inr (m + n))
    y)
  x"

definition "int_rep_negate =
  Sum_case (\<lambda>n. if n = 0 then n else inr n) (\<lambda>n. inl n)"

definition "int_rep_sub x y = int_rep_add x (int_rep_negate y)"

definition "int_rep_mul x y \<equiv> Sum_case
  (\<lambda>m. Sum_case
    (\<lambda>n. inl (m \<cdot> n))
    (\<lambda>n. inr (m \<cdot> n))
    y)
  (\<lambda>m. Sum_case
    (\<lambda>n. inr (m \<cdot> n))
    (\<lambda>n. inl (m \<cdot> n))
    y)
  x"

definition "int_add x y = Int.Abs (int_rep_add (Int.Rep x) (Int.Rep y))"
definition "int_sub x y = Int.Abs (int_rep_sub (Int.Rep x) (Int.Rep y))"
definition "int_mul x y \<equiv> Int.Abs (int_rep_mul (Int.Rep x) (Int.Rep y))"

lemmas [arith] =
  int_rep_add_def int_rep_negate_def int_rep_sub_def int_rep_mul_def
  int_add_def int_sub_def int_mul_def

subsection \<open>Notation\<close>

text \<open>
  Need a notation package that also does inference to determine if a number is a
  Nat, Int, etc. Typeclass integration here already?...
\<close>

bundle notation_int_add begin notation int_add (infixl "+" 65) end
bundle no_notation_int_add begin no_notation int_add (infixl "+" 65) end

bundle notation_int_sub begin notation int_sub (infixl "-" 65) end
bundle no_notation_int_sub begin no_notation int_sub (infixl "-" 65) end

bundle notation_int_mul begin notation int_mul (infixl "\<cdot>" 65) end
bundle no_notation_int_mul begin no_notation int_mul (infixl "\<cdot>" 65) end

unbundle
  no_notation_nat_add
  no_notation_nat_sub

  notation_int_add
  notation_int_sub


section \<open>Examples\<close>

schematic_goal
  "Int.Abs (inl (succ 0)) + Int.Abs (inl (succ 0)) + Int.Abs (inr (succ 0))
    = Int.Abs (?a)"
  by (simp add: arith)

schematic_goal
  "Int.Abs (inl 0) - Int.Abs (inr (succ 0)) + Int.Abs (inl (succ 0)) -
    Int.Abs (inr (succ 0)) = Int.Abs (inl ?a)"
  by (simp add: arith)


section \<open>Instances for algebraic structures\<close>

definition "Int_mul_monoid \<equiv> object {\<langle>@one, 1\<rangle>, \<langle>@mul, \<lambda>m n\<in> \<int>. int_mul m n\<rangle>}"


end
