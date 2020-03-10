chapter \<open>Integers\<close>

theory Integer
  imports Nat Sum Set_Extension
begin

section \<open>Carrier of \<int>\<close>

text \<open>
  We construct the integers as a pair of a non-negative and a negative part.
  By using the set extension principle, we ensure that \<open>\<nat> \<subseteq> \<int>\<close>.
\<close>

definition "int_rep = Sum \<nat> (\<nat> \<setminus> {0})"

\<comment> \<open>Some type derivation rule setup\<close>
lemma
  [type]: "succ: element \<nat> \<Rightarrow> element (\<nat> \<setminus> {0})" and
  [type]: "inl : element \<nat> \<Rightarrow> element int_rep" and
  [type]: "inr : element (\<nat> \<setminus> {0}) \<Rightarrow> element int_rep"
  unfolding int_rep_def by unfold_types auto

interpretation Int: set_extension \<nat> int_rep inl
  proof qed auto

abbreviation int ("\<int>") where "\<int> \<equiv> Int.def"
abbreviation "pos n \<equiv> Int.Abs (inl n)"
abbreviation "neg n \<equiv> Int.Abs (inr n)"

lemmas nat_subset_int [simp] = Int.extension_subset

abbreviation "Int \<equiv> element \<int>"

corollary [derive]: "n : Nat \<Longrightarrow> n : Int"
  by (unfold_types, rule subsetE) auto


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

definition "int_rep_mul x y \<equiv> Sum_case
  (\<lambda>m. Sum_case
    (\<lambda>n. inl (m \<cdot> n))
    (\<lambda>n. if m = 0 then inl 0 else inr (m \<cdot> n))
    y)
  (\<lambda>m. Sum_case
    (\<lambda>n. if n = 0 then inl 0 else inr (m \<cdot> n))
    (\<lambda>n. inl (m \<cdot> n))
    y)
  x"

definition "int_rep_negate =
  Sum_case (\<lambda>n. if n = 0 then inl n else inr n) (\<lambda>n. inl n)"

definition "int_rep_sub x y = int_rep_add x (int_rep_negate y)"

definition "int_add x y = Int.Abs (int_rep_add (Int.Rep x) (Int.Rep y))"
definition "int_mul x y \<equiv> Int.Abs (int_rep_mul (Int.Rep x) (Int.Rep y))"
definition "int_negate x \<equiv> Int.Abs (int_rep_negate (Int.Rep x))"
definition "int_sub x y = Int.Abs (int_rep_sub (Int.Rep x) (Int.Rep y))"

lemmas [arith] =
  int_rep_add_def int_rep_negate_def int_rep_sub_def int_rep_mul_def
  int_add_def int_sub_def int_mul_def

subsection \<open>Typing\<close>

lemma [type]:
  "int_rep_add : element int_rep \<Rightarrow> element int_rep \<Rightarrow> element int_rep"
  unfolding int_rep_def int_rep_add_def
  by (unfold_types, erule SumE; erule SumE) auto

lemma [type]:
  "int_rep_mul : element int_rep \<Rightarrow> element int_rep \<Rightarrow> element int_rep"
  unfolding int_rep_def int_rep_mul_def
  by (unfold_types, erule SumE; erule SumE) auto

lemma [type]:
  "int_rep_negate : element int_rep \<Rightarrow> element int_rep"
  unfolding int_rep_def int_rep_negate_def
  by unfold_types auto

lemma [type]:
  "int_rep_sub : element int_rep \<Rightarrow> element int_rep \<Rightarrow> element int_rep"
  unfolding int_rep_sub_def by auto

lemma
  int_add_type [type]: "int_add : Int \<Rightarrow> Int \<Rightarrow> Int" and
  int_mul_type [type]: "int_mul : Int \<Rightarrow> Int \<Rightarrow> Int" and
  int_negate_type [type]: "int_negate : Int \<Rightarrow> Int" and
  int_sub_type [type]: "int_sub : Int \<Rightarrow> Int \<Rightarrow> Int"
  unfolding int_add_def int_mul_def int_negate_def int_sub_def by auto

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

text \<open>
  At some point we want to just be able to write \<open>succ n\<close> below, and
  automatically infer that it has to have soft type \<open>Int\<close>.
\<close>

schematic_goal
  "pos (succ 0) + pos (succ 0) + neg (succ 0) = ?a"
  by (simp add: arith)

schematic_goal
  "pos 0 - neg (succ 0) + pos (succ 0) - neg (succ 0) = ?a"
  by (simp add: arith)


section \<open>Algebraic properties\<close>

subsection \<open>Additive group structure\<close>

definition Int_group ("'(\<int>, +')") where
  "(\<int>, +) \<equiv> object {
    \<langle>@zero, 0\<rangle>,
    \<langle>@add, \<lambda>x y\<in> \<int>. int_add x y\<rangle>,
    \<langle>@inv, \<lambda>x\<in> \<int>. int_negate x\<rangle>
  }"

text \<open>Again, the following should be automatically generated.\<close>

lemma [simp]:
  "(\<int>, +) @@ zero = 0"
  "(\<int>, +) @@ add = \<lambda>x y\<in> \<int>. int_add x y"
  "(\<int>, +) @@ inv = \<lambda>x\<in> \<int>. int_negate x"
  unfolding Int_group_def by simp_all

lemma Int_group: "(\<int>, +) : Group \<int>"
oops

subsection \<open>Multiplicative monoid structure\<close>

definition "Int_mul_monoid \<equiv> object {
  \<langle>@one, 1\<rangle>,
  \<langle>@mul, \<lambda>m n\<in> \<int>. int_mul m n\<rangle>
}"


end
