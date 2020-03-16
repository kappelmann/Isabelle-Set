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

definition "int_rep_negate =
  Sum_case (\<lambda>n. if n = 0 then inl n else inr n) (\<lambda>n. inl n)"

definition "int_rep_sub x y = int_rep_add x (int_rep_negate y)"

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

definition "int_add x y = Int.Abs (int_rep_add (Int.Rep x) (Int.Rep y))"
definition "int_negate x = Int.Abs (int_rep_negate (Int.Rep x))"
definition "int_sub x y = Int.Abs (int_rep_sub (Int.Rep x) (Int.Rep y))"
definition "int_mul x y \<equiv> Int.Abs (int_rep_mul (Int.Rep x) (Int.Rep y))"

lemmas [arith] =
  int_rep_add_def int_rep_negate_def int_rep_sub_def int_rep_mul_def
  int_add_def int_sub_def int_mul_def

subsection \<open>Typing\<close>

\<comment> \<open>Note Kevin: I do not think unfolding everything for the following
functions is a good idea. I think we want to get the type system up to a point
where this is handled by said system.\<close>
lemma int_rep_add_type [type]:
  "int_rep_add : element int_rep \<Rightarrow> element int_rep \<Rightarrow> element int_rep"
proof -
  have [dest]: "\<And>m n. m \<in> \<nat> \<Longrightarrow> n \<in> \<nat> \<Longrightarrow> m < n \<Longrightarrow> 0 < n - m"
    using nat_zero_lt_sub by simp
  show ?thesis unfolding int_rep_def int_rep_add_def
  by (unfold_types, erule SumE; erule SumE) auto
qed

lemma [type]:
  "int_rep_negate : element int_rep \<Rightarrow> element int_rep"
  unfolding int_rep_def int_rep_negate_def
  by unfold_types auto

lemma int_rep_sub_type [type]:
  "int_rep_sub : element int_rep \<Rightarrow> element int_rep \<Rightarrow> element int_rep"
  unfolding int_rep_sub_def by auto

lemma int_rep_mul_type [type]:
  "int_rep_mul : element int_rep \<Rightarrow> element int_rep \<Rightarrow> element int_rep"
  unfolding int_rep_def int_rep_mul_def
  by (unfold_types, erule SumE; erule SumE) (auto simp: nat_mul_ne_zero)

lemma
  int_add_type [type]: "int_add : Int \<Rightarrow> Int \<Rightarrow> Int" and
  int_negate_type [type]: "int_negate : Int \<Rightarrow> Int" and
  int_sub_type [type]: "int_sub : Int \<Rightarrow> Int \<Rightarrow> Int" and
  int_mul_type [type]: "int_mul : Int \<Rightarrow> Int \<Rightarrow> Int"
  unfolding int_add_def int_negate_def int_sub_def int_mul_def by auto

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
  no_notation_nat_mul

  notation_int_add
  notation_int_sub
  notation_int_mul


subsection \<open>Basic arithmetic properties\<close>

text\<open>First for the raw representation:\<close>

lemma int_rep_one_mul: assumes "x \<in> int_rep"
  shows "int_rep_mul (inl 1) x = x"
  using assms unfolding int_rep_def int_rep_mul_def
  by (rule SumE) auto

lemma int_rep_mul_one: assumes "x \<in> int_rep"
  shows "int_rep_mul x (inl 1) = x"
  using assms unfolding int_rep_def int_rep_mul_def
  by (rule SumE) auto

lemma int_rep_mul_assoc: assumes "x \<in> int_rep" "y \<in> int_rep" "z \<in> int_rep"
  shows "int_rep_mul (int_rep_mul x y) z = int_rep_mul x (int_rep_mul y z)"
  unfolding int_rep_def int_rep_mul_def by (
    rule SumE[OF assms(1)[unfolded int_rep_def]];
    rule SumE[OF assms(2)[unfolded int_rep_def]];
    rule SumE[OF assms(3)[unfolded int_rep_def]])
    (auto simp: nat_mul_assoc nat_mul_ne_zero)

text\<open>Now lift the results to the actual set \<int>. This should be automated in some
way in the future.\<close>

lemma int_one_mul [simp]: assumes "x : Int" shows "1 \<cdot> x = x"
proof -
  have "Int.Rep 1 = inl 1" unfolding Int.Rep_def by simp
  with int_rep_one_mul show ?thesis unfolding int_mul_def by simp
qed

lemma int_mul_one [simp]: assumes "x : Int" shows "x \<cdot> 1 = x"
proof -
  have "Int.Rep 1 = inl 1" unfolding Int.Rep_def by simp
  with int_rep_mul_one show ?thesis unfolding int_mul_def by simp
qed

lemma int_mul_assoc: assumes "x : Int" "y : Int" "z : Int"
  shows "x \<cdot> y \<cdot> z = x \<cdot> (y \<cdot> z)"
  using assms int_rep_mul_assoc unfolding int_mul_def by simp

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

lemma "Int_mul_monoid : Mul_Monoid \<int>"
proof unfold_types
  show "Int_mul_monoid @@ one \<in> \<int>" and "Int_mul_monoid @@ mul \<in> \<int> \<rightarrow> \<int> \<rightarrow> \<int>"
  unfolding Int_mul_monoid_def by auto
next
  fix x assume "x \<in> \<int>"
  show "mul Int_mul_monoid (one Int_mul_monoid) x = x" and
    "mul Int_mul_monoid x (one Int_mul_monoid) = x"
    unfolding Int_mul_monoid_def mul_def one_def by auto
next
  fix x y z assume "x \<in> \<int>" "y \<in> \<int>" "z \<in> \<int>"
  show "mul Int_mul_monoid (mul Int_mul_monoid x y) z =
    mul Int_mul_monoid x (mul Int_mul_monoid y z)"
    using int_mul_assoc unfolding Int_mul_monoid_def mul_def one_def by auto
qed


end
