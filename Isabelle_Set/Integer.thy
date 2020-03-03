chapter \<open>Integers\<close>

theory Integer
  imports Nat Sum Set_Extension
begin

section \<open>Carrier of \<int>\<close>

text \<open>
  We construct the integers as a pair of a non-negative and a negative part.
  By using the set extension principle, we ensure that \<open>\<nat> \<subseteq> \<int>\<close>.
\<close>

definition "raw_int = Sum \<nat> (\<nat> \<setminus> {0})"
definition "pos = inl" \<comment> \<open>includes 0\<close>
definition "neg = inr"

interpretation Int: set_extension \<nat> raw_int pos
proof
  txt \<open>We must provide an injective function from \<open>\<nat>\<close> to \<open>raw_int\<close>:\<close>

  show "pos : element \<nat> \<Rightarrow> element raw_int"
    unfolding pos_def raw_int_def by (rule inl_type)

  show "\<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>. pos x = pos y \<longrightarrow> x = y"
    unfolding pos_def by auto
qed

abbreviation int ("\<int>") where "\<int> \<equiv> Int.def"

lemmas nat_in_int = Int.extension_subset

corollary [derive]: "n : element \<nat> \<Longrightarrow> n : element \<int>"
  apply unfold_types
  apply (rule subsetE)
  by (rule nat_in_int)


text\<open>In the following, we lift constants/functions from raw_int to \<int> manually.
This should be automated in the future using some technique similar to transfer
in Isabelle/HOL.\<close>


section \<open>Basic arithmetic\<close>

definition "raw_int_add x y \<equiv> Sum_case
  (\<lambda>m. Sum_case
    (\<lambda>n. pos (m + n))
    (\<lambda>n. if m < n then neg (n - m) else pos (m - n))
    y)
  (\<lambda>m. Sum_case
    (\<lambda>n. if n < m then neg (m - n) else pos (n - m))
    (\<lambda>n. neg (m + n))
    y)
  x"

definition "int_add x y = Int.Abs (raw_int_add (Int.Rep x) (Int.Rep y))"

text \<open>
  Need a notation package that also does inference to determine if a number is a
  Nat, Int, etc. Typeclass integration here already?...
\<close>

bundle notation_int_add
begin notation int_add (infixl "+" 65)
end

bundle no_notation_int_add
begin no_notation int_add (infixl "+" 65)
end

unbundle no_notation_nat_add
unbundle notation_int_add

text\<open>Note: This should maybe be changed to use the inverse instead.\<close>
definition "raw_int_sub x y = Sum_case
  (\<lambda>m. Sum_case
    (\<lambda>n. if n \<le> m then pos (m - n) else neg (n - m))
    (\<lambda>n. pos (m + n))
    y)
  (\<lambda>m. Sum_case
    (\<lambda>n. neg (m + n))
    (\<lambda>n. if m \<le> n then pos (n - m) else neg (m - n))
    y)
  x"

definition "int_sub x y = Int.Abs (raw_int_sub (Int.Rep x) (Int.Rep y))"

definition "raw_int_mul x y \<equiv> Sum_case
  (\<lambda>n. Sum_case
    (\<lambda>m. pos (n \<cdot> m))
    (\<lambda>m. neg (n \<cdot> m))
    y)
  (\<lambda>n. Sum_case
    (\<lambda>m. neg (n \<cdot> m))
    (\<lambda>m. pos (n \<cdot> m))
    y)
  x"

definition "int_mul x y \<equiv> Int.Abs (raw_int_mul (Int.Rep x) (Int.Rep y))"

bundle notation_int_mul
begin notation int_mul (infixl "\<cdot>" 65)
end

bundle no_notation_int_mul
begin no_notation int_mul (infixl "\<cdot>" 65)
end

lemmas [arith] = pos_def neg_def int_add_def raw_int_add_def int_sub_def
  raw_int_sub_def int_mul_def raw_int_mul_def


subsection\<open>Examples\<close>

text\<open>The next examples should compute without any intermediate steps.
The premises of Int.Abs_inverse should be discharged automatically by the type
inference tooling.\<close>

(*
notepad
begin
  have "Int.Abs (pos (succ 0)) + Int.Abs (pos (succ 0)) + Int.Abs (neg (succ 0))
    = Int.Abs (pos (succ 0))"
  proof -
    have "pos (succ 0) \<in> raw_int" unfolding raw_int_def pos_def by simp
    moreover have "pos (succ (succ 0)) \<in> raw_int"
      unfolding raw_int_def pos_def by simp
    moreover have "neg (succ 0) \<in> raw_int" unfolding raw_int_def neg_def sorry
    ultimately show ?thesis using Int.Abs_inverse by (simp add: arith)
  qed
end

schematic_goal
  "pos 0 + neg (succ 0) + pos (succ 0) + neg (succ 0) = neg (?a)"
  using Int.Abs_inverse by (simp add: arith) oops
*)

section \<open>Instances for algebraic structures\<close>

definition "Int_mul_monoid \<equiv> object {\<langle>@one, 1\<rangle>, \<langle>@mul, \<lambda>n m \<in> \<int>. int_mul n m\<rangle>}"


end