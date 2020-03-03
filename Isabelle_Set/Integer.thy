chapter \<open>Integers\<close>

theory Integer
  imports Nat Sum Set_Extension
begin

section \<open>Carrier of \<int>\<close>

text \<open>
  We construct the integers as a pair of a non-negative and a negative part.
  By using the set extension principle, we ensure that \<open>\<nat> \<subseteq> \<int>\<close>.
\<close>

definition "raw_int = Sum \<nat> (\<nat> \<setminus> {{}})"
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


section \<open>Basic arithmetic\<close>

definition "int_zero \<equiv> pos 0"

definition "int_add x y \<equiv> Sum_case
  (\<lambda>m. Sum_case
    (\<lambda>n. pos (m + n))
    (\<lambda>n. if m < n then neg (n - m) else pos (m - n))
    y)
  (\<lambda>m. Sum_case
    (\<lambda>n. if n < m then neg (m - n) else pos (n - m))
    (\<lambda>n. neg (m + n))
    y)
  x"

definition "negate = Sum_case (\<lambda>n. if n = 0 then n else neg n) (\<lambda>n. pos n)"

definition "int_sub x y = int_add x (negate y)"

lemmas [arith] =
  int_zero_def pos_def neg_def negate_def int_add_def int_sub_def

subsection \<open>Notations\<close>

text \<open>
  Need a notation package that also does inference to determine if a number is a
  Nat, Int, etc. Typeclass integration here already?...
\<close>

bundle notation_int_zero begin notation int_zero ("0") end
bundle no_notation_int_zero begin no_notation int_zero ("0") end

bundle notation_int_add begin notation int_add (infixl "+" 65) end
bundle no_notation_int_add begin no_notation int_add (infixl "+" 65) end

bundle notation_int_sub begin notation int_sub (infixl "-" 65) end
bundle no_notation_int_sub begin no_notation int_sub (infixl "-" 65) end

unbundle
  no_notation_nat_add
  no_notation_nat_sub

  notation_int_add
  notation_int_sub

\<comment> \<open>Examples\<close>
schematic_goal
  "pos 0 - neg (succ 0) + pos (succ 0) - pos (succ 0) = pos (?a)"
  apply (simp add: arith) done



end