chapter \<open>Integers\<close>

theory Integer
  imports Nat Sum Set_Extension
begin

section \<open>Construction of the carrier\<close>

text \<open>
  We construct the integers as a pair of a non-negative and a negative part.
  By using the set extension principle, we ensure that \<open>\<nat> \<subseteq> \<int>\<close>.
\<close>

definition "raw_int = Sum \<nat> (\<nat> \<setminus> {})"

interpretation Int: set_extension \<nat> raw_int inl
proof
  txt \<open>We must provide an injective function from \<open>\<nat>\<close> to \<open>raw_int\<close>:\<close>

  show "inl : element \<nat> \<Rightarrow> element raw_int"
    unfolding raw_int_def by (rule inl_type)

  show "\<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>. inl x = inl y \<longrightarrow> x = y" by auto
qed

definition "int = Int.def"
notation int ("\<int>")

lemma nat_in_int: "\<nat> \<subseteq> \<int>"
  unfolding int_def by (rule Int.extension_subset)

corollary [derive]: "n : element \<nat> \<Longrightarrow> n : element \<int>"
  apply unfold_types
  apply (rule subsetE)
  by (rule nat_in_int)


section \<open>Basic arithmetic\<close>

definition "int_zero \<equiv> inl 0"

bundle notation_int_zero
begin notation int_zero ("0")
end

bundle no_notation_int_zero
begin no_notation int_zero ("0")
end

unbundle no_notation_nat_zero
unbundle notation_int_zero

definition "int_add x y \<equiv> Sum_case
  (\<lambda>n. Sum_case
    (\<lambda>m. inl (n + m))
    (\<lambda>m. if n < m then inr (m - n) else inl (n - m))
    y)
  (\<lambda>n. Sum_case
    (\<lambda>m. if m < n then inr (n - m) else inl (m - n))
    (\<lambda>m. inr (n + m))
    y)
  x"

bundle notation_int_add
begin notation int_add (infixl "+" 65)
end

bundle no_notation_int_add
begin no_notation int_add (infixl "+" 65)
end

unbundle no_notation_nat_add
unbundle notation_int_add

unbundle no_notation_int_zero
unbundle notation_nat_zero

lemma "inl (succ 0) + inl (succ 0) + inr (succ 0) = inl (succ 0)"
  by (simp add: int_add_def nat_add_def nat_sub_def)


end