chapter \<open>Integers\<close>

theory Integer
  imports Nat Sum Set_Extension
begin

section \<open>Construction of the carrier\<close>

text \<open>
  We construct the integers as a pair of a non-negative and a negative part.
  By using the set extension principle, we make sure that \<open>\<nat> \<subseteq> \<int>\<close>.
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


section \<open>Basic arithmetic operations\<close>



end