theory Integer
  imports Natural_Numbers Sum_Type Set_Extension
begin

text \<open>
  We construct the integers as a sum of a non-negative and a negative part.
  By using the set extension principle, we make sure that \<open>\<nat> \<subseteq> \<int>\<close>.
\<close>

definition "raw_int = Sum_Type \<nat> (\<nat> \<setminus> {})"
                               
interpretation INT: set_extension \<nat> raw_int Inl
proof                         
  show "Inl : element \<nat> \<Rightarrow> element raw_int"
    unfolding raw_int_def by (rule Inl_type)

  show "\<forall>x \<in> \<nat>. \<forall>y \<in> \<nat>. Inl x = Inl y \<longrightarrow> x = y" by auto
qed

notation INT.def ("\<int>")





end