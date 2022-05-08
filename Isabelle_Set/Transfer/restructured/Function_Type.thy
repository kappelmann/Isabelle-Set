theory Function_Type
  imports Function Soft_Types.Soft_Types_HOL
begin

lemma fun_typeI: "(\<And>x. x : A \<Longrightarrow> f x : B) \<Longrightarrow> f : A \<Rightarrow> B"
  using Dep_fun_typeI .

lemma fun_typeE: "\<lbrakk>f : A \<Rightarrow> B; x : A\<rbrakk> \<Longrightarrow> f x : B"
  using Dep_fun_typeE .

lemma id_type[type]: "id : A \<Rightarrow> A"
  apply (rule fun_typeI)
  unfolding id_def .


lemma map_fun_type':
  assumes rep_type: "f : a \<Rightarrow> b"
      and abs_type: "g : c \<Rightarrow> d"
      and f_type: "h : b \<Rightarrow> c"
    shows "map_fun f g h : a \<Rightarrow> d"
  unfolding map_fun_def dep_map_fun_def
  apply (rule Dep_fun_typeI)
  apply (rule fun_typeE[OF abs_type])
  apply (rule fun_typeE[OF f_type])
  apply (rule fun_typeE[OF rep_type])
  apply assumption
  done

lemma map_fun_type[type]: "map_fun : (A \<Rightarrow> B) \<Rightarrow> (C \<Rightarrow> D) \<Rightarrow> (B \<Rightarrow> C) \<Rightarrow> A \<Rightarrow> D"
  apply (rule fun_typeI, rule fun_typeI, rule fun_typeI)
  apply (rule map_fun_type')
  apply assumption+
  done

lemma in_dom_iff_Eq_rep_self: "in_dom T x = Eq_rep T x x"
  using Eq_rep_self Eq_rep_then_in_dom by fast

lemma in_dom_no_dep_fun:
  assumes "transfer_triple T1 abs1 rep1" "transfer_triple T2 abs2 rep2"
  shows "in_dom (T1 \<Rrightarrow> T2) f = (\<forall>x1 x2. Eq_rep T1 x1 x2 \<longrightarrow> Eq_rep T2 (f x1) (f x2))"
  apply (subst in_dom_iff_Eq_rep_self)
  apply (subst Eq_rep_no_dep_rel_fun_dist[OF assms])
  unfolding no_dep_rel_fun_def dep_rel_fun_def ..

lemma in_dom_no_dep_fun':
  assumes "transfer_triple T1 abs1 rep1" "transfer_triple T2 abs2 rep2"
    "\<And>x1 x2. Eq_rep T1 x1 x2 \<Longrightarrow> Eq_rep T2 (f x1) (f x2)"
  shows "in_dom (T1 \<Rrightarrow> T2) f"
  using assms in_dom_no_dep_fun by fast

end