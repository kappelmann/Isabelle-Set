theory TLifting_Functions
  imports
    Lifting_Functions
    Soft_Types.Soft_Types_HOL
begin

lemma fun_typeI: "(\<And>x. x : A \<Longrightarrow> f x : B) \<Longrightarrow> f : A \<Rightarrow> B"
  using Dep_fun_typeI .

lemma fun_typeE: "\<lbrakk>f : A \<Rightarrow> B; x : A\<rbrakk> \<Longrightarrow> f x : B"
  using Dep_fun_typeE .

lemma id_type[type]: "id : A \<Rightarrow> A"
  apply (rule fun_typeI)
  unfolding id_def .

lemma fun_map_type':
  assumes rep_type: "f : a \<Rightarrow> b"
  and abs_type: "g : c \<Rightarrow> d"
  and f_type: "h : b \<Rightarrow> c"
  shows "fun_map f g h : a \<Rightarrow> d"
  unfolding fun_map_def dep_fun_map_def
  apply (rule Dep_fun_typeI)
  apply (rule fun_typeE[OF abs_type])
  apply (rule fun_typeE[OF f_type])
  apply (rule fun_typeE[OF rep_type])
  apply assumption
  done

lemma fun_map_type[type]: "fun_map : (A \<Rightarrow> B) \<Rightarrow> (C \<Rightarrow> D) \<Rightarrow> (B \<Rightarrow> C) \<Rightarrow> A \<Rightarrow> D"
  apply (rule fun_typeI, rule fun_typeI, rule fun_typeI)
  apply (rule fun_map_type')
  apply assumption+
  done


end