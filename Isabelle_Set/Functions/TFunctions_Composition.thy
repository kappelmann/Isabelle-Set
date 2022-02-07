subsection \<open>Composition\<close>
theory TFunctions_Composition
  imports TFunctions_Base
begin

lemma Dep_Function_comp_right_unique:
  assumes f_type: "f : (x : B) \<rightarrow> (C x)"
  and g_type: "g : A \<rightarrow> B"
  shows "right_unique A (f \<circ> g)"
proof -
  have "right_unique (rng (g\<restriction>A)) f"
  proof -
    from f_type have "right_unique B f"
      by (blast dest: Dep_Function_right_unique)
    moreover from g_type have "rng (g\<restriction>A) \<subseteq> dom (f\<restriction>B)" by (auto 0 3)
    ultimately show ?thesis by (auto elim!: right_unique_contravariant_pred)
  qed
  then show ?thesis
    using assms by (auto intro: right_unique_compI
      dest: Dep_Function_right_unique elim: right_unique_contravariant_pred)
qed

lemma Dep_Function_comp_eval_eq [simp]:
  assumes f_type: "f : (x : B) \<rightarrow> (C x)"
  and g_type: "g : A \<rightarrow> B"
  and x_type: "x : A"
  shows "(f \<circ> g)`x = f`(g`x)"
proof (rule eval_eqI)
  show "x : A" by (fact x_type)
  from assms show "\<langle>x, f`(g`x)\<rangle> \<in> f \<circ> g" by auto
qed (insert Dep_Function_comp_right_unique[OF assms(1-2)], auto)

lemma comp_type_Dep_Function [type]:
  "(\<circ>) : ((x : B) \<rightarrow> C x) \<Rightarrow> (g : A \<rightarrow> B) \<Rightarrow> (x : A) \<rightarrow> C (g`x)"
proof (intro Dep_fun_typeI Dep_FunctionI)
  fix f g assume "f : (x : B) \<rightarrow> C x" "g : A \<rightarrow> B"
  then show "right_unique A (f \<circ> g)" by (rule Dep_Function_comp_right_unique)
qed auto

lemma comp_type_CDep_Function [type]:
  "(\<circ>) : ((x : B) \<rightarrow> C x) \<Rightarrow> (g : A \<rightarrow>c B) \<Rightarrow> (x : A) \<rightarrow>c C (g`x)"
proof (intro Dep_fun_typeI CDep_FunctionI Dep_Bin_RelI)
  fix f g p assume f_g_types: "f : (x : B) \<rightarrow> C x" "g : A \<rightarrow>c B" and "p \<in> f \<circ> g"
  then obtain x y z where "\<langle>x, y\<rangle> \<in> g" "\<langle>y, z\<rangle> \<in> f" "p = \<langle>x, z\<rangle>" by auto
  moreover with f_g_types have "x : A" "y : B" "g`x = y" by auto
  moreover with \<open>\<langle>y, z\<rangle> \<in> f\<close> f_g_types have "z : C y" by auto
  ultimately show "p : \<Sum>x : A. (C (g`x))" by simp
qed auto

lemma Function_lambda_comp_lambda_eq [simp]:
  assumes "f : Element A \<Rightarrow> Element B"
  shows "(\<lambda>y \<in> B. g y) \<circ> (\<lambda>x \<in> A. f x) = \<lambda>x \<in> A. g (f x)"
  using assms by (intro eqI) auto

end
