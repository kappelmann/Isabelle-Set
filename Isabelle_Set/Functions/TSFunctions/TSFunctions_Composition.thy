\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Composition\<close>
theory TSFunctions_Composition
  imports TSFunctions_Base
begin

unbundle no_comp_syntax
unbundle no_restrict_syntax

lemma Dep_Function_comp_set_right_unique_on:
  assumes f_type: "f : (x : B) \<rightarrow>s (C x)"
  and g_type: "g : A \<rightarrow>s B"
  shows "set_right_unique_on A (f \<circ> g)"
proof -
  have "set_right_unique_on (rng g\<restriction>\<^bsub>A\<^esub> \<inter> dom f) f"
  proof -
    from f_type have "set_right_unique_on (type_pred B) f"
      by (auto dest: Dep_Function_set_right_unique_on)
    then have "set_right_unique_on (mem_of (rng g\<restriction>\<^bsub>A\<^esub> \<inter> dom f)) f"
      using antimono'D[OF antimono'_set_right_unique_on_pred]
      by (rule le_boolD'')
      (insert g_type, auto intro!: le_predI elim!: mem_set_restrict_leftE)
    then show ?thesis by simp
  qed
  then show ?thesis using assms by (auto intro!: set_right_unique_on_compI
    dest: Dep_Function_set_right_unique_on)
qed

lemma Dep_Function_comp_eval_eq [simp]:
  assumes f_type: "f : (x : B) \<rightarrow>s (C x)"
  and g_type: "g : A \<rightarrow>s B"
  and x_type: "x : A"
  shows "(f \<circ> g)`x = f`(g`x)"
proof (rule eval_eqI)
  show "x : A" by (fact x_type)
  from assms show "\<langle>x, f`(g`x)\<rangle> \<in> f \<circ> g" by auto
qed (insert Dep_Function_comp_set_right_unique_on[OF f_type g_type], auto)

lemma set_comp_type_Dep_Function [type]:
  "(\<circ>) : ((x : B) \<rightarrow>s C x) \<Rightarrow> (g : A \<rightarrow>s B) \<Rightarrow> (x : A) \<rightarrow>s C (g`x)"
proof (intro Dep_fun_typeI Dep_FunctionI)
  fix f g assume "f : (x : B) \<rightarrow>s C x" "g : A \<rightarrow>s B"
  then show "set_right_unique_on A (f \<circ> g)"
    by (rule Dep_Function_comp_set_right_unique_on)
qed auto

lemma comp_type_CDep_Function [type]:
  "(\<circ>) : ((x : B) \<rightarrow>s C x) \<Rightarrow> (g : A \<rightarrow>cs B) \<Rightarrow> (x : A) \<rightarrow>cs C (g`x)"
proof (intro Dep_fun_typeI CDep_FunctionI Dep_Bin_RelI)
  fix f g p assume f_g_types: "f : (x : B) \<rightarrow>s C x" "g : A \<rightarrow>cs B" and "p \<in> f \<circ> g"
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
