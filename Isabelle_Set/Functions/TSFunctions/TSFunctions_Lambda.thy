\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Lambda Abstractions\<close>
theory TSFunctions_Lambda
  imports TSFunctions_Base
begin

lemma lambda_type [type]:
  "lambda : (A : Set) \<Rightarrow> ((x : Element A) \<Rightarrow> B x) \<Rightarrow> (x : Element A) \<rightarrow>cs B x"
  by unfold_types auto

(*TODO: it is necessery to specify this backward_derive rule since although
above type rule encodes that the type of f depends on A, this will not be
used in the type_derivator when proving `lambda A f : T`; more specifically,
the derivator will merely derivate types for A and f and then see if they can be
fed to Dep_fun_typeE together with lambda_type*)
lemma lambda_app_type [backward_derive]:
  assumes "f : (x : Element A) \<Rightarrow> B x"
  shows "lambda A f : (x : Element A) \<rightarrow>cs B x"
  by discharge_types

lemma Dep_Function_restrict_eq_lambdaI:
  assumes "f : (x : A) \<rightarrow>s B x"
  and "\<And>x. x \<in> A' \<Longrightarrow> x : A"
  shows "f\<restriction>\<^bsub>A'\<^esub> = (\<lambda>x \<in> A'. f`x)"
proof (rule eqI)
  fix p assume "p \<in> f\<restriction>\<^bsub>A'\<^esub>"
  then obtain x y where "p = \<langle>x, y\<rangle>" "\<langle>x, y\<rangle> \<in> f" "x \<in> A'" by auto
  with assms show "p \<in> \<lambda>x \<in> A'. f`x"
    using lambda_pair_mem_if_mem[where ?a=x and ?f="eval f"] by auto
qed (use assms in \<open>auto\<close>)

lemma Dep_Function_lambda_bin_inter_type:
  assumes "f : (x : Element A) \<rightarrow>s B x"
  shows "(\<lambda>x \<in> A \<inter> A'. f`x) : (x : Element (A \<inter> A')) \<rightarrow>cs B x"
proof -
  from assms have "f : (x : Element (A \<inter> A')) \<rightarrow>s B x"
    by (elim Dep_Function_contravariant_dom) (unfold_types, auto)
  then show ?thesis by auto
qed

lemma Dep_Function_Element_lambda_subset_self [simp]:
  assumes "f : (x : Element A) \<rightarrow>s B x"
  shows "(\<lambda>x \<in> A. f`x) \<subseteq> f"
proof -
  from assms have "(\<lambda>x \<in> A. f`x) = f\<restriction>\<^bsub>A\<^esub>"
    by (elim Dep_Function_restrict_eq_lambdaI[symmetric]) discharge_types
  then show ?thesis by simp
qed


end
