\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Composition\<close>
theory SFunctions_Composition
  imports SFunctions_Lambda
begin

lemma comp_mem_dep_functionsI:
  assumes f_mem: "f \<in> (x \<in> B) \<rightarrow>s (C x)"
  and g_mem: "g \<in> A \<rightarrow>s B"
  shows "f \<circ> g \<in> (x \<in> A) \<rightarrow>s (C (g`x))"
proof
  show "f \<circ> g \<subseteq> \<Sum>x \<in> A. (C (g`x))"
  proof
    fix p assume "p \<in> f \<circ> g"
    then obtain x y z where "\<langle>x, y\<rangle> \<in> g" "\<langle>y, z\<rangle> \<in> f" "p = \<langle>x, z\<rangle>" by auto
    moreover with assms have "x \<in> A" "z \<in> C (g`x)" by auto
    ultimately show "p \<in> \<Sum>x \<in> A. (C (g`x))" by auto
  qed
next
  show "set_right_unique_on A (f \<circ> g)"
  proof (subst set_right_unique_on_set_iff_set_right_unique_on,
    intro set_right_unique_on_compI)
    let ?C = "rng g\<restriction>\<^bsub>\<lambda>x. x \<in> A\<^esub> \<inter> dom f"
    from f_mem have "mem_of ?C \<le> mem_of B" by auto
    moreover have "set_right_unique_on (mem_of B) f" using f_mem by blast
    ultimately have "set_right_unique_on (mem_of ?C) f"
      using antimonoD[OF antimono_set_right_unique_on_pred] by auto
    then show "set_right_unique_on ?C f" by simp
  qed (insert g_mem, auto)
  from g_mem have "rng g \<subseteq> B" by auto
  then show "set_left_total_on A (f \<circ> g)"
    using assms by (subst set_left_total_on_set_iff_set_left_total_on,
      intro set_left_total_on_compI)
    auto
qed

lemma comp_eval_eq_if_mem_dep_functions [simp]:
  assumes f_mem: "f \<in> (x \<in> B) \<rightarrow>s (C x)"
  and g_mem: "g \<in> A \<rightarrow>s B"
  and x_mem: "x \<in> A"
  shows "(f \<circ> g)`x = f`(g`x)"
proof -
  have "f \<circ> g \<in> (x \<in> A) \<rightarrow>s (C (g`x))"
    using f_mem g_mem comp_mem_dep_functionsI by auto
  with x_mem have "\<langle>x, (f \<circ> g)`x\<rangle> \<in> f \<circ> g"
    using pair_eval_mem_if_mem_if_mem_dep_functions by auto
   then show "(f \<circ> g)`x = f`(g`x)" using g_mem f_mem by auto
qed

definition "set_id A \<equiv> \<lambda>x \<in> A. x"

lemma set_id_eq [simp]: "set_id A = \<lambda>x \<in> A. x"
  unfolding set_id_def by simp

lemma set_id_mem_dep_functions [iff]: "set_id A \<in> (x \<in> A) \<rightarrow>s {x}"
  by auto

lemma comp_set_id_eq [simp]:
  assumes "f \<in> (x \<in> A) \<rightarrow>s (B x)"
  shows "f \<circ> set_id A = f"
proof -
  from assms have "f \<circ> set_id A \<in> (x \<in> A) \<rightarrow>s (B((set_id A)`x))"
    by (elim comp_mem_dep_functionsI) auto
  then have "f \<circ> set_id A \<in> (x \<in> A) \<rightarrow>s (B x)"
    by (rule mem_dep_functions_covariant_codom) auto
  from this assms show ?thesis
    by (rule dep_functions_ext, subst comp_eval_eq_if_mem_dep_functions) auto
qed

lemma set_id_comp_eq [simp]:
  assumes "f \<in> A \<rightarrow>s B"
  shows "set_id B \<circ> f = f"
proof -
  have "set_id B \<circ> f \<in> A \<rightarrow>s B"
    by (rule comp_mem_dep_functionsI[OF _ assms]) auto
  from this assms show ?thesis
    by (rule dep_functions_ext, subst comp_eval_eq_if_mem_dep_functions)
    (auto intro: eval_lambda_eq)
qed


end