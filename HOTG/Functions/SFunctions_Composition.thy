\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Composition\<close>
theory SFunctions_Composition
  imports SFunctions_Lambda
begin

definition "set_comp f g \<equiv> set_rel_comp g f"

bundle hotg_comp_syntax begin notation set_comp (infixl "\<circ>" 55) end
bundle no_hotg_comp_syntax begin no_notation set_comp (infixl "\<circ>" 55) end
unbundle
  no_comp_syntax
  no_rel_comp_syntax
  hotg_comp_syntax

lemma set_comp_eq_rel_comp [simp]: "f \<circ> g = g \<circ>\<circ> f"
  unfolding set_comp_def by simp

lemma comp_subset_dep_pairsI:
  assumes "g \<in> A \<rightarrow>s B"
  and "f \<subseteq> \<Sum>x \<in> B. (C x)"
  shows "f \<circ> g \<subseteq> \<Sum>x \<in> A. (C (g`x))"
proof (rule subsetI)
  fix p assume "p \<in> f \<circ> g"
  then obtain x y z where "\<langle>x, y\<rangle> \<in> g" "\<langle>y, z\<rangle> \<in> f" "p = \<langle>x, z\<rangle>" by auto
  with assms show "p \<in> \<Sum>x \<in> A. (C (g`x))" by auto
qed

lemma comp_mem_dep_functionsI:
  assumes g_mem: "g \<in> A \<rightarrow>s B"
  and f_mem: "f \<in> (x \<in> B) \<rightarrow>s (C x)"
  shows "f \<circ> g \<in> (x \<in> A) \<rightarrow>s (C (g`x))"
proof
  show "f \<circ> g \<subseteq> \<Sum>x \<in> A. (C (g`x))"
    using assms comp_subset_dep_pairsI by (elim mem_dep_functionsE) blast
next
  show "right_unique_on A (f \<circ> g)"
  proof (urule set_right_unique_on_compI)
    let ?C = "codom g\<restriction>\<^bsub>mem_of A\<^esub> \<inter> dom f"
    from f_mem have "mem_of ?C \<le> mem_of B" by auto
    moreover from f_mem have "right_unique_on (mem_of B) f" by blast
    ultimately have "right_unique_on (mem_of ?C) f"
      using antimono_right_unique_on by (auto dest: dep_mono_wrt_relD)
    then show "right_unique_on ?C f" by simp
  qed (use g_mem in auto)
  from g_mem have "codom g \<subseteq> B" by auto
  then show "left_total_on A (f \<circ> g)"
    using assms by (urule set_left_total_on_compI where chained = insert) (auto 6 0)
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
    by (intro comp_mem_dep_functionsI) auto
  then have "f \<circ> set_id A \<in> (x \<in> A) \<rightarrow>s (B x)"
    by (rule mem_dep_functions_covariant_codom) auto
  from this assms show ?thesis
    by (rule dep_functions_ext, subst comp_eval_eq_if_mem_dep_functions) auto
qed

lemma set_id_comp_eq [simp]:
  assumes "f \<in> A \<rightarrow>s B"
  shows "set_id B \<circ> f = f"
proof -
  from assms have "set_id B \<circ> f \<in> A \<rightarrow>s B" by (rule comp_mem_dep_functionsI) auto
  from this assms show ?thesis
    by (rule dep_functions_ext, subst comp_eval_eq_if_mem_dep_functions)
    (auto intro: eval_lambda_eq)
qed


end