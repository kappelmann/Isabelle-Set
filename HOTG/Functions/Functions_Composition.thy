subsection \<open>Composition\<close>
theory Functions_Composition
  imports Functions_Lambda
begin

lemma comp_mem_dep_functionsI:
  assumes f_mem: "f \<in> (x \<in> B) \<rightarrow> (C x)"
  and g_mem: "g \<in> A \<rightarrow> B"
  shows "f \<circ> g \<in> (x \<in> A) \<rightarrow> (C (g`x))"
proof
  show "f \<circ> g \<subseteq> \<Sum>x \<in> A. (C (g`x))"
  proof
    fix p assume "p \<in> f \<circ> g"
    then obtain x y z where "\<langle>x, y\<rangle> \<in> g" "\<langle>y, z\<rangle> \<in> f" "p = \<langle>x, z\<rangle>" by auto
    moreover with assms have "x \<in> A" "z \<in> C (g`x)" by auto
    ultimately show "p \<in> \<Sum>x \<in> A. (C (g`x))" by auto
  qed
next
  show "right_unique A (f \<circ> g)"
    using assms by (auto intro!: right_unique_compI elim: mem_dep_functionsE)
  from g_mem have "rng g \<subseteq> B" by auto
  then show "left_total A (f \<circ> g)"
    using assms
    by (auto elim!: mem_dep_functionsE left_total_compI
      left_total_contravariant_pred)
qed

lemma comp_eval_eq_if_mem_dep_functions [simp]:
  assumes f_mem: "f \<in> (x \<in> B) \<rightarrow> (C x)"
  and g_mem: "g \<in> A \<rightarrow> B"
  and x_mem: "x \<in> A"
  shows "(f \<circ> g)`x = f`(g`x)"
proof -
  have "f \<circ> g \<in> (x \<in> A) \<rightarrow> (C (g`x))"
    using f_mem g_mem comp_mem_dep_functionsI by auto
  with x_mem have "\<langle>x, (f \<circ> g)`x\<rangle> \<in> f \<circ> g"
    using pair_eval_mem_if_mem_if_mem_dep_functions by auto
   then show "(f \<circ> g)`x = f`(g`x)" using g_mem f_mem by auto
qed

lemma comp_id_eq [simp]:
  assumes "f \<in> (x \<in> A) \<rightarrow> (B x)"
  shows "f \<circ> (\<lambda>x \<in> A. x) = f"
proof -
  from assms have "f \<circ> (\<lambda>x \<in> A. x) \<in> (x \<in> A) \<rightarrow> (B((\<lambda>x \<in> A. x)`x))"
    by (elim comp_mem_dep_functionsI) auto
  then have "f \<circ> (\<lambda>x \<in> A. x) \<in> (x \<in> A) \<rightarrow> (B x)"
    by (rule mem_dep_functions_covariant_codom) auto
  from this assms show ?thesis
    by (rule dep_functions_ext, subst comp_eval_eq_if_mem_dep_functions) auto
qed

lemma id_comp_eq [simp]:
  assumes "f \<in> A \<rightarrow> B"
  shows "(\<lambda>x \<in> B. x) \<circ> f = f"
proof -
  have "(\<lambda>x \<in> B. x) \<circ> f \<in> A \<rightarrow> B"
    by (rule comp_mem_dep_functionsI[OF _ assms]) auto
  from this assms show ?thesis
    by (rule dep_functions_ext, subst comp_eval_eq_if_mem_dep_functions) auto
qed


end