\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Composition\<close>
theory TSFunctions_Composition
  imports
    TSFunctions_Lambda
    TSBinary_Relation_Functions
begin

context
  includes no_rel_comp_syntax
begin

lemma Dep_Function_comp_set_right_unique_on:
  assumes f_type: "f : (x : B) \<rightarrow>s (C x)"
  and g_type: "g : A \<rightarrow>s B"
  shows "right_unique_on A (g \<circ>\<circ> f)"
proof -
  have "right_unique_on (codom g\<restriction>\<^bsub>A\<^esub> \<inter> dom f) f"
  proof -
    from f_type have "right_unique_on (type_pred B) f" by auto
    have "right_unique_on (type_pred B) f \<le> right_unique_on (mem_of (codom g\<restriction>\<^bsub>A\<^esub> \<inter> dom f)) f"
      sorry
      (* by (urule antimono_right_unique_on[THEN dep_mono_wrt_relD, THEN Dep_Fun_Rel_relD])
      (auto intro!: le_predI elim!: mem_rel_restrict_leftE
      simp: eval_eq_if_pair_mem_if_Dep_Function[OF g_type]) *)
      (* (insert g_type, auto intro!: le_predI elim!: mem_set_restrict_leftE) *)
    with f_type show ?thesis by auto
  qed
  with assms show ?thesis by (urule set_right_unique_on_compI where chained = insert) auto
qed

lemma Dep_Function_comp_eval_eq [simp]:
  assumes f_type: "f : (x : B) \<rightarrow>s (C x)"
  and g_type: "g : A \<rightarrow>s B"
  and x_type: "x : A"
  shows "(g \<circ>\<circ> f)`x = f`(g`x)"
proof (rule eval_eqI)
  show "x : A" by (fact x_type)
  from assms show "\<langle>x, f`(g`x)\<rangle> \<in> g \<circ>\<circ> f" sorry
qed (insert Dep_Function_comp_set_right_unique_on[OF f_type g_type], auto simp: type_pred_eq)

lemma set_rel_comp_type_Dep_Function [type]:
  "(\<circ>\<circ>) : (g : A \<rightarrow>s B) \<Rightarrow> ((x : B) \<rightarrow>s C x) \<Rightarrow> (x : A) \<rightarrow>s C (g`x)"
proof (intro Dep_fun_typeI Dep_FunctionI)
  fix f g assume "f : (x : B) \<rightarrow>s C x" "g : A \<rightarrow>s B"
  then show "right_unique_on A (g \<circ>\<circ> f)" by (rule Dep_Function_comp_set_right_unique_on)
  show "left_total_on A (g \<circ>\<circ> f)" sorry
qed auto

lemma comp_type_CDep_Function [type]:
  "(\<circ>\<circ>) : (g : A \<rightarrow>cs B) \<Rightarrow> ((x : B) \<rightarrow>s C x) \<Rightarrow> (x : A) \<rightarrow>cs C (g`x)"
proof (intro Dep_fun_typeI CDep_FunctionI Dep_Bin_RelI)
  fix f g p assume f_g_types: "f : (x : B) \<rightarrow>s C x" "g : A \<rightarrow>cs B" and "p \<in> g \<circ>\<circ> f"
  then obtain x y z where "\<langle>x, y\<rangle> \<in> g" "\<langle>y, z\<rangle> \<in> f" "p = \<langle>x, z\<rangle>" by auto
  moreover with f_g_types have "x : A" "y : B" "g`x = y" by auto
  moreover with \<open>\<langle>y, z\<rangle> \<in> f\<close> f_g_types have "z : C y" sorry
  ultimately show "p : \<Sum>x : A. (C (g`x))" by simp
qed auto

lemma Function_lambda_comp_lambda_eq [simp]:
  assumes "f : Element A \<Rightarrow> Element B"
  shows "(\<lambda>x \<in> A. f x) \<circ>\<circ> (\<lambda>y \<in> B. g y) = \<lambda>x \<in> A. g (f x)"
  sorry
  (* using assms by (intro eqI mem_rel_compI) auto *)

end

end
