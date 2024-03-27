\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Restriction\<close>
theory TSFunctions_Extend_Restrict
  imports TSFunctions_Base
begin

context
  includes fun_restrict_syntax no_rel_restrict_syntax
begin

lemma restrict_Dep_Function_type [type]:
  includes fun_restrict_syntax no_rel_restrict_syntax
  shows "fun_restrict : ((x : A) \<rightarrow>s B x) \<Rightarrow> (P : Set \<Rightarrow> Bool) \<Rightarrow> ((x : (A & type P)) \<rightarrow>s B x)"
proof (intro Dep_fun_typeI Dep_FunctionI)
  fix f P assume f_type: "f : (x : A) \<rightarrow>s B x"
  let ?A' = "A & type P"
  have [simp]: "type_pred (A & type P) = type_pred A \<sqinter> P"
    by (intro ext) (auto simp: meaning_of_type dest: Int_typeD1 Int_typeD2)
  with f_type show "left_total_on ?A' f\<restriction>\<^bsub>P\<^esub>"
    by (urule left_total_on_inf_restrict_leftI where chained = insert) auto
  have "right_unique_on (type_pred A) f \<le> right_unique_on (type_pred ?A') f\<restriction>\<^bsub>P\<^esub>"
    supply Int_typeD1[derive]
    by (urule antimono_right_unique_on[THEN dep_mono_wrt_relD, THEN Dep_Fun_Rel_relD]) auto
  with f_type show "right_unique_on ?A' f\<restriction>\<^bsub>P\<^esub>" by auto
  fix x assume "x : A & type P"
  then have "x : A" and "P x" by unfold_types
  then have "f\<restriction>\<^bsub>P\<^esub>`x = f`x" by simp
  with f_type show "f\<restriction>\<^bsub>P\<^esub>`x : B x" by auto
qed

(*TODO: should be proven with lemma above*)
lemma restrict_Dep_Function_set_type [type]:
  "fun_restrict : ((x : A) \<rightarrow>s B x) \<Rightarrow> (A' : Set) \<Rightarrow> Dep_Function (A & Element A') B"
  sorry

lemma restrict_Dep_Function_type_type [type]:
  "fun_restrict : ((x : A) \<rightarrow>s B x) \<Rightarrow> (T : Any) \<Rightarrow> Dep_Function (A & T) B"
  sorry

lemma restrict_CDep_Function_if_Dep_Function [derive]:
  assumes "f : (x : A) \<rightarrow>s B x"
  shows "f\<restriction>\<^bsub>A\<^esub> : (x : A) \<rightarrow>cs B x"
proof (rule CDep_FunctionI)
  have "f\<restriction>\<^bsub>A\<^esub> : (x : A & A) \<rightarrow>s B x" by discharge_types
  then show "f\<restriction>\<^bsub>A\<^esub> : (x : A) \<rightarrow>s B x"
    by (elim Dep_Function_contravariant_dom) discharge_types
  show "f\<restriction>\<^bsub>A\<^esub> : Dep_Bin_Rel A B"
  proof (rule Dep_Bin_RelI)
    fix p assume "p \<in> f\<restriction>\<^bsub>A\<^esub>"
    then obtain x y where obs: "p = \<langle>x, y\<rangle>" "\<langle>x, y\<rangle> \<in> f" "x : A" by auto
    then have "y = f`x" by simp
    then have "y : B x"  by simp
    with obs show "p : \<Sum>x : A. (B x)" by simp
  qed
qed

end


end