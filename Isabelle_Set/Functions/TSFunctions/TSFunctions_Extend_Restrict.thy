\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Restriction\<close>
theory TSFunctions_Extend_Restrict
  imports TSFunctions_Base
begin

unbundle no_restrict_syntax

lemma restrict_Dep_Function_type [type]:
  "set_restrict_left : ((x : A) \<rightarrow>s B x) \<Rightarrow> (P : Set \<Rightarrow> Bool) \<Rightarrow>
    ((x : (A & type P)) \<rightarrow>s B x) "
proof (intro Dep_fun_typeI Dep_FunctionI)
  fix f P assume f_type: "f : (x : A) \<rightarrow>s B x"
  let ?A' = "A & type P"
  have "type_pred ?A' = (\<lambda>x. x : A \<and> P x)" by unfold_types
  with f_type show "set_left_total_on ?A' f\<restriction>\<^bsub>P\<^esub>"
    by (auto intro: set_left_total_on_inf_restrict_leftI)
  from f_type have "set_right_unique_on (type_pred A) f"
    by (auto dest: Dep_Function_set_right_unique_on)
  then have "set_right_unique_on (type_pred A) f\<restriction>\<^bsub>P\<^esub>"
    using antimonoD[OF antimono_set_right_unique_on_set]
    by (rule le_boolD'') auto
  then have "set_right_unique_on (type_pred ?A') f\<restriction>\<^bsub>P\<^esub>"
    using antimonoD[OF antimono_set_right_unique_on_pred]
    by (rule le_boolD'') (auto dest: Int_typeD1)
  then show "set_right_unique_on ?A' f\<restriction>\<^bsub>P\<^esub>" by simp
  fix x assume "x : A & type P"
  then have "x : A" and "P x" by unfold_types
  then have "f\<restriction>\<^bsub>P\<^esub>`x = f`x" by simp
  with f_type show "f\<restriction>\<^bsub>P\<^esub>`x : B x" by auto
qed

lemma restrict_Dep_Function_set_type [type]:
  "set_restrict_left : Dep_Function A B \<Rightarrow> (A' : Set) \<Rightarrow>
    Dep_Function (A & Element A') B"
  (*TODO: should be proved with lemma above*)
  by unfold_types force

lemma restrict_Dep_Function_type_type [type]:
  "set_restrict_left : Dep_Function A B \<Rightarrow> (T : Any) \<Rightarrow> Dep_Function (A & T) B"
  (*TODO: should be proved with lemma above*)
  by unfold_types force

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
    then obtain x y where "p = \<langle>x, y\<rangle>" "\<langle>x, y\<rangle> \<in> f" "x : A" by auto
    moreover with assms have "y : B x" by auto
    ultimately show "p : \<Sum>x : A. (B x)" by simp
  qed
qed


end