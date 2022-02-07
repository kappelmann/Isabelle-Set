theory TFunctions_Extend_Restrict
  imports TFunctions_Base
begin

subsection \<open>Restriction\<close>

lemma restrict_Dep_Function_type [type]:
  "restrict : Dep_Function A B \<Rightarrow> (P : Set \<Rightarrow> Bool) \<Rightarrow> Dep_Function (A & type P) B"
proof (intro Dep_fun_typeI Dep_FunctionI)
  fix f P assume f_type: "f : (x : A) \<rightarrow> B x"
  let ?A' = "A & type P"
  let ?P' = "\<lambda>x. x : A \<and> P x"
  have "left_total ?A' (f\<restriction>P) = left_total ?P' (f\<restriction>P)"
    by (simp add: meaning_of_type typedef)
  with f_type show "left_total ?A' (f\<restriction>P)"
    by (auto intro: left_total_and_restrictI)
  from f_type have "right_unique A f" by (elim Dep_Function_right_unique)
  with right_unique_contravariant_set have "right_unique A (f\<restriction>P)" by auto
  with right_unique_contravariant_pred show "right_unique ?A' (f\<restriction>P)"
    by (auto simp: meaning_of_type typedef)
  fix x assume "x : A & type P"
  then have "x : A" and "P x" by unfold_types
  then have "(f\<restriction>P)`x = f`x" by simp
  with f_type show "(f\<restriction>P)`x : B x" by auto
qed

lemma restrict_Dep_Function_set_type [type]:
  "restrict : Dep_Function A B \<Rightarrow> (A' : Set) \<Rightarrow> Dep_Function (A & Element A') B"
  (*TODO: should be proved with lemma above*)
  by unfold_types force

lemma restrict_Dep_Function_type_type [type]:
  "restrict : Dep_Function A B \<Rightarrow> (T : Any) \<Rightarrow> Dep_Function (A & T) B"
  (*TODO: should be proved with lemma above*)
  by unfold_types force

lemma restrict_CDep_Function_if_Dep_Function [derive]:
  assumes "f : (x : A) \<rightarrow> B x"
  shows "f\<restriction>A : (x : A) \<rightarrow>c B x"
proof (rule CDep_FunctionI)
  have "f\<restriction>A : (x : A & A) \<rightarrow> B x" by discharge_types
  then show "f\<restriction>A : (x : A) \<rightarrow> B x"
    by (elim Dep_Function_contravariant_dom) discharge_types
  show "f\<restriction>A : Dep_Bin_Rel A B"
  proof (rule Dep_Bin_RelI)
    fix p assume "p \<in> f\<restriction>A"
    then obtain x y where "p = \<langle>x, y\<rangle>" "\<langle>x, y\<rangle> \<in> f" "x : A" by auto
    moreover with assms have "y : B x" by auto
    ultimately show "p : \<Sum>x : A. (B x)" by simp
  qed
qed


end