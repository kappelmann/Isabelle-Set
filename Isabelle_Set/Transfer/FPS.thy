theory FPS
  imports
    Lifting_Set
    Isabelle_Set.SNat
    Isabelle_Set.SRings
begin

lemma elem_function: "f \<in> ((A ::set) \<rightarrow> B) \<equiv> f : (Element A) \<rightarrow>c (Element B)"
  using mem_dep_functions_iff_CDep_Function by auto

unbundle no_isa_set_zero_implicit_syntax

lemma Ring_zero_type: "\<And>R A. R : Ring (Element A) \<Longrightarrow> zero R : Element A"
  by (simp add: Group_Monoid Monoid_Zero Zero_zero_type zero_def)

locale formal_power_series =
  fixes A R :: set
  assumes Ring_R [type]: "R : Ring (Element A)"
begin

definition "fps_rep = functions \<nat> A"
abbreviation "FPS_rep \<equiv> Element fps_rep"

unbundle no_hotg_comp_syntax

definition fps_map :: "(set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set"
  where "fps_map f s \<equiv> (\<lambda>n\<in>\<nat>. f (s`n))"

definition fps_rel :: "(set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  where "fps_rel S s1 s2 \<equiv> (\<forall>n\<in>\<nat>. S (s1`n) (s2`n))"

definition "fps_rep_zero = (\<lambda>n\<in>\<nat>. zero R)"

lemma fps_rep_zero_type: "fps_rep_zero : FPS_rep"
  unfolding fps_rep_zero_def fps_rep_def
  apply (rule ElementI)
  apply (subst elem_function)
  apply (rule lambda_app_type)
  apply (rule Dep_fun_typeI)
  apply (rule Ring_zero_type[OF Ring_R])
  done

lemma fps_app_elem: "s \<in> fps_rep \<Longrightarrow> n \<in> \<nat> \<Longrightarrow> s`n \<in> A"
  unfolding fps_rep_def elem_function
  by discharge_types

definition "fps_rep_add = (\<lambda>s1\<in>fps_rep. \<lambda>s2\<in>fps_rep. \<lambda>n\<in>\<nat>. add R (s1`n) (s2`n))"

lemma FunctionI: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> (\<lambda>x\<in>A. f x) : Element A \<rightarrow> Element B"
  by (subst Dep_Function_if_CDep_Function) (auto iff: mem_iff_Element)

lemma fps_rep_add_type: "fps_rep_add : FPS_rep \<rightarrow>c FPS_rep \<rightarrow>c FPS_rep"
  unfolding fps_rep_add_def fps_rep_def
  apply (auto intro!: lambda_app_type Dep_fun_typeI ElementI
    dest!: ElementD
    iff: mem_dep_functions_iff_CDep_Function)
  apply (drule Dep_Function_if_CDep_Function)+
  using [[type_derivation_depth=5]]
  apply discharge_types
  done

definition fps_inj :: "set \<Rightarrow> set"
  where "fps_inj x = (\<lambda>n\<in>\<nat>. if n = 0 then x else zero R)"

lemma [type]: "fps_inj: Element A \<Rightarrow> Element fps_rep"
  unfolding fps_rep_def fps_inj_def
  apply unfold_types
  sorry
interpretation FPS: set_extension A fps_rep fps_inj
proof
  show "fps_inj : Element A \<Rightarrow> Element fps_rep"
    by simp
  show "\<forall>x \<in> A. \<forall>y \<in> A. fps_inj x = fps_inj y \<longrightarrow> x = y"
  proof ((rule Bounded_Quantifiers.ballI)+, rule impI)
    fix x y
    assume assms: "x \<in> A" "y \<in> A" "fps_inj x = fps_inj y"
    show "x = y"
      using app_eq_if_mem_if_lambda_eq[OF assms(3)[unfolded fps_inj_def] zero_mem_nat]
      by simp
  qed
qed

abbreviation "fps \<equiv> FPS.abs_image"
abbreviation "FPS \<equiv> Element fps"

lemmas subset_fps = FPS.subset_abs_image

lemma subtype_FPS: "x : Element A \<Longrightarrow> x : FPS"
  apply unfold_types
  apply (rule mem_if_mem_if_subset)
  apply (simp add: subset_fps)+
  done

abbreviation "FPS_Rel \<equiv> Ext_Rel fps FPS.Rep" (* not parametrized *)

lemmas FPS_lifting = set_extension_lifting(1)[OF FPS.set_extension_axioms]

abbreviation "eq_FPS_abs \<equiv> eq FPS.abs_image"
abbreviation "eq_FPS_rep \<equiv> eq fps_rep"

lemma lifting_start: "lifting Eq_rep Eq_abs T abs rep \<Longrightarrow> Eq_rep x x \<Longrightarrow> const True (T x (abs x)) \<Longrightarrow> T x (abs x)"
  using lifting_Eq_rep(1)
  by metis

lemma FPS_Rel_zero: "\<exists>T t. T fps_rep_zero t"
  apply (rule exI, rule exI)
  apply (rule lifting_start[where x=fps_rep_zero])
    apply (rule FPS_lifting)
  sorry

end


term "formal_power_series.fps_rep_zero"

end