theory FPS
  imports
    Lifting_Set
    Isabelle_Set.SNat
    Isabelle_Set.SRings
    Lifting_Group
begin

lemma elem_function: "f \<in> ((A ::set) \<rightarrow> B) \<equiv> f : (Element A) \<rightarrow>c (Element B)"
  using mem_dep_functions_iff_CDep_Function by auto

unbundle no_isa_set_zero_implicit_syntax

lemma Ring_zero_type: "\<And>R A. R : Ring (Element A) \<Longrightarrow> zero R : Element A"
  by (simp add: Group_Monoid Monoid_Zero Zero_zero_type zero_def)

locale formal_power_series =
  fixes A R :: set
    and Eq :: "set \<Rightarrow> set \<Rightarrow> bool"
  assumes Ring_R [type]: "R : Ring (Element A)"
      and per_Eq: "partial_equivalence Eq"
      and elem_A_iff_Eq: "x \<in> A = Eq x x"
begin

definition "fps_rep = functions \<nat> A"
abbreviation "FPS_rep \<equiv> Element fps_rep"

unbundle no_hotg_comp_syntax

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

definition fps_map :: "(set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set"
  where "fps_map f s \<equiv> (\<lambda>n\<in>\<nat>. f (s`n))"

definition fps_rel :: "(set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  where "fps_rel S s1 s2 \<equiv> s1 \<in> fps_rep \<and> s2 \<in> fps_rep \<and> (\<forall>n\<in>\<nat>. S (s1`n) (s2`n))"

lemma fps_rel_in_fps_rep:
  assumes "fps_rel S x y"
  shows "x \<in> fps_rep" "y \<in> fps_rep"
  using assms[unfolded fps_rel_def]
  by blast+

lemma fps_rel_peserves_per: "partial_equivalence S \<Longrightarrow> partial_equivalence (fps_rel S)"
  unfolding partial_equivalence_unfold fps_rel_def
   by blast


abbreviation "FPS_Rel_p S \<equiv> rel_comp' FPS_Rel (fps_rel S)"

lemma lifting_start: "lifting Eq_rep Eq_abs T abs rep \<Longrightarrow> Eq_rep x x \<Longrightarrow> const True (T x (abs x)) \<Longrightarrow> T x (abs x)"
  using lifting_Eq_rep(1)
  by metis

lemma FPS_Rel_zero: "\<exists>T t. T fps_rep_zero t"
  apply (rule exI, rule exI)
  apply (rule lifting_start[where x=fps_rep_zero])
    apply (rule FPS_lifting)
  sorry

end

definition Ring_hom :: "set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  where "Ring_hom A_rep A_abs R_rep R_abs = undefined"

locale formal_power_series_trans =
  fps_rep: formal_power_series A_rep R_rep Eq_rep +
  fps_abs: formal_power_series A_abs R_abs Eq_abs
  for A_rep R_rep Eq_rep A_abs R_abs Eq_abs +
  fixes T :: "set \<Rightarrow> set \<Rightarrow> bool"
    and abs rep :: "set \<Rightarrow> set"
  assumes lifting: "lifting Eq_rep Eq_abs T abs rep"
      and Ring_hom: "Ring_hom A_rep A_abs R_rep R_abs"
begin

definition fps_rel :: "set \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> set \<Rightarrow> bool"
  where "fps_rel A B R s1 s2 \<equiv>
    s1 \<in> A \<and> s2 \<in> B \<and> (\<forall>n\<in>\<nat>. R (s1`n) (s2`n))"

lemma fps_rel_preseves_per: "partial_equivalence S \<Longrightarrow> partial_equivalence (fps_rel A A S)"
  unfolding partial_equivalence_unfold fps_rel_def
  by blast

definition Eq_fps_rep_rep :: "set \<Rightarrow> set \<Rightarrow> bool"
  where "Eq_fps_rep_rep \<equiv> fps_rel fps_rep.fps_rep fps_rep.fps_rep Eq_rep"

definition Eq_fps_rep_abs :: "set \<Rightarrow> set \<Rightarrow> bool"
  where "Eq_fps_rep_abs \<equiv> fps_rel fps_abs.fps_rep fps_abs.fps_rep Eq_abs"

definition T_fps_rep :: "set \<Rightarrow> set \<Rightarrow> bool"
  where "T_fps_rep \<equiv> fps_rel fps_rep.fps_rep fps_abs.fps_rep T"

definition fps_map :: "(set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set"
  where "fps_map f s \<equiv> (\<lambda>n\<in>\<nat>. f (s`n))"

definition fps_rep_abs :: "set \<Rightarrow> set"
  where "fps_rep_abs \<equiv> fps_map abs"

definition fps_rep_rep :: "set \<Rightarrow> set"
  where "fps_rep_rep \<equiv> fps_map rep"

lemma Eq_fps_rep_fps_rel_comm:
  "rel_comp' (eq fps_abs.fps_rep) Eq_fps_rep_abs = rel_comp' Eq_fps_rep_abs (eq fps_abs.fps_rep)"
proof ((rule ext)+, (rewrite rel_comp'_def)+, (rewrite eq_def)+, rule iffI)
  fix x y
  assume "\<exists>z. Eq_fps_rep_abs x z \<and> z \<in> fps_abs.fps_rep \<and> z = y"
  hence 1: "Eq_fps_rep_abs x y"
    by blast
  moreover have "x \<in> fps_abs.fps_rep"
    using 1[unfolded Eq_fps_rep_abs_def fps_rel_def]
    by blast
  ultimately show "\<exists>z. (x \<in> fps_abs.fps_rep \<and> x = z) \<and> Eq_fps_rep_abs z y"
    by blast
next
  fix x y
  assume "\<exists>z. (x \<in> fps_abs.fps_rep \<and> x = z) \<and> Eq_fps_rep_abs z y"
  hence 1: "Eq_fps_rep_abs x y"
    by blast
  moreover have "y \<in> fps_abs.fps_rep"
    using 1[unfolded Eq_fps_rep_abs_def fps_rel_def]
    by blast
  ultimately show "\<exists>z. Eq_fps_rep_abs x z \<and> z \<in> fps_abs.fps_rep \<and> z = y"
    by blast
qed

lemma inner_lifting: "lifting Eq_fps_rep_rep Eq_fps_rep_abs T_fps_rep fps_rep_abs fps_rep_rep"
proof (rule liftingI)
  fix x y
  assume prem: "Eq_fps_rep_rep x y"
  thus "Eq_fps_rep_rep y x"
    unfolding Eq_fps_rep_rep_def
    using fps_rel_preseves_per fps_rep.per_Eq per_sym
    by metis
next
  fix x y z
  assume prems:
    "Eq_fps_rep_rep x y"
    "Eq_fps_rep_rep y z"
  have "\<And>x y z. Eq_rep x y \<Longrightarrow> Eq_rep y z \<Longrightarrow> Eq_rep x z"
    using lifting[unfolded lifting_unfold]
    by metis
  hence "\<forall>n\<in>\<nat>. Eq_rep (x`n) (z`n)"
    using prems[unfolded Eq_fps_rep_rep_def fps_rel_def]
    by blast
  moreover have "x \<in> fps_rep.fps_rep"
    using prems(1)[unfolded Eq_fps_rep_rep_def fps_rel_def]
    by blast
  moreover have "z \<in> fps_rep.fps_rep"
    using prems(2)[unfolded Eq_fps_rep_rep_def fps_rel_def]
    by blast
  ultimately show "Eq_fps_rep_rep x z"
    unfolding Eq_fps_rep_rep_def fps_rel_def
    by blast
next
  fix x y
  assume prem: "Eq_fps_rep_abs x y"
  thus "Eq_fps_rep_abs y x"
    unfolding Eq_fps_rep_abs_def
    using fps_rel_preseves_per fps_abs.per_Eq per_sym
    by metis
next
  fix x y z
  assume prems:
    "Eq_fps_rep_abs x y"
    "Eq_fps_rep_abs y z"
  have "\<And>x y z. Eq_abs x y \<Longrightarrow> Eq_abs y z \<Longrightarrow> Eq_abs x z"
    using lifting[unfolded lifting_unfold]
    by metis
  hence "\<forall>n\<in>\<nat>. Eq_abs (x`n) (z`n)"
    using prems[unfolded Eq_fps_rep_abs_def fps_rel_def]
    by blast
  moreover have "x \<in> fps_abs.fps_rep"
    using prems(1)[unfolded Eq_fps_rep_abs_def fps_rel_def]
    by blast
  moreover have "z \<in> fps_abs.fps_rep"
    using prems(2)[unfolded Eq_fps_rep_abs_def fps_rel_def]
    by blast
  ultimately show "Eq_fps_rep_abs x z"
    unfolding Eq_fps_rep_abs_def fps_rel_def
    by blast
next
  fix x y z
  assume prems:
    "T_fps_rep x z"
    "T_fps_rep y z"
  have "\<And>x y z. T x z \<Longrightarrow> T y z \<Longrightarrow> Eq_rep x y"
    using lifting[unfolded lifting_unfold]
    by metis
  with prems show "Eq_fps_rep_rep x y"
    unfolding Eq_fps_rep_rep_def T_fps_rep_def fps_rel_def
    by blast
next
  fix x y z
  assume prems:
    "T_fps_rep x y"
    "T_fps_rep x z"
  have "\<And>x y z. T x y \<Longrightarrow> T x z \<Longrightarrow> Eq_abs y z"
    using lifting[unfolded lifting_unfold]
    by metis
  with prems show "Eq_fps_rep_abs y z"
    unfolding Eq_fps_rep_abs_def T_fps_rep_def fps_rel_def
    by blast
next
  fix x y z
  assume prems:
    "Eq_fps_rep_rep x y"
    "T_fps_rep x z"
  have "\<And>x y z. Eq_rep x y \<Longrightarrow> T x z \<Longrightarrow> T y z"
    using lifting[unfolded lifting_unfold]
    by metis
  with prems show "T_fps_rep y z"
    unfolding Eq_fps_rep_rep_def T_fps_rep_def fps_rel_def
    by blast
next
  fix x y z
  assume prems:
    "Eq_fps_rep_abs y z"
    "T_fps_rep x y"
  have "\<And>x y z. Eq_abs y z \<Longrightarrow> T x y \<Longrightarrow> T x z"
    using lifting[unfolded lifting_unfold]
    by metis
  with prems show "T_fps_rep x z"
    unfolding Eq_fps_rep_abs_def T_fps_rep_def fps_rel_def
    by blast
next
  fix x
  assume prem: "Eq_fps_rep_rep x x"
  have 1: "x \<in> fps_rep.fps_rep"
    using prem
    unfolding Eq_fps_rep_rep_def fps_rel_def
    by blast
  from 1 have "\<And>n. n \<in> \<nat> \<Longrightarrow> abs (x`n) \<in> A_abs"
    using lifting[unfolded lifting_unfold] fps_abs.elem_A_iff_Eq fps_rep.elem_A_iff_Eq fps_rep.fps_app_elem
    by metis
  hence 2: "fps_map abs x \<in> fps_abs.fps_rep"
    unfolding fps_map_def fps_abs.fps_rep_def
    by blast
  have "\<And>x. Eq_rep x x \<Longrightarrow> T x (abs x)"
    using lifting[unfolded lifting_unfold]
    by metis
  with 1 have "\<And>n. n \<in> \<nat> \<Longrightarrow> T (x`n) (fps_map abs x`n)"
    using fps_rep.elem_A_iff_Eq eval_lambda_eq fps_rep.fps_app_elem
    unfolding fps_map_def
    by metis
  with 1 2 show "T_fps_rep x (fps_rep_abs x)"
    unfolding T_fps_rep_def fps_rep_abs_def fps_rel_def
    by blast
next
  fix y
  assume prem: "Eq_fps_rep_abs y y"
  have 1: "y \<in> fps_abs.fps_rep"
    using prem
    unfolding Eq_fps_rep_abs_def fps_rel_def
    by blast
  from 1 have "\<And>n. n \<in> \<nat> \<Longrightarrow> rep (y`n) \<in> A_rep"
    using lifting[unfolded lifting_unfold] fps_abs.elem_A_iff_Eq fps_rep.elem_A_iff_Eq fps_abs.fps_app_elem
    by metis
  hence 2: "fps_map rep y \<in> fps_rep.fps_rep"
    unfolding fps_map_def fps_rep.fps_rep_def
    by blast
  have "\<And>y. Eq_abs y y \<Longrightarrow> T (rep y) y"
    using lifting[unfolded lifting_unfold]
    by metis
  with 1 have "\<And>n. n \<in> \<nat> \<Longrightarrow> T (fps_map rep y`n) (y`n)"
    using fps_abs.elem_A_iff_Eq eval_lambda_eq fps_abs.fps_app_elem
    unfolding fps_map_def
    by metis
  with 1 2 show "T_fps_rep (fps_rep_rep y) y"
    unfolding T_fps_rep_def fps_rep_rep_def fps_rel_def
    by blast
qed

lemmas FPS_lifting_p = comp_lifting'[OF inner_lifting fps_abs.FPS_lifting Eq_fps_rep_fps_rel_comm[symmetric]]

end

term "f, g : a \<rightarrow> b" "f \<noteq> g"
term "c < a"
term "f : c \<rightarrow> b" "f = g"

term "f : Z \<rightarrow> Z"
term "f : N \<rightarrow> Q"
term "f : N\<times>N \<rightarrow> Z/5"

term "formal_power_series.fps_rep_zero"

end