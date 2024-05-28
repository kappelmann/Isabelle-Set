\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Typed Functions\<close>
theory TFunctions_Base
  imports
    Soft_Types_HOL
    Transport.Functions_Restrict
    Transport.LFunctions
begin

context
  notes type_to_HOL_simp[simp, symmetric, simp del]
  [[ucombine add = \<open>Standard_Unification_Combine.eunif_data (K Higher_Order_Unification.unify)
    (Standard_Unification_Combine.default_metadata \<^binding>\<open>ho_unif\<close>)\<close>]]
begin

lemma id_type [type]: "id \<Ztypecolon> A \<Rightarrow> A"
  by (urule mono_wrt_pred_self_id)

lemma comp_type [type]:
  "(\<circ>) \<Ztypecolon> ((x : B) \<Rightarrow> C x) \<Rightarrow> (f : A \<Rightarrow> B) \<Rightarrow> (x : A) \<Rightarrow> C (f x)"
  by (urule mono_dep_mono_wrt_dep_mono_wrt_comp)

lemma dep_fun_map_type [type]:
  "dep_fun_map \<Ztypecolon> (f : A \<Rightarrow> B) \<Rightarrow> ((x : A) \<Rightarrow> (y : B) \<Rightarrow> (z : C (f x)) \<Rightarrow> D x y z) \<Rightarrow>
    (h : (x : B) \<Rightarrow> C x) \<Rightarrow> (x : A) \<Rightarrow> D x (f x) (h (f x))"
  by (urule mono_wrt_dep_mono_wrt_dep_fun_map)

lemma fun_map_type [type]:
  "fun_map \<Ztypecolon> (f : A \<Rightarrow> B) \<Rightarrow> ((x : C) \<Rightarrow> D x) \<Rightarrow> (h : B \<Rightarrow> C) \<Rightarrow> (x : A) \<Rightarrow> D (h (f x))"
  by (urule mono_wrt_dep_mono_wrt_fun_map)

end

definition "has_inverse_on_type T :: ('a type \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool \<equiv> has_inverse_on (of_type T)"
adhoc_overloading has_inverse_on has_inverse_on_type

lemma has_inverse_on_type_eq_has_inverse_on_pred [simp]:
  "(has_inverse_on_type T :: ('a type \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool) = has_inverse_on (of_type T)"
  unfolding has_inverse_on_type_def by simp

lemma has_inverse_on_type_eq_has_inverse_on_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  shows "has_inverse_on_type T :: ('a type \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool \<equiv> has_inverse_on P"
  using assms by simp

lemma has_inverse_on_type_iff_has_inverse_on_pred_uhint [iff]:
  "has_inverse_on_type T f y \<longleftrightarrow> has_inverse_on (of_type T) f y"
  by simp

lemma mono_wrt_dep_mono_wrt_top_inf_fun_restrict:
  "(((x : A) \<Rightarrow> B x) \<Rightarrow> (A' : (\<top> :: _ \<Rightarrow> bool)) \<Rightarrow> (x : A \<sqinter> A') \<Rightarrow> B x) fun_restrict"
  by fastforce

definition "(fun_restrict_type (f :: 'a \<Rightarrow> 'b) (T :: 'a type) :: 'a \<Rightarrow> 'b) \<equiv>
  fun_restrict f (of_type T)"
adhoc_overloading fun_restrict fun_restrict_type

lemma fun_restrict_type_eq_fun_restrict_pred [simp]:
  "(fun_restrict (f :: 'a \<Rightarrow> 'b) (T :: 'a type) :: 'a \<Rightarrow> 'b) = fun_restrict f (of_type T)"
  unfolding fun_restrict_type_def by auto

lemma fun_restrict_type_eq_fun_restrict_pred_uhint [uhint]:
  assumes "P \<equiv> of_type T"
  and "f \<equiv> g"
  shows "fun_restrict (f :: 'a \<Rightarrow> 'b) (T :: 'a type) :: 'a \<Rightarrow> 'b \<equiv> fun_restrict g P"
  using assms by simp

lemma fun_restrict_type_type [type]:
  "fun_restrict_type \<Ztypecolon> ((x : A) \<Rightarrow> B x) \<Rightarrow> (A' : Any) \<Rightarrow> (x : A & A') \<Rightarrow> B x"
  supply type_to_HOL_simp[simp, symmetric, simp del]
    dep_mono_wrt_type_eq_pred_map_dep_mono_wrt_pred_comp_type_if_iff[simp]
  by (urule mono_wrt_dep_mono_wrt_top_inf_fun_restrict)


end