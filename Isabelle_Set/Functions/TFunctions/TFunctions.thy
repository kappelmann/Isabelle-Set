\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Typed Functions\<close>
theory TFunctions
  imports
    Transport.LFunctions
    HOTG.Axioms
    Soft_Types.Soft_Types_HOL
begin

overloading
  injective_on_set \<equiv> "injective_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> bool"
  injective_on_type \<equiv> "injective_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "injective_on_set A (f :: set \<Rightarrow> 'a) \<equiv> injective_on (mem_of A) f"
  definition "injective_on_type (T :: 'a type) (f :: 'a \<Rightarrow> 'b) \<equiv>
    injective_on (type_pred T) f"
end

lemma injective_on_set_eq_injective_on_pred [simp]:
  "(injective_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> bool) A = injective_on (mem_of A)"
  unfolding injective_on_set_def by simp

lemma injective_on_set_iff_injective_on_pred [iff]:
  "injective_on (A :: set) (f :: set \<Rightarrow> 'a) \<longleftrightarrow> injective_on (mem_of A) f"
  by simp

lemma injective_on_type_eq_injective_on_pred [simp]:
  "(injective_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) T = injective_on (type_pred T)"
  unfolding injective_on_type_def by simp

lemma injective_on_type_iff_injective_on_pred [iff]:
  "injective_on (T :: 'a type) (f :: 'a \<Rightarrow> 'b) \<longleftrightarrow> injective_on (type_pred T) f"
  by simp

overloading
  bijection_on_set \<equiv> "bijection_on :: set \<Rightarrow> set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> bool"
begin
  definition "bijection_on_set A B (f :: set \<Rightarrow> set) (g :: set \<Rightarrow> set) \<equiv>
    bijection_on (mem_of A) (mem_of B) f g"
end
(*
lemma bijection_on_set_eq_bijection_on_pred [simp]:
  "(bijection_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> bool) A = bijection_on (mem_of A)"
  unfolding bijection_on_set_def by simp

lemma bijection_on_set_iff_bijection_on_pred [iff]:
  "bijection_on (A :: set) (f :: set \<Rightarrow> 'a) \<longleftrightarrow> bijection_on (mem_of A) f"
  by simp *)

overloading
  inverse_on_set \<equiv> "inverse_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool"
  inverse_on_type \<equiv> "inverse_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "inverse_on_set A (f :: set \<Rightarrow> 'a) \<equiv> inverse_on (mem_of A) f"
  definition "inverse_on_type (T :: 'a type) (f :: 'a \<Rightarrow> 'b) \<equiv>
    inverse_on (type_pred T) f"
end

lemma inverse_on_set_eq_inverse_on_pred [simp]:
  "(inverse_on :: set \<Rightarrow> (set \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> set) \<Rightarrow> bool) A = inverse_on (mem_of A)"
  unfolding inverse_on_set_def by simp

lemma inverse_on_set_iff_inverse_on_pred [iff]:
  "inverse_on (A :: set) (f :: set \<Rightarrow> 'a) g \<longleftrightarrow> inverse_on (mem_of A) f g"
  by simp

lemma inverse_on_type_eq_inverse_on_pred [simp]:
  "(inverse_on :: 'a type \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool) T = inverse_on (type_pred T)"
  unfolding inverse_on_type_def by simp

lemma inverse_on_type_iff_inverse_on_pred [iff]:
  "inverse_on (T :: 'a type) (f :: 'a \<Rightarrow> 'b) g \<longleftrightarrow> inverse_on (type_pred T) f g"
  by simp


subsection \<open>Types and Monotonicity\<close>

lemma dep_mono_wrt_pred_type_pred_if_Dep_fun_type:
  assumes "f : (x : A) \<Rightarrow> B x"
  shows "([x \<Colon> type_pred A] \<Rrightarrow>\<^sub>m type_pred (B x)) f"
  using assms by (intro dep_mono_wrt_predI) auto

lemma Dep_fun_type_if_dep_mono_wrt_pred_type_pred:
  assumes "([x \<Colon> type_pred A] \<Rrightarrow>\<^sub>m type_pred (B x)) f"
  shows "f : (x : A) \<Rightarrow> B x"
  using assms by auto

corollary dep_mono_wrt_pred_type_pred_iff_Dep_fun_type:
  "([x \<Colon> type_pred A] \<Rrightarrow>\<^sub>m type_pred (B x)) f \<longleftrightarrow> f : (x : A) \<Rightarrow> B x"
  using dep_mono_wrt_pred_type_pred_if_Dep_fun_type
    Dep_fun_type_if_dep_mono_wrt_pred_type_pred
  by blast

soft_type_translation
  "([x \<Colon> type_pred A] \<Rrightarrow>\<^sub>m type_pred (B x)) f" \<rightleftharpoons> "f : (x : A) \<Rightarrow> B x"
  using dep_mono_wrt_pred_type_pred_iff_Dep_fun_type by auto


end