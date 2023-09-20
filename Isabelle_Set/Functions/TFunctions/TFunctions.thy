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

overloading
  restrict_left_set \<equiv> "restrict_left :: (set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow>
    (set \<Rightarrow> 'a \<Rightarrow> bool)"
  restrict_left_type \<equiv> "restrict_left :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a type \<Rightarrow>
    ('a \<Rightarrow> 'b \<Rightarrow> bool)"
begin
  definition "restrict_left_set (R :: set \<Rightarrow> _) (A :: set) \<equiv> R\<restriction>\<^bsub>mem_of A\<^esub>"
  definition "restrict_left_type (R :: 'a \<Rightarrow> _) (T :: 'a type) \<equiv> R\<restriction>\<^bsub>type_pred T\<^esub>"
end

lemma restrict_left_set_eq_restrict_left_pred [simp]:
  "restrict_left (R :: set \<Rightarrow> _) (A :: set) = R\<restriction>\<^bsub>mem_of A\<^esub>"
  unfolding restrict_left_set_def by simp

lemma restrict_left_set_iff_restrict_left_pred [iff]:
  "restrict_left (R :: set \<Rightarrow> _) (A :: set) x y \<longleftrightarrow> R\<restriction>\<^bsub>mem_of A\<^esub> x y"
  by simp

lemma restrict_left_type_eq_restrict_left_pred [simp]:
  "restrict_left (R :: 'a \<Rightarrow> _) (T :: 'a type) = R\<restriction>\<^bsub>type_pred T\<^esub>"
  unfolding restrict_left_type_def by simp

lemma restrict_left_type_iff_restrict_left_pred [iff]:
  "restrict_left (R :: 'a \<Rightarrow> _) (T :: 'a type) x y \<longleftrightarrow> R\<restriction>\<^bsub>type_pred T\<^esub> x y"
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