\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Functions\<close>
theory TSFunctions_Base
  imports
    HOTG.SFunctions_Base
    Soft_Types.TFunctions_Base
    TSBinary_Relations_Left_Total
    TSBinary_Relations_Right_Unique
    TSBinary_Relations_Base
begin

unbundle no_HOL_ascii_syntax

subsection \<open>Restrictions\<close>

overloading
  set_fun_restrict_type \<equiv> "fun_restrict :: set \<Rightarrow> set type \<Rightarrow> set"
begin
  definition "(set_fun_restrict_type (f :: set) (T :: set type) :: set) \<equiv>
    fun_restrict f (type_pred T)"
end

lemma set_fun_restrict_type_eq_set_fun_restrict [simp]:
  "(fun_restrict (f :: set) (T :: set type) :: set) = fun_restrict f (type_pred T)"
  unfolding set_fun_restrict_type_def by auto

lemma set_fun_restrict_type_eq_set_fun_restrict_uhint [uhint]:
  assumes "P \<equiv> type_pred T"
  and "f \<equiv> g"
  shows "fun_restrict (f :: set) (T :: set type) :: set \<equiv> fun_restrict g P"
  using assms by simp

subsection \<open>Set-Function Type\<close>

text \<open>Functions might also contain elements outside their domain.\<close>
definition [typedef]: "Dep_Function (A :: set type) (B :: set \<Rightarrow> set type) \<equiv>
  type (\<lambda>f. left_total_on A f \<and> right_unique_on A f \<and> (eval f) : (x : A) \<Rightarrow> (B x))"

abbreviation "Function A B \<equiv> Dep_Function A (\<lambda>_. B)"

translations
  "(x y \<in> A) \<rightarrow>s B" \<rightharpoonup> "(x \<in> A)(y \<in> A) \<rightarrow>s B"
  "(x \<in> A) args \<rightarrow>s B" \<rightharpoonup> "(x \<in> A) \<rightarrow>s args \<rightarrow>s B"
  "(x \<in> A) \<rightarrow>s B" \<rightleftharpoons> "CONST dep_functions A (\<lambda>x. B)"

  "(x y : A) \<rightarrow>s B" \<rightharpoonup> "(x : A)(y : A) \<rightarrow>s B"
  "(x : A) args \<rightarrow>s B" \<rightharpoonup> "(x : A) \<rightarrow>s args \<rightarrow>s B"
  "(x : A) \<rightarrow>s B" \<rightleftharpoons> "CONST Dep_Function A (\<lambda>x. B)"
  (*TODO: explicity type annotation necessary; could be fixed with additional type-checking phase*)
  "(A :: set) \<rightarrow>s B" \<rightleftharpoons> "CONST functions A B"
  "A \<rightarrow>s B" \<rightleftharpoons> "CONST Function A B"

lemma Dep_FunctionI:
  assumes "left_total_on A f"
  and "right_unique_on A f"
  and "eval f : (x : A) \<Rightarrow> (B x)"
  shows "f : (x : A) \<rightarrow>s B x"
  by unfold_types (use assms in auto)

lemma Dep_FunctionE [elim]:
  assumes "f : (x : A) \<rightarrow>s B x"
  obtains "left_total_on A f" "right_unique_on A f" "eval f : (x : A) \<Rightarrow> (B x)"
  using assms unfolding Dep_Function_def by auto

lemma eval_type [type]: "eval : (f : (x : A) \<rightarrow>s B x) \<Rightarrow> (x : A) \<Rightarrow> B x" by auto

lemma Dep_Function_ex1_pairI: "f : ((x : A) \<rightarrow>s B x) \<Longrightarrow> x : A \<Longrightarrow> \<exists>!y. \<langle>x, y\<rangle> \<in> f"
  by (blast dest: right_unique_onD)

lemma Dep_Function_eq_if_pair_mem_if_pair_mem:
  assumes "f : (x : A) \<rightarrow>s B x"
  and "x : A"
  and "\<langle>x, y\<rangle> \<in> f" "\<langle>x, y'\<rangle> \<in> f"
  shows "y = y'"
  using assms by (blast dest: right_unique_onD)

lemma Dep_Function_eval_eq_if_pair_mem [simp]:
  assumes "f : (x : A) \<rightarrow>s B x"
  and "x : A"
  and "\<langle>x, y\<rangle> \<in> f"
  shows "f`x = y"
  using assms by (intro Dep_Function_eq_if_pair_mem_if_pair_mem[symmetric])
  (auto intro: pair_eval_mem_if_ex1_pair_mem dest: right_unique_onD)

lemma Dep_Function_contravariant_dom:
  "\<lbrakk>f : (x : A) \<rightarrow>s B x; \<And>x. x : A' \<Longrightarrow> x : A\<rbrakk> \<Longrightarrow> f : (x : A') \<rightarrow>s B x"
  unfolding Dep_Function_def by unfold_types (auto 0 4 dest: right_unique_onD)

lemma Dep_Function_covariant_codom:
  assumes "f : (x : A) \<rightarrow>s B x"
  and "\<And>x. x : A \<Longrightarrow> f`x : B x \<Longrightarrow> f`x : B' x"
  shows "f : (x : A) \<rightarrow>s B' x"
  using assms unfolding Dep_Function_def meaning_of_type by auto

lemma eval_eq_if_pair_mem_if_Dep_Function:
  assumes "f : (x : A) \<rightarrow>s B x"
  and "x : A"
  and "\<langle>x, y\<rangle> \<in> f"
  shows "f`x = y"
  using assms by (auto dest: right_unique_onD)

lemma pair_mem_if_eval_eq_if_Dep_Function:
  assumes "f : (x : A) \<rightarrow>s B x"
  and "x : A"
  and "f`x = y"
  shows "\<langle>x, y\<rangle> \<in> f"
  using assms by (auto 0 4 dest: right_unique_onD)

lemma Dep_Function_pair_mem_iff_eval_eq:
  assumes "f : (x : A) \<rightarrow>s B x"
  and "x : A"
  shows "\<langle>x, y\<rangle> \<in> f \<longleftrightarrow> f`x = y"
  using assms eval_eq_if_pair_mem_if_Dep_Function pair_mem_if_eval_eq_if_Dep_Function by blast

lemma Dep_Function_cong [cong]:
  assumes "\<And>x. x : A \<longleftrightarrow> x : A'"
  and "\<And>x y. x : A' \<Longrightarrow> y : B x \<longleftrightarrow> y : B' x"
  shows "f : (x : A) \<rightarrow>s B x \<longleftrightarrow> f : (x : A') \<rightarrow>s B' x"
  using assms by (auto intro!: Dep_fun_typeI Dep_FunctionI left_total_onI intro: right_unique_onD
    elim!: Dep_FunctionE)

lemma Dep_Function_mem_dom [simp]:
  assumes "f : (x : A) \<rightarrow>s B x" "x : A"
  shows "x \<in> dom f"
  using assms by auto

lemma Dep_Function_pair_memE [elim]:
  assumes "f : (x : A) \<rightarrow>s B x" "p : \<Sum>x : A. (B x)"
  and "p \<in> f"
  obtains x y where "x : A" "y : B x" "f`x = y" "p = \<langle>x, y\<rangle>"
  using assms by auto

lemma Dep_Function_repl_eval_subset [simp]:
  assumes "f : (x : Element A) \<rightarrow>s B x"
  shows "{\<langle>x, f`x\<rangle> | x \<in> A} \<subseteq> f"
  using assms by (auto elim!: Dep_FunctionE)

lemma Dep_Function_eval_eqI:
  assumes "f : (x : A) \<rightarrow>s B x"
  and "g : (x : A') \<rightarrow>s B' x"
  and "x : A & A'"
  and "f \<subseteq> g"
  shows "f`x = g`x"
proof -
  from assms have "x : A" "x : A'" by (auto elim!: Int_typeE)
  with assms have "f`x : B x" "\<langle>x, f`x\<rangle> \<in> g" by (auto 0 5)
  then show "f`x = g`x" by auto
qed


text \<open>Clean functions only contain elements in their domain.\<close>
definition [typedef]: "CDep_Function A B \<equiv> Dep_Function A B & Dep_Bin_Rel A B"

abbreviation "CFunction A B \<equiv> CDep_Function A (\<lambda>_. B)"

bundle isa_set_clean_set_functions_syntax
begin
syntax
  "_clean_set_functions_telescope" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<rightarrow>cs" 55)
end
bundle no_isa_set_clean_set_functions_syntax
begin
syntax
  "_clean_set_functions_telescope" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<rightarrow>cs" 55)
end
unbundle isa_set_clean_set_functions_syntax

translations
  "(x y : A) \<rightarrow>cs B" \<rightharpoonup> "(x : A)(y : A) \<rightarrow>cs B"
  "(x : A) args \<rightarrow>cs B" \<rightharpoonup> "(x : A) \<rightarrow>cs args \<rightarrow>cs B"
  "(x : A) \<rightarrow>cs B" \<rightleftharpoons> "CONST CDep_Function A (\<lambda>x. B)"
  "A \<rightarrow>cs B" \<rightleftharpoons> "CONST CFunction A B"

lemma mem_dep_functions_iff_CDep_Function:
  "(f \<in> (x \<in> A) \<rightarrow>s (B x)) \<longleftrightarrow> (f : (x : Element A) \<rightarrow>cs Element (B x))"
  by unfold_types (auto intro!: mem_dep_functionsI left_total_onI elim!: mem_dep_functionsE
    simp: meaning_of_type intro!: right_unique_onI dest: right_unique_onD)

soft_type_translation
  "f \<in> (x \<in> A) \<rightarrow>s (B x)" \<rightleftharpoons> "f : (x : Element A) \<rightarrow>cs Element (B x)"
  using mem_dep_functions_iff_CDep_Function by auto

lemma CDep_FunctionI:
  assumes "f : (x : A) \<rightarrow>s B x"
  and "f : Dep_Bin_Rel A B"
  shows "f : (x : A) \<rightarrow>cs B x"
  unfolding CDep_Function_def using assms by auto

lemma Dep_Function_if_CDep_Function [derive]:
  "f : (x : A) \<rightarrow>cs B x \<Longrightarrow> f : (x : A) \<rightarrow>s B x"
  unfolding CDep_Function_def by (drule Int_typeD1)

lemma Dep_Bin_Rel_if_CDep_Function [derive]:
  "f : (x : A) \<rightarrow>cs (B x) \<Longrightarrow> f : Dep_Bin_Rel A B"
  unfolding CDep_Function_def by (drule Int_typeD2)

lemma CDep_Function_pair_memE [elim]:
  assumes "f : (x : A) \<rightarrow>cs B x"
  and "p \<in> f"
  obtains x y where "x : A" "y : B x" "f`x = y" "p = \<langle>x, y\<rangle>"
proof (rule Dep_Function_pair_memE)
  from assms have "f : Dep_Bin_Rel A B" by discharge_types
  with assms show "p : \<Sum>x : A. (B x)" by blast
qed auto

lemma CDep_Function_covariant_codom:
  assumes "f : (x : A) \<rightarrow>cs B x"
  and "\<And>x. x : A \<Longrightarrow> f`x : B x \<Longrightarrow> f`x : B' x"
  shows "f : (x : A) \<rightarrow>cs B' x"
proof -
  from assms have "f : (x : A) \<rightarrow>s B x" by discharge_types
  with assms have "f : (x : A) \<rightarrow>s B' x" by (elim Dep_Function_covariant_codom)
  from assms have "f : Dep_Bin_Rel A B" by discharge_types
  with assms have "f : Dep_Bin_Rel A B'"
    by (elim Dep_Bin_Rel_covariant_codom) auto
  then show ?thesis by (intro CDep_FunctionI) discharge_types
qed

lemma empty_CFunction [type]: "{} : Element {} \<rightarrow>cs X"
  by (intro CDep_FunctionI Dep_FunctionI Dep_Bin_RelI) (auto dest: ElementD)

lemma singleton_CFunctionI [intro]: "y : B \<Longrightarrow> {\<langle>x, y\<rangle>} : Element {x} \<rightarrow>cs B"
  by (intro CDep_FunctionI Dep_FunctionI Dep_Bin_RelI)
    (auto dest: ElementD intro: ElementI)


end