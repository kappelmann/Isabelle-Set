section\<open>Functions\<close>
theory Functions
imports
  Bin_Rels
  Rewrite
  HOTG.Set_Difference
begin

subsection \<open>Evaluation of Functions\<close>

definition "eval S x \<equiv> THE y. \<langle>x, y\<rangle> \<in> S"

bundle isa_set_eval_syntax begin notation eval ("_`_" [999, 1000] 999) end
bundle no_isa_set_eval_syntax begin no_notation eval ("_`_" [999, 1000] 999) end
unbundle isa_set_eval_syntax

lemma eval_singleton_eq [simp]: "{\<langle>x, y\<rangle>}`x = y"
  unfolding eval_def by auto

lemma eval_repl_eq [simp]: "x \<in> A \<Longrightarrow> {\<langle>a, f a\<rangle> | a \<in> A}`x = f x"
  unfolding eval_def by auto

lemma cons_eval_eq [simp]:
  "x \<notin> dom A \<Longrightarrow> (cons \<langle>x, y\<rangle> A)`x = y"
  unfolding eval_def by auto

lemma cons_eval_eq' [simp]:
  "x \<noteq> y \<Longrightarrow> (cons \<langle>y, z\<rangle> A)`x = A`x"
  unfolding eval_def by auto

lemma bin_union_eval_eq_left_eval [simp]:
  "x \<notin> dom B \<Longrightarrow> (A \<union> B)`x = A`x"
  unfolding eval_def by (auto elim: not_mem_domE)

lemma bin_union_eval_eq_right_eval [simp]:
  "x \<notin> dom A \<Longrightarrow> (A \<union> B)`x = B`x"
  unfolding eval_def by (auto elim: not_mem_domE)


subsection \<open>Functional Part of a Set\<close>

text \<open>The following expresses that a set S is a function on A (it need not even be
relation elsewhere).\<close>

definition "function A S \<equiv> \<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> S"

(*TODO: alternative with type constraints rather than set constraints*)
(* definition "fu A B \<equiv> type (\<lambda>f. \<forall>x : A. \<exists>!y. \<langle>x, y\<rangle> \<in> f \<and> y : B x)"
definition "fu3 A B C \<equiv> fu A (\<lambda>x. fu (B x) (C x))" *)

lemma functionI [intro]:
  assumes "\<And>x y y'. \<lbrakk>x \<in> A; \<langle>x, y\<rangle> \<in> S; \<langle>x, y'\<rangle> \<in> S\<rbrakk> \<Longrightarrow> y = y'"
  and "\<And>x. x \<in> A \<Longrightarrow> \<exists>y. \<langle>x, y\<rangle> \<in> S"
  shows "function A S"
  unfolding function_def by (auto intro: assms)

lemma functionD: "function A S \<Longrightarrow> x \<in> A \<Longrightarrow> \<exists>!y. \<langle>x, y\<rangle> \<in> S"
  unfolding function_def by auto

lemma function_right_unique:
  "\<lbrakk>function A S; x \<in> A; S`x = y; S`x = y'\<rbrakk> \<Longrightarrow> y = y'"
  unfolding function_def by auto

lemma function_pair_eval_mem_if_mem_dom [elim]:
  "\<lbrakk>function A S; x \<in> A\<rbrakk> \<Longrightarrow> \<langle>x, S`x\<rangle> \<in> S"
  unfolding eval_def function_def by (rule theI', drule ballD)

lemma function_pair_mem_iff_eval_eq [iff]:
  "\<lbrakk>function A S; x \<in> A\<rbrakk> \<Longrightarrow> \<langle>x, y\<rangle> \<in> S \<longleftrightarrow> S`x = y"
  unfolding function_def eval_def by (auto dest!: ballD intro: theI')

lemma function_mem_domE:
  assumes "function A S"
  and "x \<in> A"
  obtains y where "S`x = y"
  using assms by auto

lemma function_empty_dom: "function {} S"
  unfolding function_def by auto


subsection \<open>Generic Notion of a Function\<close>

definition [typedef]: "Fun \<equiv> (\<lambda>f. function (dom f) f) \<sqdot> Bin_Rel"

lemma
  FunI: "\<lbrakk>f : Bin_Rel; function (dom f) f\<rbrakk> \<Longrightarrow> f : Fun" and
  FunD: "f : Fun \<Longrightarrow> function (dom f) f \<and> f : Bin_Rel"
  unfolding Fun_def by auto

lemma FunE [elim]:
  assumes "f : Fun"
  obtains "f : Bin_Rel" "function (dom f) f"
  using assms by (auto dest: FunD)

lemma Fun_right_unique:
  assumes "f : Fun"
  and "x \<in> dom f"
  and "f`x = y"
  and "f`x = y'"
  shows "y = y'"
proof -
  from \<open>f : Fun\<close> have "function (dom f) f" by (auto dest: FunD)
  with function_right_unique show "y = y'" using assms by auto
qed

lemma Fun_pair_mem_iff_eval_eq:
  "f : Fun \<Longrightarrow> x \<in> (dom f) \<Longrightarrow> \<langle>x, y\<rangle> \<in> f \<longleftrightarrow> f`x = y"
  by auto

lemma Fun_eval_eq_if_pair_mem [simp]:
  "\<lbrakk>f : Fun; \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> f`x = y"
  by auto

lemma Fun_fst_snd_eq_pair_if_mem [simp]:
  "\<lbrakk>f : Fun; p \<in> f\<rbrakk> \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by auto

lemma Fun_fst_snd_mem_if_mem:
  "\<lbrakk>f : Fun; p \<in> f\<rbrakk> \<Longrightarrow> \<langle>fst p, snd p\<rangle> \<in> f"
  by auto

lemma Fun_fst_mem_dom_if_mem:
  "\<lbrakk>f : Fun; p \<in> f\<rbrakk> \<Longrightarrow> fst p \<in> (dom f)"
  by auto

lemma Fun_eval_fst_eq [simp]:
  "\<lbrakk>f : Fun; p \<in> f\<rbrakk> \<Longrightarrow> f`(fst p) = snd p"
  by auto

lemma Fun_mem_domE:
  assumes "f : Fun"
  and "x \<in> dom f"
  obtains y where "f`x = y"
  using assms by auto

lemma Fun_memE [elim]:
  assumes "f : Fun"
  and "p \<in> f"
  obtains x y where "p = \<langle>x, y\<rangle>" "f`x = y"
  using assms by (auto dest: Fun_fst_snd_eq_pair_if_mem[symmetric])

subsection \<open>Functions with Explicit Domain and Codomain\<close>

definition [typedef]: "Dep_Function A B \<equiv> function A \<sqdot> Subset (\<Sum>x \<in> A. (B x))"

abbreviation "Function A B \<equiv> Dep_Function A (\<lambda>_. B)"

text \<open>Set model of \<^term>\<open>Dep_Function\<close>:\<close>

definition
  "dep_functions A B \<equiv> {f \<in> powerset (\<Sum>x \<in> A. (B x)) | function A f}"

(*TODO: localise*)
syntax
  "_dep_functions"  :: \<open>[pttrns, set, set] \<Rightarrow> set type\<close> ("(2\<Prod>_ \<in> _./ _)" [0, 0, 100])
  "_dep_functions2" :: \<open>[pttrns, set, set] \<Rightarrow> set type\<close>
translations
  "\<Prod>x xs \<in> A. B" \<rightharpoonup> "CONST dep_functions A (\<lambda>x. _dep_functions2 xs A B)"
  "_dep_functions2 x A B" \<rightharpoonup> "\<Prod>x \<in> A. B"
  "\<Prod>x \<in> A. B" \<rightleftharpoons> "CONST dep_functions A (\<lambda>x. B)"

text \<open>Syntax rules converting soft type notation to underlying set representation:\<close>
syntax
  "_telescope'" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<rightarrow>" 50)
translations
  "(x \<in> A) \<rightarrow> (y \<in> B) \<rightarrow> C" \<rightleftharpoons> "(x \<in> A) \<rightarrow> \<Prod>y \<in> B. C"
  "(x \<in> A) \<rightarrow> B \<rightarrow> C" \<rightleftharpoons> "(x \<in> A) \<rightarrow> \<Prod>_ \<in> B. C"
  "A \<rightarrow> (y \<in> B) \<rightarrow> C" \<rightleftharpoons> "A \<rightarrow> \<Prod>y \<in> B. C"
  "A \<rightarrow> B \<rightarrow> C" \<rightleftharpoons> "A \<rightarrow> \<Prod>_ \<in> B. C"
  "\<Prod>x \<in> A. ((y \<in> B) \<rightarrow> C)" \<rightharpoonup> "\<Prod>x \<in> A. \<Prod>y \<in> B. C"
  "\<Prod>x \<in> A. (B \<rightarrow> C)" \<rightharpoonup> "\<Prod>x \<in> A. \<Prod>_ \<in> B. C"
  "(x \<in> A) \<rightarrow> B" \<rightleftharpoons> "CONST Dep_Function A (\<lambda>x. B)"
  "A \<rightarrow> B" \<rightleftharpoons> "CONST Function A B"

soft_type_translation "f \<in> \<Prod>x \<in> A. (B x)" \<rightleftharpoons> "f : (x \<in> A) \<rightarrow> B x"
  unfolding dep_functions_def by unfold_types auto

corollary mem_dep_functions_iff_Dep_Function:
  "f \<in> \<Prod>x \<in> A. (B x) \<longleftrightarrow> f : (x \<in> A) \<rightarrow> B x"
  by auto

corollary Element_dep_functions_iff_Dep_Function:
  "f : (Element \<Prod>x \<in> A. (B x)) \<longleftrightarrow> f : (x \<in> A) \<rightarrow> B x"
  by (subst mem_iff_Element[symmetric]) (fact mem_dep_functions_iff_Dep_Function)

(*TODO: rules like these should automatically be derivable from above lemma and
allow for type simplification*)
lemma Dep_Function_if_Element_dep_functions [derive]:
  "f : Element (\<Prod>x \<in> A. (B x)) \<Longrightarrow> f : (x \<in> A) \<rightarrow> B x"
  by (fact iffD1[OF Element_dep_functions_iff_Dep_Function])

lemma Element_dep_functions_if_Dep_Function [backward_derive]:
  "f : (x \<in> A) \<rightarrow> B x \<Longrightarrow> f : Element (\<Prod>x \<in> A. (B x))"
  by (fact iffD2[OF Element_dep_functions_iff_Dep_Function])

subsection \<open>Properties of generic functions\<close>

lemma Dep_Function_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> f : (x \<in> A) \<rightarrow> B x \<longleftrightarrow> f : (x \<in> A') \<rightarrow> B' x"
  unfolding Dep_Function_def by auto

lemma function_if_Dep_Function: "f : (x \<in> A) \<rightarrow> B x \<Longrightarrow> function A f"
  by unfold_types

lemma Dep_Function_Subset_dep_pairs [derive]:
  "f : (x \<in> A) \<rightarrow> B x \<Longrightarrow> f : Subset (\<Sum>x \<in> A. (B x))"
  by unfold_types

lemma Dep_Function_dom_eq [simp]:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  shows "dom f = A"
proof (rule eqI)
  have "function A f" by (rule function_if_Dep_Function) discharge_types
  fix x assume "x \<in> A"
  then show "x \<in> dom f"
    by (intro mem_domI) (auto dest!: functionD[OF \<open>function A f\<close>])
next
  have f_subset: "f \<subseteq> \<Sum>x \<in> A. (B x)" by discharge_types
  fix x assume "x \<in> dom f"
  then obtain y where "\<langle>x, y\<rangle> \<in> f "by auto
  with f_subset have "\<langle>x, y\<rangle> \<in> \<Sum>x \<in> A. (B x)" by auto
  then show "x \<in> A" by simp
qed

lemma Fun_if_Dep_Function [derive]: "f : (x \<in> A) \<rightarrow> B x \<Longrightarrow> f : Fun"
  by (rule FunI) (auto dest: function_if_Dep_Function)

lemma Function_if_Dep_Function [derive]:
  "f : (x \<in> A) \<rightarrow> B x \<Longrightarrow> f : A \<rightarrow> (\<Union>x \<in> A. B x)"
  by unfold_types auto

lemma Dep_FunctionI:
  assumes func_f: "function A f"
  and "f : Bin_Rel"
  and [simp]: "dom f = A"
  and f_eval_x_mem: "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> B x"
  shows "f : (x \<in> A) \<rightarrow> B x"
proof -
  {
    have f_subset: "f \<subseteq> (dom f) \<times> (rng f)"
      by (rule Bin_Rel_subset_pairs_dom_rng) discharge_types
    fix p assume "p \<in> f"
    with f_subset obtain x y where "x \<in> A" and [simp]: "p = \<langle>x, y\<rangle>" by auto
    with \<open>p \<in> f\<close> have "f`x = y" by auto
    moreover have "f`x \<in> B x" by (fact f_eval_x_mem[OF \<open>x \<in> A\<close>])
    ultimately have "p \<in> \<Sum>x \<in> A. B x" by auto
  }
  then show ?thesis
    by (intro iffD1[OF mem_dep_functions_iff_Dep_Function])
      (auto simp only: dep_functions_def)
qed

lemma FunctionI' [derive]: "f : function A \<sqdot> Relation A B \<Longrightarrow> f : A \<rightarrow> B"
  by unfold_types

lemma Dep_Function_pair_eval_mem_if_mem [elim]:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  and "x \<in> A"
  shows "\<langle>x, f`x\<rangle> \<in> f"
  using assms by (auto dest: function_if_Dep_Function)

lemma Dep_Function_mem_dom_if_pair_mem:
  "\<lbrakk>f : (x \<in> A) \<rightarrow> B x; \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> x \<in> A"
  by unfold_types auto

lemma Dep_Function_mem_codom_if_pair_mem:
  "\<lbrakk>f : (x \<in> A) \<rightarrow> B x; \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y \<in> B x"
  by unfold_types auto

lemma Dep_Function_eval_mem_if_mem [elim]:
  "\<lbrakk>f : (x \<in> A) \<rightarrow> B x; x \<in> A\<rbrakk> \<Longrightarrow> f`x \<in> B x"
  using Dep_Function_mem_codom_if_pair_mem
  by (fast dest: Dep_Function_pair_eval_mem_if_mem)

lemma Dep_Function_fst_mem_dom_if_mem [elim]:
  "\<lbrakk>f : (x \<in> A) \<rightarrow> B x; p \<in> f\<rbrakk> \<Longrightarrow> fst p \<in> A"
  by (rule Dep_Function_mem_dom_if_pair_mem)
    (auto intro: Fun_fst_snd_mem_if_mem)

lemma Dep_Function_snd_mem_codom_if_mem:
  "\<lbrakk>f : (x \<in> A) \<rightarrow> B x; p \<in> f\<rbrakk> \<Longrightarrow> snd p \<in> B (fst p)"
  by (rule Dep_Function_mem_codom_if_pair_mem)
    (auto intro: Fun_fst_snd_mem_if_mem)

lemma Dep_Function_subset_pairs: "f : (x \<in> A) \<rightarrow> B x \<Longrightarrow> f \<subseteq> A \<times> (\<Union>x \<in> A. B x)"
  by auto

lemma Function_subset_pairs [derive]:
  "f : A \<rightarrow> B \<Longrightarrow> f : Subset (A \<times> B)"
  by auto

lemma Dep_Function_fst_snd_eq_pair [simp]:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  and "p \<in> f"
  shows "\<langle>fst p, snd p\<rangle> = p"
  using assms by (auto intro!: Fun_fst_snd_eq_pair_if_mem)

lemma Dep_Function_fst_eval_fst_eq_pair [simp]:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  and "p \<in> f"
  shows "f`(fst p) = snd p"
  using assms by auto

lemma Dep_Function_pair_mem_iff_eval_eq:
  "f : (x \<in> A) \<rightarrow> B x \<Longrightarrow> x \<in> A \<Longrightarrow> \<langle>x, y\<rangle> \<in> f \<longleftrightarrow> f`x = y"
  by auto

lemma Dep_Fun_eval_eq_if_pair_mem [simp]:
  "\<lbrakk>f : (x \<in> A) \<rightarrow> B x; \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> f`x = y"
  by auto

lemma Dep_Function_mem_domE:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  and "x \<in> A"
  obtains y where "f`x = y" "y \<in> B x"
  using assms Dep_Function_eval_mem_if_mem by auto

lemma Dep_Function_memE [elim]:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  and "p \<in> f"
  obtains x y where "p = \<langle>x, y\<rangle>" "x \<in> A" "y \<in> B x" "f`x = y"
proof -
  assume hyp: "\<And>x y. p = \<langle>x, y\<rangle> \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f`x = y \<Longrightarrow> thesis"
  obtain x y where "p = \<langle>x, y\<rangle>" "f`x = y"
    by (rule Fun_memE) (insert assms, auto)
  then show thesis
  proof (intro hyp[of x y])
    from assms have "p = \<langle>fst p, snd p\<rangle>" by auto
    moreover from Dep_Function_fst_mem_dom_if_mem have "fst p \<in> A"
      using assms by auto
    moreover from Dep_Function_snd_mem_codom_if_mem have "snd p \<in> B (fst p)"
      using assms by auto
    ultimately show "x \<in> A" and "y \<in> B x" using \<open>p = \<langle>x, y\<rangle>\<close> by auto
  qed assumption
qed

lemma Dep_Function_Rep_eval_eq [simp]:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  shows "{\<langle>x, f`x\<rangle> | x \<in> A} = f"
  using assms by (intro eqI) auto

lemma Dep_Function_empty_dom_iff_eq_empty [iff]: "f : (x \<in> {}) \<rightarrow> B x \<longleftrightarrow> f = {}"
  by unfold_types auto

lemma Dep_Function_subsetI:
  assumes f_type: "f : (x \<in> A) \<rightarrow> B x"
  and g_type: "g : (x \<in> A') \<rightarrow> B' x"
  and A_subset: "A \<subseteq> A'"
  and f_g_agree: "\<And>x. x \<in> A \<Longrightarrow> f`x = g`x"
  shows "f \<subseteq> g"
proof
  fix p assume "p \<in> f"
  then obtain x y where p_eq: "p = \<langle>x, y\<rangle>" and "x \<in> A" "f`x = y"
    by (rule Dep_Function_memE[OF f_type])
  with f_g_agree have p_eq: "p = \<langle>x, g`x\<rangle>" by blast
  show "p \<in> g"
    by (subst p_eq, rule Dep_Function_pair_eval_mem_if_mem[OF g_type])
      (insert A_subset, auto)
qed

lemma Dep_Function_eval_eqI:
  assumes "f : (x \<in> A) \<rightarrow> B x" "g : (x \<in> A') \<rightarrow> B' x"
  and "f \<subseteq> g"
  and "x \<in> A \<inter> A'"
  shows "f`x = g`x"
proof -
  from assms have "\<langle>x, f`x\<rangle> \<in> g" and "\<langle>x, g`x\<rangle> \<in> g" by auto
  then show ?thesis by auto
qed

lemma Dep_Function_ex_dom_iff:
  "\<exists>A. f : (x \<in> A) \<rightarrow> B x \<longleftrightarrow> f : (x \<in> dom f) \<rightarrow> B x"
  by auto

lemma empty_Function [type]: "{} : {} \<rightarrow> X" by auto

lemma singleton_FunctionI [intro]: "y \<in> B \<Longrightarrow> {\<langle>x, y\<rangle>} : {x} \<rightarrow> B"
  by (rule Dep_FunctionI) auto

lemma Function_eq_singleton [simp]: "f : {a} \<rightarrow> {b} \<Longrightarrow> f = {\<langle>a, b\<rangle>}"
  by (unfold_types, unfold function_def) auto

lemma cons_FunctionI:
  "\<lbrakk>f : A \<rightarrow> B; x \<notin> A\<rbrakk> \<Longrightarrow> cons \<langle>x, y\<rangle> f : A \<union> {x} \<rightarrow> B \<union> {y}"
  by (unfold_types, unfold function_def) auto

lemma cons_FunctionI':
  assumes "f : A \<rightarrow> B"
  and "x \<notin> A"
  and "y \<in> B"
  shows "cons \<langle>x, y\<rangle> f : A \<union> {x} \<rightarrow> B"
proof -
  from assms(1-2) have "cons \<langle>x, y\<rangle> f : A \<union> {x} \<rightarrow> B \<union> {y}"
    by (rule cons_FunctionI)
  moreover from \<open>y \<in> B\<close> have "B \<union> {y} = B" by simp
  ultimately show "cons \<langle>x, y\<rangle> f : A \<union> {x} \<rightarrow> B" by simp
qed

lemma singleton_bin_union_FunctionI:
  "\<lbrakk>f : A \<rightarrow> B; x \<notin> A\<rbrakk> \<Longrightarrow> {\<langle>x, y\<rangle>} \<union> f : A \<union> {x} \<rightarrow> B \<union> {y}"
  by (subst singleton_bin_union_eq_cons, fact cons_FunctionI)


subsection \<open>Lambda abstraction\<close>

definition lambda :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "lambda A f \<equiv> {\<langle>x, f x\<rangle> | x \<in> A}"

(*TODO: localise*)
syntax
  "_lam"  :: "[pttrns, set, set] \<Rightarrow> set" ("(2\<lambda>_ \<in> _./ _)" 60)
  "_lam2" :: \<open>[pttrns, set, set] \<Rightarrow> set\<close>
translations
  "\<lambda>x xs \<in> A. f" \<rightharpoonup> "CONST lambda A (\<lambda>x. _lam2 xs A f)"
  "_lam2 x A f" \<rightharpoonup> "\<lambda>x \<in> A. f"
  "\<lambda>x \<in> A. f" \<rightleftharpoons> "CONST lambda A (\<lambda>x. f)"

lemma lambda_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> f x = f' x\<rbrakk> \<Longrightarrow> (\<lambda>x \<in> A. f x) = \<lambda>x \<in> A'. f' x"
  unfolding lambda_def by auto

lemma eval_lambda_eq [simp]: "a \<in> A \<Longrightarrow> (\<lambda>x \<in> A. f x)`a = f a"
  unfolding lambda_def by auto

lemma eval_lambda_uncurry_eq [simp]:
  assumes "a \<in> A" "b \<in> B"
  shows "(\<lambda>p \<in> A \<times> B. uncurry f p)`\<langle>a, b\<rangle> = f a b"
  using assms by auto

lemma lambda_pairs_eq_lambda_uncurry:
  "(\<lambda>p \<in> A \<times> B. f p) = (\<lambda>\<langle>a, b\<rangle> \<in> A \<times> B. f \<langle>a, b\<rangle>)"
  by (rule lambda_cong) auto

lemma lambda_pair_mem_if_mem [intro]: "a \<in> A \<Longrightarrow> \<langle>a, f a\<rangle> \<in> \<lambda>x \<in> A. f x"
  unfolding lambda_def by auto

lemma lambda_memE [elim]:
  assumes "p \<in> \<lambda>x \<in> A. f x"
  obtains x y where "p = \<langle>x, y\<rangle>" "x \<in> A" "f x = y"
  using assms unfolding lambda_def by auto

lemma lambda_memD [dest]: "\<langle>a, b\<rangle> \<in> \<lambda>x \<in> A. f x \<Longrightarrow> b = f a"
  by auto

lemma lambda_dom_eq [simp]: "dom (\<lambda>x \<in> A. f x) = A"
  unfolding lambda_def by simp

lemma app_eq_if_mem_if_lambda_eq:
  "\<lbrakk>(\<lambda>x \<in> A. f x) = \<lambda>x \<in> A. g x; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
  by (erule eqE) auto


subsubsection\<open>Type-theoretic rules\<close>

lemma lambda_type [type]:
  "lambda : (A : Set) \<Rightarrow> ((x : Element A) \<Rightarrow> Element (B x)) \<Rightarrow> (x \<in> A) \<rightarrow> B x"
  by unfold_types auto

(*TODO: it is necessery to specify this backward_derive rule since although
above type rule encodes that the type of f depends on A, this will not be
used in the type_derivator when proving `lambda A f : T`; more specifically,
the derivator will merely derivate types for A and f and then see if they can be
fed to Dep_fun_typeE together with lambda_type*)
lemma lambda_app_type [backward_derive]:
  assumes "A : Set" "f : (x : Element A) \<Rightarrow> Element (B x)"
  shows "lambda A f : (x \<in> A) \<rightarrow> B x"
  by discharge_types

lemma uncurry_type [type]:
  "uncurry : ((a : Element A) \<Rightarrow> (b : Element B) \<Rightarrow> C \<langle>a, b\<rangle>) \<Rightarrow>
    (p : Element (A \<times> B)) \<Rightarrow> C p"
  unfolding uncurry_def by unfold_types auto

(*TODO: if f is a lambda abstraction, the derivator must use backward_derive
rules to prove its type before being able to apply it to uncurry_type together
with Dep_fun_typeE; so we need to create this backward_derive rule to guide
the derivator*)
lemma uncurry_app_type [backward_derive]:
  assumes "f : (a : Element A) \<Rightarrow> (b : Element B) \<Rightarrow> C \<langle>a, b\<rangle>"
  shows "uncurry f : (p : Element (A \<times> B)) \<Rightarrow> C p"
  by discharge_types

lemma eval_type [type]:
  "eval: ((x \<in> A) \<rightarrow> B x) \<Rightarrow> (x : Element A) \<Rightarrow> Element (B x)"
  (*TOOD: the type derivator should convert the set-theoretic statement
    Dep_Function_eval_mem_if_mem to a type-theoretic one*)
  using Dep_Function_eval_mem_if_mem
  by (intro Dep_fun_typeI) (auto intro: ElementI dest: ElementD)

notepad
begin
  have
    "\<lbrakk>f : (x \<in> A) \<rightarrow> (y \<in> B x) \<rightarrow> C x y; a: Element A; b: Element (B a)\<rbrakk>
      \<Longrightarrow> f`a`b: Element (C a b)"
    (*TODO: should not need an increase of the limit*)
    using [[type_derivation_depth=3]]
    by discharge_types
end

lemma lambda_type_dom_subset_if_Dep_Function:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  and "A' \<subseteq> A"
  shows "(\<lambda>a \<in> A'. f`a) : (x \<in> A') \<rightarrow> B x"
  using assms by (intro Dep_FunctionI) auto

lemma lambda_type_dom_bin_inter_if_Dep_Function:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  shows "(\<lambda>a \<in> A \<inter> A'. f`a) : (x \<in> A \<inter> A') \<rightarrow> B x"
  using assms by (rule lambda_type_dom_subset_if_Dep_Function) auto


subsection \<open>Extensionality\<close>

lemma Dep_Function_ext:
  assumes "f : (x \<in> A) \<rightarrow> B x" "g : (x \<in> A) \<rightarrow> C x"
  and "\<And>x. x \<in> A \<Longrightarrow> f`x = g`x"
  shows "f = g"
  by (rule subset_antisym; rule Dep_Function_subsetI) (insert assms, auto)

lemma lambda_ext:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  and "\<And>a. a \<in> A \<Longrightarrow> g a = f`a"
  shows "(\<lambda>a \<in> A. g a) = f"
  unfolding lambda_def
  using assms
  by (rewrite at "{\<langle>x, g x\<rangle> | x \<in> A}" to "{\<langle>x, f`x\<rangle> | x \<in> A}" repl_cong) auto

lemma Dep_Function_eta [simp]: "f : (x \<in> A) \<rightarrow> B x \<Longrightarrow> (\<lambda>x \<in> A. f`x) = f"
  by (rule Dep_Function_ext) auto

lemma Dep_Function_eq_if_subset:
  assumes f_type: "f : (x \<in> A) \<rightarrow> B x" and g_type: "g : (x \<in> A) \<rightarrow> C x"
  and "f \<subseteq> g"
  shows "f = g"
proof (rule eqI)
  fix p assume "p \<in> g"
  with g_type obtain x y where [simp]: "p = \<langle>x, y\<rangle>" "g`x = y" "x \<in> A" by blast
  then have [simp]: "f`x = g`x" by (intro Dep_Function_eval_eqI) auto
  from Dep_Function_pair_mem_iff_eval_eq show "p \<in> f" by auto
qed (insert assms, auto)

(*Every element of `(x \<in> A) \<rightarrow> B x` may be expressed as a lambda abstraction*)
lemma Dep_Function_eq_lambdaE:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  obtains g where "g : (x : Element A) \<Rightarrow> Element (B x)" and "f = (\<lambda>x \<in> A. g x)"
proof
  let ?g="(\<lambda>x. f`x)"
  show "f = (\<lambda>x \<in> A. ?g x)" by auto
  show "?g : (x : Element A) \<Rightarrow> Element (B x)" by discharge_types
qed

(*note: no contravariance with current definition possible*)
lemma Dep_Function_covariant_codom:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  and "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> B x \<Longrightarrow> f`x \<in> B' x"
  shows "f : (x \<in> A) \<rightarrow> B' x"
  using assms by (intro Dep_FunctionI) (auto intro!: functionI)

corollary Dep_Function_covariant_codom_subset:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  and "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x"
  shows "f : (x \<in> A) \<rightarrow> C x"
  using assms(2) by (intro Dep_Function_covariant_codom[OF assms(1)]) auto

(*Larry: Such functions arise in non-standard datatypes, ZF/ex/Ntree for
  instance.*)
lemma Dep_Function_collectI:
  assumes "f : (x \<in> A) \<rightarrow> B x"
  and "\<And>x. x \<in> A \<Longrightarrow> P x (f`x)"
  shows "f : (x \<in> A) \<rightarrow> {y \<in> B x | P x y}"
  by (rule Dep_Function_covariant_codom) (insert assms, auto)

lemma Dep_Function_collectD:
  assumes "f : (x \<in> A) \<rightarrow> {y \<in> B x | P x y}"
  shows "f : (x \<in> A) \<rightarrow> B x" and "\<And>x. x \<in> A \<Longrightarrow> P x (f`x)"
proof -
  from assms show "f : (x \<in> A) \<rightarrow> B x"
    by (rule Dep_Function_covariant_codom_subset) auto
  fix x assume "x \<in> A"
  then show "P x (f`x)" by (auto dest: Dep_Function_eval_mem_if_mem[OF assms])
qed


subsection \<open>Injectivity and surjectivity\<close>

definition "injective A f \<equiv> \<forall>x x' \<in> A. f`x = f`x' \<longrightarrow> x = x'"

definition "surjective B f \<equiv> \<forall>y \<in> B. \<exists>x. f`x = y"

lemma injectiveI:
  assumes "\<And>x x'. x \<in> A \<Longrightarrow> x' \<in> A \<Longrightarrow> f`x = f`x' \<Longrightarrow> x = x'"
  shows "injective A f"
  unfolding injective_def using assms by simp

lemma surjectiveI:
  assumes "\<And>y. y \<in> B \<Longrightarrow> \<exists>x \<in> A. f`x = y"
  shows "surjective B f"
  unfolding surjective_def using assms by blast


text \<open>Extend a function's domain by mapping new elements to the empty set.\<close>

definition triv_ext :: "set \<Rightarrow> set \<Rightarrow> set"
  where "triv_ext A f \<equiv> f \<union> (\<lambda>x \<in> (A \<setminus> dom f). {})"

lemma dom_triv_ext_eq [simp]: "dom (triv_ext A f) = dom f \<union> A"
  unfolding triv_ext_def by auto


subsection \<open>Composition\<close>

definition "fun_comp g f \<equiv> \<lambda>x \<in> dom f. g`(f`x)"

bundle isa_set_fun_comp_syntax begin notation fun_comp (infixr "\<circ>" 80) end
bundle no_isa_set_fun_comp_syntax begin no_notation fun_comp (infixr "\<circ>" 80) end
unbundle isa_set_fun_comp_syntax

lemma fun_comp_type [type]:
  "(\<circ>) : ((x \<in> B) \<rightarrow> C x) \<Rightarrow> (f : A \<rightarrow> B) \<Rightarrow> (x \<in> A) \<rightarrow> C (f`x)"
  unfolding fun_comp_def
  by (intro Dep_fun_typeI Dep_FunctionI) auto

lemma lambda_comp_lambda_eq [simp]:
  "f : Element A \<Rightarrow> Element B \<Longrightarrow> (\<lambda>y \<in> B. g y) \<circ> (\<lambda>x \<in> A. f x) = \<lambda>x \<in> A. g (f x)"
  unfolding fun_comp_def by auto

lemma comp_id_eq [simp]: "f : (x \<in> A) \<rightarrow> B x \<Longrightarrow> f \<circ> (\<lambda>x \<in> A. x) = f"
  unfolding fun_comp_def by auto

lemma id_comp_eq [simp]: "f : A \<rightarrow> B \<Longrightarrow> (\<lambda>x \<in> B. x) \<circ> f = f"
  unfolding fun_comp_def by auto

lemma comp_assoc [simp]:
  assumes "f : A \<rightarrow> B" "g : B \<rightarrow> C"
  shows "h \<circ> g \<circ> f = (h \<circ> g) \<circ> f"
  (*TOOD: slow proof*)
  unfolding fun_comp_def by auto

subsection \<open>Restriction\<close>

definition "restriction f A \<equiv> \<lambda>a \<in> dom f \<inter> A. f`a"

bundle isa_set_restriction_syntax begin notation restriction (infix "\<restriction>" 100) end
bundle no_isa_set_restriction_syntax begin no_notation restriction (infix "\<restriction>" 100) end
unbundle isa_set_restriction_syntax

lemma restriction_type [type]:
  "(\<restriction>) : ((x \<in> A) \<rightarrow> B x) \<Rightarrow> (A' : Set) \<Rightarrow> (x \<in> A \<inter> A') \<rightarrow> B x"
  unfolding restriction_def
  using lambda_type_dom_bin_inter_if_Dep_Function
  by (auto simp only: Dep_Function_dom_eq)

lemma Fun_restriction_subset [simp]: "f : Fun \<Longrightarrow> restriction f A \<subseteq> f"
  unfolding restriction_def by auto

lemma Fun_restriction_eq_collect:
  assumes "f : Fun"
  shows "f\<restriction>A = {p \<in> f | fst p \<in> A}" (is "?lhs = ?rhs")
proof (rule eqI)
  fix p assume "p \<in> ?rhs"
  then have "p \<in> f" "fst p \<in> A" by auto
  with Fun_fst_mem_dom_if_mem have "fst p \<in> dom f" by auto
  with assms obtain x y where [simp]: "p = \<langle>x, y\<rangle>" "y = f`x"
    by (auto elim!: Fun_memE)
  with assms \<open>fst p \<in> A\<close> \<open>fst p \<in> dom f\<close> show "p \<in> ?lhs"
    unfolding restriction_def by (auto intro!: lambda_pair_mem_if_mem)
next
  fix p assume "p \<in> ?lhs"
  with assms show "p \<in> ?rhs" unfolding restriction_def by auto
qed

lemma restriction_eval_eq [simp]: "a \<in> A \<Longrightarrow> A \<subseteq> dom f \<Longrightarrow> (f\<restriction>A)`a = f`a"
  unfolding restriction_def by auto

lemma dom_restriction_eq [simp]: "dom (f\<restriction>A) = dom f \<inter> A"
  unfolding restriction_def by auto

lemma restriction_type_Subset:
  "(\<restriction>) : ((x \<in> A) \<rightarrow> B x) \<Rightarrow> (A' : Subset A) \<Rightarrow> (x \<in> A') \<rightarrow> B x"
  by (intro Dep_fun_typeI,
    rewrite at "A'" in "(x \<in> A') \<rightarrow> _" in for (A')
      bin_inter_eq_right_if_subset[where ?A=A, symmetric])
    auto


subsection \<open>Gluing\<close>

definition "glue X = \<Union>X"

lemma glue_eval_eq:
  assumes "\<And>f y'. \<lbrakk>f \<in> F; \<langle>x, y'\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y' = y"
  and "f \<in> F"
  and "\<langle>x, y\<rangle> \<in> f"
  shows "(glue F)`x = y"
  unfolding eval_def glue_def by (rule the_equality) (auto intro: assms)

lemma glue_Dep_Functions_typeI:
  assumes all_fun: "\<And>f. f \<in> F \<Longrightarrow> f : (x \<in> dom f) \<rightarrow> B x"
  and all_agree: "\<And>f g x. \<lbrakk>f \<in> F; g \<in> F; x \<in> dom f; x \<in> dom g\<rbrakk> \<Longrightarrow> f`x = g`x"
  shows "glue F : (x \<in> (\<Union>f \<in> F. dom f)) \<rightarrow> B x"
proof (rule Dep_FunctionI)
  {
    fix x assume "x \<in> (\<Union>f \<in> F. dom f)"
    then obtain f where "f \<in> F" "x \<in> dom f" by auto
    moreover have "\<langle>x, f`x\<rangle> \<in> f"
      by (simp only:
        Dep_Function_pair_mem_iff_eval_eq[OF all_fun[OF \<open>f \<in> F\<close>] \<open>x \<in> dom f\<close>])
    ultimately have "\<exists>f y. f \<in> F \<and> \<langle>x, y\<rangle> \<in> f \<and> f`x = y" by auto
  }
  note ex_mem_F_pair_mem = this
  show "function (\<Union>f \<in> F. dom f) (glue F)" unfolding glue_def
  proof
   fix x y y' assume "x \<in> (\<Union>f \<in> F. dom f)" "\<langle>x, y\<rangle> \<in> \<Union>F" "\<langle>x, y'\<rangle> \<in> \<Union>F"
    then obtain f g where f_g_props: "\<langle>x, y\<rangle> \<in> f" "\<langle>x, y'\<rangle> \<in> g" "f \<in> F" "g \<in> F"
      by auto
    with all_fun have "y = f`x" by auto
    also with f_g_props have "... = g`x" by (intro all_agree) auto
    also with all_fun f_g_props have "... = y'" by auto
    finally show "y = y'" .
  next
    fix x assume "x \<in> (\<Union>f \<in> F. dom f)"
    from ex_mem_F_pair_mem[OF this] show "\<exists>y. \<langle>x, y\<rangle> \<in> \<Union>F" by auto
  qed
  fix x assume "x \<in> (\<Union>f \<in> F. dom f)"
  from ex_mem_F_pair_mem[OF this]
    obtain f y where "f \<in> F" "\<langle>x, y\<rangle> \<in> f" and "f`x = y" by auto
  then have "glue F`x = y"
  proof (intro glue_eval_eq)
    fix f' y' assume "f' \<in> F" "\<langle>x, y'\<rangle> \<in> f'"
    with all_fun have "y' = f'`x" by auto
    also with \<open>\<langle>x, y'\<rangle> \<in> f'\<close> have "... = f`x"
      using \<open>\<langle>x, y\<rangle> \<in> f\<close> by (intro all_agree) auto
    finally show "y' = y" using \<open>f`x = y\<close> by simp
  qed assumption
  moreover from \<open>f \<in> F\<close> have "y \<in> B x" by
    (intro Dep_Function_mem_codom_if_pair_mem[where ?B=B]) (auto dest: all_fun)
  ultimately show "glue F`x \<in> B x" unfolding glue_def by auto
qed (unfold glue_def, auto dest: all_fun)

lemma glue_Dep_Functions_eval_eq:
  assumes all_fun: "\<And>f. f \<in> F \<Longrightarrow> f : (x \<in> dom f) \<rightarrow> B x"
  and all_agree: "\<And>f'. \<lbrakk>f' \<in> F; x \<in> dom f'\<rbrakk> \<Longrightarrow> f'`x = f`x"
  and "f \<in> F"
  and "x \<in> dom f"
  shows "(glue F)`x = f`x"
proof (rule glue_eval_eq[OF _ \<open>f \<in> F\<close>])
 fix f' y' assume f'_props: "f' \<in> F" "\<langle>x, y'\<rangle> \<in> f'"
  then have "y' = f'`x"
    by (intro Dep_Fun_eval_eq_if_pair_mem[symmetric]) (auto dest: all_fun)
  also have "... = f`x" using f'_props by (intro all_agree) auto
  finally show "y' = f`x" .
next
  show "\<langle>x, f`x\<rangle> \<in> f"
    by (rule Dep_Function_pair_eval_mem_if_mem) (auto intro: assms)
qed

lemma glue_upair_Dep_Functions_typeI:
  assumes "f : (x \<in> A) \<rightarrow> B x" "g : (x \<in> A') \<rightarrow> B x"
  and "\<And>x. \<lbrakk>x \<in> A; x \<in> A'\<rbrakk> \<Longrightarrow> f`x = g`x"
  shows "glue {f, g} : (x \<in> A \<union> A') \<rightarrow> B x"
proof -
  have "(\<Union>f \<in> {f, g}. dom f) = (\<Union>f \<in> {f}. dom f) \<union> (\<Union>f \<in> {g}. dom f)"
    by (auto simp only: idx_union_bin_union_dom_eq_bin_union_idx_union)
  also have "... = dom f \<union> dom g" by auto
  also have "... = A \<union> A'" by simp
  finally have "A \<union> A' = (\<Union>f \<in> {f, g}. dom f)" by auto
  then show ?thesis using assms by (auto intro: glue_Dep_Functions_typeI)
qed

lemma glue_upair_Dep_Functions_eval_eq_left:
  assumes "f : (x \<in> A) \<rightarrow> B x" "g : (x \<in> A') \<rightarrow> B x"
  and "\<And>x. x \<in> A \<inter> A' \<Longrightarrow> f`x = g`x"
  and "x \<in> A"
  shows "(glue {f, g})`x = f`x"
  by (intro glue_Dep_Functions_eval_eq) (auto simp: assms)

lemma glue_upair_Dep_Functions_eval_eq_right:
  assumes "f : (x \<in> A) \<rightarrow> B x" "g : (x \<in> A') \<rightarrow> B x"
  and "\<And>x. x \<in> A \<inter> A' \<Longrightarrow> f`x = g`x"
  and  "x \<in> A'"
  shows "(glue {f, g})`x = g`x"
  by (subst cons_comm, rule glue_upair_Dep_Functions_eval_eq_left)
    (auto simp: assms)


subsection \<open>Universes\<close>

lemma univ_closed_dep_functions [intro!]:
  assumes "A \<in> univ U"
  and "\<And>x. x \<in> A \<Longrightarrow> B x \<in> univ U"
  shows "\<Prod>x \<in> A. (B x) \<in> univ U"
proof -
  let ?P = "powerset \<Sum>x \<in> A. (B x)"
  have "\<Prod>x \<in> A. (B x) \<subseteq> ?P" unfolding dep_functions_def by (fact collect_subset)
  moreover have "?P \<in> univ U" using assms by auto
  ultimately show ?thesis by (auto intro: mem_univ_trans)
qed


end
