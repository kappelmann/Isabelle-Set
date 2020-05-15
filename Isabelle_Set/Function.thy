chapter \<open>Functions\<close>

theory Function
imports BinRel

begin


section \<open>Function-like part of a set\<close>

text \<open>
The following expresses that a set S is function-like on A (it need not even be
relation-like elsewhere).
\<close>
definition "function_like A S \<equiv> \<forall>a \<in> A. \<exists>!y. \<langle>a, y\<rangle> \<in> S"

definition eval ("_`_" [999, 1000] 999) where "S`x \<equiv> THE y. \<langle>x, y\<rangle> \<in> S"

lemma function_likeI [intro]:
  assumes "\<And>a x y. \<lbrakk>a \<in> A; \<langle>a, x\<rangle> \<in> S; \<langle>a, y\<rangle> \<in> S\<rbrakk> \<Longrightarrow> x = y"
      and "\<And>a. a \<in> A \<Longrightarrow> \<exists>y. \<langle>a, y\<rangle> \<in> S"
  shows "function_like A S"
  unfolding function_like_def
  by (auto intro: assms)

lemma function_likeD: "function_like A S \<Longrightarrow> \<forall>a \<in> A. \<exists>!y. \<langle>a, y\<rangle> \<in> S"
  unfolding function_like_def by auto

lemma function_likeD1: \<comment> \<open>existence of image\<close>
  assumes "function_like A S" and "a \<in> A"
  obtains y where "\<langle>a, y\<rangle> \<in> S"
  using assms unfolding function_like_def by auto

lemma function_likeD2: \<comment> \<open>uniqueness of image\<close>
  "\<lbrakk>function_like A S; a \<in> A; \<langle>a, y\<rangle> \<in> S; \<langle>a, y'\<rangle> \<in> S\<rbrakk> \<Longrightarrow> y = y'"
  unfolding function_like_def by auto

lemma function_like_elem [elim]:
  "\<lbrakk>function_like A S; a \<in> A\<rbrakk> \<Longrightarrow> \<langle>a, S`a\<rangle> \<in> S"
  unfolding eval_def
  by (auto simp: function_like_def dest!: ballD intro: theI')

lemma function_like_eval:
  "\<lbrakk>function_like A S; a \<in> A; \<langle>a, y\<rangle> \<in> S\<rbrakk> \<Longrightarrow> S`a = y"
  unfolding function_like_def eval_def by auto

lemma function_like_empty: "function_like {} {}"
  unfolding function_like_def by auto


section \<open>Generic notion of a function\<close>

definition [typedef]: "Fun \<equiv> (\<lambda>f. function_like (dom f) f) \<sqdot> BinRel"

lemma
  FunI [derive]: "\<lbrakk>f : BinRel; function_like (dom f) f\<rbrakk> \<Longrightarrow> f: Fun" and
  FunD: "f: Fun \<Longrightarrow> function_like (dom f) f \<and> f : BinRel"
  unfolding Fun_def by auto

lemma FunE [elim]:
  "\<lbrakk>f : Fun; \<And>f. \<lbrakk>f : BinRel; function_like (dom f) f\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by (auto dest: FunD)

lemma Fun_uniq_val:
  assumes "f: Fun"
      and "\<langle>x, y\<rangle> \<in> f" "\<langle>x, y'\<rangle> \<in> f"
  shows "y = y'"
proof -
  from assms(1) have "function_like (dom f) f" by (auto dest: FunD)
  moreover from assms have "x \<in> dom f" by auto
  ultimately show ?thesis using assms(3) unfolding function_like_def by auto
qed

lemma Fun_comp [simp]:
  "\<lbrakk>f: Fun; \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> f`x = y"
  by (auto intro: function_like_eval dest!: FunD)

lemma Fun_elem_eq [simp]:
  "\<lbrakk>f: Fun; p \<in> f\<rbrakk> \<Longrightarrow> \<langle>fst p, snd p\<rangle> = p"
  by (auto dest: FunD)

lemma Fun_elem_rewrite [elim]:
  "\<lbrakk>f: Fun; p \<in> f\<rbrakk> \<Longrightarrow> \<langle>fst p, snd p\<rangle> \<in> f"
  by auto

lemma Fun_eval_fst [simp]:
  "\<lbrakk>f: Fun; p \<in> f\<rbrakk> \<Longrightarrow> f`(fst p) = snd p"
  by auto

lemma Fun_elemE:
  "\<lbrakk>f: Fun; p \<in> f; P p \<Longrightarrow> Q; P \<langle>fst p, snd p\<rangle>\<rbrakk> \<Longrightarrow> Q"
  by auto

lemma Fun_elemE':
  "\<lbrakk>f: Fun; p \<in> f; P p \<Longrightarrow> Q; P \<langle>fst p, f`(fst p)\<rangle>\<rbrakk> \<Longrightarrow> Q"
  by auto


section \<open>Function space\<close>

definition [typedef]: "DepFunction A B \<equiv> function_like A \<sqdot> Subset (\<Sum>x\<in> A. (B x))"

abbreviation "Function A B \<equiv> DepFunction A (\<lambda>_. B)"

text \<open>Set model of \<^term>\<open>DepFunction\<close>:\<close>

definition
  "piset A B \<equiv> {f \<in> powerset (\<Sum>x \<in> A. (B x)) | \<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f}"

syntax
  "_piset"  :: \<open>[pttrns, set, set] \<Rightarrow> set type\<close> ("(2\<Prod>_\<in> _./ _)" [0, 0, 100])
  "_piset2" :: \<open>[pttrns, set, set] \<Rightarrow> set type\<close>
translations
  "\<Prod>x xs\<in> A. B" \<rightharpoonup> "CONST piset A (\<lambda>x. _piset2 xs A B)"
  "_piset2 x A B" \<rightharpoonup> "\<Prod>x\<in> A. B"
  "\<Prod>x\<in> A. B" \<rightleftharpoons> "CONST piset A (\<lambda>x. B)"

text \<open>Syntax rules converting soft type notation to underlying set representation:\<close>
syntax
  "_telescope'" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<rightarrow>" 50)
translations
  "(x \<in> A) \<rightarrow> (y \<in> B) \<rightarrow> C" \<rightleftharpoons> "(x \<in> A) \<rightarrow> \<Prod>y\<in> B. C"
  "(x \<in> A) \<rightarrow> B \<rightarrow> C" \<rightleftharpoons> "(x \<in> A) \<rightarrow> \<Prod>_\<in> B. C"
  "A \<rightarrow> (y \<in> B) \<rightarrow> C" \<rightleftharpoons> "A \<rightarrow> \<Prod>y\<in> B. C"
  "A \<rightarrow> B \<rightarrow> C" \<rightleftharpoons> "A \<rightarrow> \<Prod>_\<in> B. C"
  "\<Prod>x\<in> A. ((y \<in> B) \<rightarrow> C)" \<rightharpoonup> "\<Prod>x\<in> A. \<Prod>y\<in> B. C"
  "\<Prod>x\<in> A. (B \<rightarrow> C)" \<rightharpoonup> "\<Prod>x\<in> A. \<Prod>_\<in> B. C"
  "(x \<in> A) \<rightarrow> B" \<rightleftharpoons> "CONST DepFunction A (\<lambda>x. B)"
  "A \<rightarrow> B" \<rightleftharpoons> "CONST Function A B"

soft_type_translation "f \<in> \<Prod>x\<in> A. (B x)" \<rightleftharpoons> "f: (x \<in> A) \<rightarrow> B x"
  unfolding piset_def by unfold_types (auto simp: function_like_def)

corollary piset_iff_DepFunction [iff]: "f \<in> \<Prod>x\<in> A. (B x) \<longleftrightarrow> f: (x \<in> A) \<rightarrow> B x" by auto

(*Soft type translations now get all translations that unify; no longer
  restricted to just one.*)
ML \<open>Derivation.get_translations @{context} @{term "f \<in> \<Prod>x\<in> A. (B x)"}\<close>


section \<open>Properties of generic functions\<close>

lemma
  DepFunction_imp_function_like [derive]:
    "f: (x \<in> A) \<rightarrow> B x \<Longrightarrow> function_like A f" and
  DepFunction_imp_Subset [derive]:
    "f: (x \<in> A) \<rightarrow> B x \<Longrightarrow> f: Subset (\<Sum>x\<in> A. (B x))"
  by unfold_types

lemma DepFunction_imp_Fun [derive]:
  "f: (x \<in> A) \<rightarrow> B x \<Longrightarrow> f: Fun"
  apply unfold_types
  unfolding function_like_def by auto force

lemma DepFunction_imp_Function [derive]:
  "f: (x \<in> A) \<rightarrow> B x \<Longrightarrow> f: A \<rightarrow> (\<Union>x\<in> A. B x)"
  by unfold_types auto

lemma generic_DepFunctionI:
  assumes "function_like A f" "f: BinRel"
      and "dom f = A"
      and "\<And>u. u \<in> f \<Longrightarrow> snd u \<in> B (fst u)"
  shows "f: (x \<in> A) \<rightarrow> B x"
  apply unfold_types
  using assms by (auto intro: pairsetI2 elim: BinRel_elem_eq[symmetric])

lemma generic_FunctionI [derive]:
  "f: function_like A \<sqdot> Relation A B \<Longrightarrow> f: A \<rightarrow> B"
  by unfold_types

lemma DepFunction_elem [elim]:
  assumes "f: (x \<in> A) \<rightarrow> B x" and "x \<in> A"
  shows "\<langle>x, f`x\<rangle> \<in> f"
proof -
  from assms(1) have "function_like A f" by auto
  with assms(2) show ?thesis by auto
qed

lemma DepFunction_elem_proj1 [elim]:
  "\<lbrakk>f: (x \<in> A) \<rightarrow> B x; \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> x \<in> A"
  by unfold_types auto

(*EXAMPLE
  for type derivation improvement: integration with elim-resolution*)
lemma example_Depfunction_elem_fst [elim]:
  "\<lbrakk>f: (x \<in> A) \<rightarrow> B x; p \<in> f\<rbrakk> \<Longrightarrow> fst p \<in> A"
  apply (rule DepFunction_elem_proj1)
  apply (auto dest: DepFunction_imp_Fun)
    (* We want to avoid having to explicitly give DepFunction_imp_Fun *)
  done

lemma Depfunction_elem_fst [elim]:
  "\<lbrakk>f: (x \<in> A) \<rightarrow> B x; p \<in> f\<rbrakk> \<Longrightarrow> fst p \<in> A"
  by (rule DepFunction_elem_proj1) (auto intro: Fun_elem_rewrite)

lemma DepFunction_elem_proj2:
  "\<lbrakk>f: (x \<in> A) \<rightarrow> B x; \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y \<in> B x"
  by unfold_types auto

lemma DepFunction_elem_snd:
  "\<lbrakk>f: (x \<in> A) \<rightarrow> B x; p \<in> f\<rbrakk> \<Longrightarrow> snd p \<in> B (fst p)"
  by (rule DepFunction_elem_proj2) (auto intro: Fun_elem_rewrite)

lemma DepFunction_as_relation:
  "f: (x \<in> A) \<rightarrow> B x \<Longrightarrow> f \<subseteq> A \<times> (\<Union>x \<in> A. B x)"
  by unfold_types auto

lemma Function_as_relation:
  "f: A \<rightarrow> B \<Longrightarrow> f \<subseteq> A \<times> B"
  by unfold_types auto

lemma DepFunction_dom [simp]:
  "f: (x \<in> A) \<rightarrow> B x \<Longrightarrow> dom f = A"
  by unfold_types (force intro: equalityI simp: dom_def function_like_def)

lemma DepFunction_graph [simp]:
  assumes "f: (x \<in> A) \<rightarrow> B x"
  shows "{\<langle>x, f`x\<rangle> | x \<in> A} = f"
  apply (rule equalityI) using assms by auto

lemma DepFunction_empty_iff [iff]: "f: (x \<in> {}) \<rightarrow> (B x) \<longleftrightarrow> f = {}"
  by unfold_types auto

lemma DepFunction_subsetI:
  assumes
    "f: (x \<in> A) \<rightarrow> B x"
    "g: (x \<in> A') \<rightarrow> B' x"
    "A \<subseteq> A'"
    "\<And>x. x \<in> A \<Longrightarrow> f`x = g`x"
  shows "f \<subseteq> g"
proof (rule subsetI)
  fix p assume "p \<in> f"
  hence 1:"p = \<langle>fst p, f`(fst p)\<rangle>" by auto
  hence "fst p \<in> A" using assms(1) by auto
  hence 2: "f`(fst p) = g`(fst p)" using assms(4) by blast

  have "fst p \<in> A'" using assms(3) by auto
  hence "\<langle>fst p, g`(fst p)\<rangle> \<in> g" using assms(2) by fast
  then show "p \<in> g" by (rewrite 1, rewrite 2)
qed

lemma DepFunction_eval_eqI:
  assumes
    "f: (x \<in> A) \<rightarrow> B x"
    "g: (x \<in> A') \<rightarrow> B' x"
    "f \<subseteq> g"
    "x \<in> A \<inter> A'"
  shows "f`x = g`x"
proof -
  have "\<langle>x, f`x\<rangle> \<in> g" and "\<langle>x, g`x\<rangle> \<in> g" using assms by auto
  thus ?thesis by auto
qed

lemma function_domain_iff [iff]:
  "\<exists>A. f: (x \<in> A) \<rightarrow> B x \<longleftrightarrow> f: (x \<in> dom f) \<rightarrow> B x"
  by auto

lemma empty_function [type]: "{}: {} \<rightarrow> X" by auto

lemma singleton_function [intro]: "y \<in> B \<Longrightarrow> {\<langle>x, y\<rangle>}: {x} \<rightarrow> B"
  by unfold_types auto

lemma function_singletons [simp]: "f: {a} \<rightarrow> {b} \<Longrightarrow> f = {\<langle>a, b\<rangle>}"
  by unfold_types (auto simp: function_like_def)

lemma cons_FunctionI:
  "\<lbrakk>f: A \<rightarrow> B; x \<notin> A\<rbrakk> \<Longrightarrow> cons \<langle>x, y\<rangle> f: A \<union> {x} \<rightarrow> B \<union> {y}"
  by unfold_types (auto simp: function_like_def)

lemma cons_FunctionI':
  "\<lbrakk>f: A \<rightarrow> B; x \<notin> A; y \<in> B\<rbrakk> \<Longrightarrow> cons \<langle>x, y\<rangle> f: A \<union> {x} \<rightarrow> B"
  apply (drule cons_FunctionI, assumption)
  apply (subst bin_union_singleton_absorb[symmetric, where ?t=B])
  by (auto simp: bin_union_ac)

lemma bin_union_FunctionI:
  "\<lbrakk>f: A \<rightarrow> B; x \<notin> A\<rbrakk> \<Longrightarrow> {\<langle>x, y\<rangle>} \<union> f: A \<union> {x} \<rightarrow> B \<union> {y}"
  by unfold_types (auto simp: function_like_def)


section \<open>Lambda abstraction\<close>

definition lambda :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "lambda A b \<equiv> {\<langle>x, b x\<rangle> | x \<in> A}"

syntax
  "_lam"  :: "[pttrns, set, set] \<Rightarrow> set" ("(2\<lambda>_\<in> _./ _)" 60)
  "_lam2" :: \<open>[pttrns, set, set] \<Rightarrow> set\<close>
translations
  "\<lambda>x xs\<in> A. b" \<rightharpoonup> "CONST lambda A (\<lambda>x. _lam2 xs A b)"
  "_lam2 x A b" \<rightharpoonup> "\<lambda>x\<in> A. b"
  "\<lambda>x\<in> A. b" \<rightleftharpoons> "CONST lambda A (\<lambda>x. b)"

lemma lambda_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> b x = b' x\<rbrakk> \<Longrightarrow> (\<lambda>x\<in> A. b x) = \<lambda>x\<in> A'. b' x"
  by (simp only: lambda_def cong add: repl_cong)

lemma beta [simp]: "a \<in> A \<Longrightarrow> (\<lambda>x\<in> A. b x)`a = b a"
  by (auto simp: lambda_def eval_def)

lemma beta_split [simp]:
  assumes "a \<in> A" "b \<in> B"
  shows "(\<lambda>p \<in> A \<times> B. (\<lambda>\<langle>x,y\<rangle>. P x y) p)`\<langle>a, b\<rangle> = P a b"
  using assms by auto

\<comment> \<open>Does not work as simp rule\<close>
lemma lambda_times_split: "(\<lambda>x\<in> A \<times> B. f x) = (\<lambda>\<langle>a, b\<rangle> \<in> A \<times> B. f \<langle>a, b\<rangle>)"
  by (rule lambda_cong) auto

lemma lambdaI [intro]: "a \<in> A \<Longrightarrow> \<langle>a, b a\<rangle> \<in> \<lambda>x\<in> A. b x"
  unfolding lambda_def by auto

lemma lambdaE [elim]: "\<lbrakk>p \<in> \<lambda>x\<in> A. b x; \<And>x. \<lbrakk>x \<in> A; p = \<langle>x, b x\<rangle>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: lambda_def, blast)

lemma lambdaD [dest]: "\<lbrakk>\<langle>a, c\<rangle> \<in> \<lambda>x\<in> A. b x\<rbrakk> \<Longrightarrow> c = b a"
  by auto

lemma lambda_dom [simp]: "dom (\<lambda>x\<in> A. b x) = A"
  by (auto simp: lambda_def)

lemma lambda_eqE: "\<lbrakk>(\<lambda>x\<in> A. f x) = \<lambda>x\<in> A. g x; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
  by (auto elim: equalityE)


section \<open>Type theoretic rules\<close>

lemma DepFunctionI [backward_derive]:
  "(\<And>x. x \<in> A \<Longrightarrow> b x \<in> B x) \<Longrightarrow> (\<lambda>x\<in> A. b x): (x \<in> A) \<rightarrow> B x"
  unfolding lambda_def by unfold_types auto

corollary DepFunctionI':
  "(\<And>x. x \<in> A \<Longrightarrow> b`x \<in> B x) \<Longrightarrow> (\<lambda>x\<in> A. b`x): (x \<in> A) \<rightarrow> B x" by auto

lemma split_DepFunctionI [intro]:
  assumes "\<And>x y. \<lbrakk>x \<in> X; y \<in> Y\<rbrakk> \<Longrightarrow> b x y \<in> B \<langle>x, y\<rangle>"
  shows "(\<lambda>\<langle>x, y\<rangle>\<in> X \<times> Y. b x y): (p \<in> X \<times> Y) \<rightarrow> B p"
  using assms by auto

lemma DepFunction_cong:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> f: (x \<in> A) \<rightarrow> B x \<longleftrightarrow> f: (x \<in> A') \<rightarrow> B' x"
  by unfold_types (simp cong: pairset_cong)

lemma lambda_type [type]:
  "lambda: (A: Set) \<Rightarrow> ((x: Element A) \<Rightarrow> Element (B x)) \<Rightarrow> (x \<in> A) \<rightarrow> B x"
  by unfold_types auto
  
lemma lambda_function_typeI' [derive]:
  assumes "f: (x: Element A) \<Rightarrow> Element (B x)"
  shows "(\<lambda>x\<in> A. f x): (x \<in> A) \<rightarrow> B x"
  by discharge_types

lemma lambda_function_typeI [backward_derive]:
  assumes "\<And>x. x: Element A \<Longrightarrow> f x: Element (B x)"
  shows "(\<lambda>x\<in> A. f x): (x \<in> A) \<rightarrow> B x"
  by (rule lambda_function_typeI') auto

lemma DepFunctionE [elim]:
  assumes "f: (x \<in> A) \<rightarrow> B x" and "a \<in> A"
  shows "f`a \<in> B a"
  using DepFunction_elem_proj2 DepFunction_elem assms by auto

lemma id_type [type]: "(\<lambda>x \<in> A. x) : A \<rightarrow> A" by unfold_types auto

lemma eval_type [type]:
  "eval: ((x \<in> A) \<rightarrow> B x) \<Rightarrow> (x: Element A) \<Rightarrow> Element (B x)"
  \<comment> \<open>
    Note how type derivation fails to solve this immediately because of the
    `Element` coercion.
  \<close>
  by discharge_types (rule ElementI, auto)

lemma curry_type [derive]:
  "\<lbrakk>f: (x \<in> A) \<rightarrow> (y \<in> B x) \<rightarrow> C x y; a: Element A\<rbrakk> \<Longrightarrow> f`a: (y \<in> B a) \<rightarrow> C a y"
  by (auto simp only: piset_iff_DepFunction[symmetric])

lemma curry_type' [derive]:
  "\<lbrakk>f: (x \<in> A) \<rightarrow> (y \<in> B x) \<rightarrow> C x y; a: Element A; b: Element (B a)\<rbrakk>
    \<Longrightarrow> f`a`b: Element (C a b)"
  by auto

lemma id_function_type [type]: "(\<lambda>x\<in> A. x): A \<rightarrow> A" by discharge_types

lemma funext:
  assumes
    "f: (x \<in> A) \<rightarrow> B x"
    "g: (x \<in> A) \<rightarrow> C x"
    "\<And>x. x \<in> A \<Longrightarrow> f `x = g `x"
  shows
    "f = g"
  apply (rule extensionality)
  using assms DepFunction_subsetI by unfold_types

lemma lambda_ext:
  assumes "g: (x \<in> A) \<rightarrow> B x"
  and "\<And>a. a \<in> A \<Longrightarrow> f a = g`a"
  shows "(\<lambda>a \<in> A. f a) = g"
  unfolding lambda_def
  by (rewrite at "{\<langle>x, f x\<rangle> | x \<in> A}" to "{\<langle>x, g`x\<rangle> | x \<in> A}" repl_cong)
     (simp_all add: assms)

lemma eta: "f: (x\<in> A) \<rightarrow> B x \<Longrightarrow> (\<lambda>x\<in> A. f`x) = f"
  by (rule funext) auto

lemma function_refine:
  assumes
    "f: (x\<in> A) \<rightarrow> B x"
    "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x"
  shows
    "f: (x\<in> A) \<rightarrow> C x"
proof -
  have "(\<lambda>x\<in> A. f`x): (x\<in> A) \<rightarrow> C x"
    using assms by (auto intro: ElementI)
  moreover have "(\<lambda>x\<in> A. f`x) = f"
    using assms by (simp add: eta)
  ultimately show ?thesis by auto
qed

corollary function_enlarge_range:
  assumes
    "f: (x\<in> A) \<rightarrow> B x"
    "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x"
  shows
    "f: (x\<in> A) \<rightarrow> C x"
proof -
  from assms(1) have "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> B x" by auto
  with assms(2) have "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x" by auto
  hence "(\<lambda>x\<in> A. f`x): (x\<in> A) \<rightarrow> C x" by auto
  thus ?thesis using assms(1) eta by auto
qed

corollary function_enlarge_range': "\<lbrakk>f: A \<rightarrow> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> f: A \<rightarrow> C"
  by (rule function_enlarge_range)

(*Larry: Such functions arise in non-standard datatypes, ZF/ex/Ntree for
  instance.*)
lemma DepFunction_collectI:
    "f: (x \<in> A) \<rightarrow> B x \<and> (\<forall>x \<in> A. P x (f`x)) \<Longrightarrow> f: (x \<in> A) \<rightarrow> {y \<in> B x | P x y}"
  and DepFunction_collectD:
    "f: (x \<in> A) \<rightarrow> {y \<in> B x | P x y} \<Longrightarrow> f: (x \<in> A) \<rightarrow> B x \<and> (\<forall>x \<in> A. P x (f`x))"
  by (auto intro: function_refine dest: DepFunctionE)




section \<open>Injectivity and surjectivity\<close>

definition "injective f \<equiv> \<forall>x \<in> dom f. \<forall>x' \<in> dom f. f`x = f`x' \<longrightarrow> x = x'"

text \<open>Surjectivity has to be with respect to an explicit codomain.\<close>

definition "surjective B f \<equiv> \<forall>y \<in> B. \<exists>x. \<langle>x, y\<rangle> \<in> f"

lemma surjectiveI:
  assumes
    "f: A \<rightarrow> B"
    "(\<And>y. y \<in> B \<Longrightarrow> \<exists>x \<in> A. f`x = y)"
  shows "surjective B f"
unfolding surjective_def
proof
  fix y assume "y \<in> B"
  then obtain x where "x \<in> A" and "y = f`x" using assms by auto
  thus "\<exists>x. \<langle>x, y\<rangle> \<in> f" using assms by (auto intro: DepFunction_elem)
qed


section \<open>Evaluation of function graphs\<close>

lemma eval_cons_head [simp]:
  "x \<notin> dom A \<Longrightarrow> (cons \<langle>x, y\<rangle> A)`x = y"
  unfolding dom_def eval_def by (rule theI2) auto

lemma eval_cons_tail [simp]:
  "x \<noteq> y \<Longrightarrow> (cons \<langle>y, z\<rangle> A)`x = A`x"
  unfolding eval_def by auto

lemma eval_bin_union1 [simp]:
  "x \<notin> dom B \<Longrightarrow> (A \<union> B)`x = A`x"
  unfolding eval_def by (auto elim: not_in_domE)

lemma eval_bin_union2 [simp]:
  "x \<notin> dom A \<Longrightarrow> (A \<union> B)`x = B `x"
  unfolding eval_def by (auto elim: not_in_domE)


section \<open>More function extensionality\<close>

lemma funext_iff:
  "\<lbrakk>f: (x \<in> A) \<rightarrow> B x; g: (x \<in> A) \<rightarrow> C x\<rbrakk> \<Longrightarrow> (\<forall>a \<in> A. f`a = g`a) \<longleftrightarrow> f = g"
  by (auto intro: funext)

(*Larry: Theorem by Mark Staples, proof by LCP.*)
lemma function_dom_imp_subset_iff_eq:
  "\<lbrakk>f: (x \<in> A) \<rightarrow> B x; g: (x \<in> A) \<rightarrow> C x\<rbrakk> \<Longrightarrow> f \<subseteq> g \<longleftrightarrow> f = g"
  by (blast
    dest: DepFunction_elem DepFunction_imp_Fun
    intro: funext Fun_comp[symmetric])

(*Every element of A \<rightarrow> B may be expressed as a lambda abstraction*)
lemma function_lambdaE:
  assumes
    "f: (x \<in> A) \<rightarrow> B x" and
    "\<And>b. \<lbrakk>\<forall>x \<in> A. b x \<in> B x; f = (\<lambda>x\<in> A. b x)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  by (rule assms(2)[of "eval f"]) (auto simp: assms(1) eta)

text \<open>Extend a function's domain by mapping new elements to the empty set.\<close>

definition triv_ext :: "set \<Rightarrow> set \<Rightarrow> set"
  where "triv_ext A f \<equiv> f \<union> (\<lambda>x\<in> (A \<setminus> dom f). {})"

lemma triv_ext_dom [simp]: "dom (triv_ext A f) = dom f \<union> A"
  unfolding triv_ext_def by (auto simp: bin_union_dom diff_partition')


section \<open>Composition\<close>

definition fun_comp :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> (infixr "\<circ>" 80)
  where "g \<circ> f = \<lambda>x\<in> dom f. g`(f`x)"

lemma fun_comp_type [type]:
  "(\<circ>): ((x \<in> B) \<rightarrow> C x) \<Rightarrow> (f: A \<rightarrow> B) \<Rightarrow> (x \<in> A) \<rightarrow> C (f`x)"
  unfolding fun_comp_def by auto

lemma compose_functions:
  assumes "f: A \<rightarrow> B" and "g: (x \<in> B) \<rightarrow> C x"
  shows "g \<circ> f: (x \<in> A) \<rightarrow> C (f`x)"
  by auto

lemma compose_lambdas:
  "f : Element A \<Rightarrow> Element B \<Longrightarrow> (\<lambda>y \<in> B. g y) \<circ> (\<lambda>x \<in> A. f x) = \<lambda>x \<in> A. g (f x)"
  by (auto simp: fun_comp_def)

lemma compose_idr [simp]: "f: (x \<in> A) \<rightarrow> B x \<Longrightarrow> f \<circ> (\<lambda>x\<in> A. x) = f"
  unfolding fun_comp_def by (auto simp: eta)

lemma compose_idl [simp]: "f: A \<rightarrow> B \<Longrightarrow> (\<lambda>x\<in> B. x) \<circ> f = f"
  unfolding fun_comp_def by (auto simp: eta)

lemma compose_assoc [simp]:
  assumes "f: A \<rightarrow> B" "g: B \<rightarrow> C"
  shows "h \<circ> g \<circ> f = (h \<circ> g) \<circ> f"
  unfolding fun_comp_def by auto

section \<open>Restriction\<close>

definition restriction :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> (infix "\<restriction>" 100)
  where "f \<restriction> A = \<lambda>a\<in> A \<inter> dom f. f`a" (* {p \<in> f | fst p \<in> A}" *)

lemma restriction_type [type]:
  "(\<restriction>): ((x \<in> A) \<rightarrow> B x) \<Rightarrow> (A': Subset A) \<Rightarrow> (x \<in> A') \<rightarrow> B x"
  unfolding restriction_def
  by discharge_types (auto
      intro!: generic_DepFunctionI
      dest!: SubsetD
      simp: function_like_def bin_inter_subset_right_absorb)

lemma eval_restriction [simp]: "A \<subseteq> dom f \<Longrightarrow> a \<in> A \<Longrightarrow> (f \<restriction> A)`a = f`a"
  unfolding restriction_def eval_def lambda_def by auto

lemma restriction_dom: "dom (f \<restriction> A) = dom f \<inter> A"
  unfolding restriction_def by (auto intro: equalityI)

lemma restriction_function:
  "f: (x \<in> A) \<rightarrow> B x \<Longrightarrow> f \<restriction> A': (x \<in> A \<inter> A') \<rightarrow> B x"
  unfolding restriction_def by auto

lemma restriction_function_subset:
  "\<lbrakk>f: (x \<in> A) \<rightarrow> B x; A' \<subseteq> A\<rbrakk> \<Longrightarrow> f \<restriction> A': (x \<in> A') \<rightarrow> B x"
  by (rewrite at A' in "_ \<rightarrow> _" bin_inter_subset_right_absorb[symmetric])
     (auto intro: restriction_function)


section \<open>Gluing\<close>

definition "glue X = \<Union>X"

lemma glueI:
  assumes "\<And>f. f \<in> X \<Longrightarrow> f: (x \<in> dom f) \<rightarrow> B x"
      and "\<And>f g x. \<lbrakk>f \<in> X; g \<in> X; x \<in> dom f; x \<in> dom g\<rbrakk> \<Longrightarrow> f`x = g`x"
  shows "glue X: (x \<in> (\<Union>f\<in> X. dom f)) \<rightarrow> B x"
proof (rule generic_DepFunctionI)
  show "function_like (\<Union>f\<in> X. dom f) (glue X)"
  unfolding glue_def function_like_def
  proof (clarify, rule ex1I, fast dest: assms(1))
    fix f a y assume asm:
      "f \<in> X" "a \<in> dom f" and "\<langle>a, y\<rangle> \<in> \<Union>X"
    obtain g where
      "g \<in> X" "a \<in> dom g" and "\<langle>a, y\<rangle> \<in> g" "g: (x \<in> dom g) \<rightarrow> B x"
      using assms(1) \<open>\<langle>a, y\<rangle> \<in> \<Union>X\<close> by fast
    have "y = g`a"
      using \<open>g: (x \<in> dom g) \<rightarrow> B x\<close> \<open>\<langle>a, y\<rangle> \<in> g\<close>
      by (intro Fun_comp[symmetric]) discharge_types
    also have "g`a = f`a"
      using assms(2) \<open>f \<in> X\<close> \<open>g \<in> X\<close> \<open>a \<in> dom f\<close> \<open>a \<in> dom g\<close> by fast
    finally show "y = f`a" .
  qed
  show "glue X: BinRel"
    by (rule BinRelI) (auto simp: glue_def dest: assms(1))
  show "dom (glue X) = (\<Union>f\<in> X. dom f)"
    using assms by (auto intro: equalityI simp: glue_def dom_def)
  show "\<And>f. f \<in> glue X \<Longrightarrow> snd f \<in> B (fst f)"
    by (auto simp: glue_def intro: DepFunction_elem_snd assms(1))
qed

lemma eval_glue:
  assumes "\<And>f. f \<in> X \<Longrightarrow> f: (x \<in> dom f) \<rightarrow> B x"
      and "\<And>f g x. \<lbrakk>f \<in> X; g \<in> X; x \<in> dom f; x \<in> dom g\<rbrakk> \<Longrightarrow> f`x = g`x"
      and "f \<in> X"
      and "a \<in> dom f"
  shows "(glue X)`a = f`a"
proof (rule Fun_comp)
  show "glue X: Fun" by (rule DepFunction_imp_Fun) (auto intro: glueI assms)
  show "\<langle>a, f`a\<rangle> \<in> glue X" unfolding glue_def using assms by fast
qed

lemma glue_pairI:
  assumes "f: (x \<in> A) \<rightarrow> B x" "g: (x \<in> A') \<rightarrow> B x"
  and "\<And>a. \<lbrakk>a \<in> A; a \<in> A'\<rbrakk> \<Longrightarrow> f`a = g`a"
  shows "glue {f, g}: (x \<in> A \<union> A') \<rightarrow> B x" (is "glue ?X: (x \<in> ?D) \<rightarrow> B x")
proof -
  have *: "?D = (\<Union>f \<in> ?X. dom f)" using repl_cons bin_union_def by auto
  show ?thesis by (auto simp: * assms intro: glueI)
qed

lemma eval_glue_bin:
  assumes
    "f: (x \<in> A) \<rightarrow> B x"
    "g: (x \<in> A') \<rightarrow> B x"
    "\<And>a. a \<in> A' \<Longrightarrow> f`a = g`a"
    "a \<in> A"
  shows "(glue {f, g})`a = f`a"
  by (rule eval_glue) (auto simp: assms)

lemma eval_glue_bin':
  assumes
    "f: (x \<in> A) \<rightarrow> B x"
    "g: (x \<in> A') \<rightarrow> B x"
    "\<And>a. a \<in> A \<Longrightarrow> f`a = g`a"
    "a \<in> A'"
  shows "(glue {f, g})`a = g`a"
  by (rule eval_glue) (auto simp: assms)


section \<open>Universes\<close>

lemma univ_piset_closed [intro]:
  assumes
    "A \<in> univ U"
    "\<And>x. x \<in> A \<Longrightarrow> B x \<in> univ U"
  shows
    "\<Prod>x\<in> A. (B x) \<in> univ U"
proof -
  let ?P = "powerset \<Sum>x\<in> A. (B x)"
  have "\<Prod>x\<in> A. (B x) \<subseteq> ?P" unfolding piset_def by (fact collect_subset)
  moreover have "?P \<in> univ U" using assms by auto
  ultimately show ?thesis by (auto intro: univ_transitive)
qed


end
