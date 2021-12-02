chapter \<open>Functions\<close>

theory Functions_Old
imports Relations

begin

text \<open>
  Functions are identified with their graphs. Function sets are formulated
  dependently by default.
\<close>

definition Function :: "[set, set \<Rightarrow> set] \<Rightarrow> set"
  where "Function A B \<equiv> {f \<in> powerset (\<Sum>x \<in> A. (B x)) | \<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f}"

syntax
  "_Function"  :: "[pttrns, set, set] \<Rightarrow> set type" ("(2\<Prod>_\<in> _./ _)" [0, 0, 100])
  "_Function2" :: \<open>[pttrns, set, set] \<Rightarrow> set type\<close>
translations
  "\<Prod>x xs\<in> A. B" \<rightharpoonup> "CONST Function A (\<lambda>x. _Function2 xs A B)"
  "_Function2 x A B" \<rightharpoonup> "\<Prod>x\<in> A. B"
  "\<Prod>x\<in> A. B" \<rightleftharpoons> "CONST Function A (\<lambda>x. B)"

abbreviation "function" :: "[set, set] \<Rightarrow> set" (infixr "\<rightarrow>" 60)
  where "A \<rightarrow> B \<equiv> \<Prod>x\<in> A. B"


section \<open>Lambda abstraction\<close>

text \<open>Construct set-theoretic functions from HOL functions.\<close>

definition lambda :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "lambda A b \<equiv> {\<langle>x, b x\<rangle> | x \<in> A}"

syntax
  "_lam"  :: "[pttrns, set, set] \<Rightarrow> set" ("(2\<lambda>_\<in> _./ _)" 60)
  "_lam2" :: \<open>[pttrns, set, set] \<Rightarrow> set\<close>
translations
  "\<lambda>x xs\<in> A. b" \<rightharpoonup> "CONST lambda A (\<lambda>x. _lam2 xs A b)"
  "_lam2 x A b" \<rightharpoonup> "\<lambda>x\<in> A. b"
  "\<lambda>x\<in> A. b" \<rightleftharpoons> "CONST lambda A (\<lambda>x. b)"

lemma lambdaI [intro]: "a \<in> A \<Longrightarrow> \<langle>a, b a\<rangle> \<in> \<lambda>x\<in> A. b x"
  unfolding lambda_def by auto

lemma lambdaE [elim]: "\<lbrakk>p \<in> \<lambda>x\<in> A. b x; \<And>x. \<lbrakk>x \<in> A; p = \<langle>x, b x\<rangle>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: lambda_def, blast)

lemma lambdaD [dest]: "\<lbrakk>\<langle>a, c\<rangle> \<in> \<lambda>x\<in> A. b x\<rbrakk> \<Longrightarrow> c = b a"
  by auto

lemma lambda_dom [simp]: "dom (\<lambda>x\<in> A. b x) = A"
  by (auto simp: lambda_def)

lemma lambda_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> b x = b' x\<rbrakk> \<Longrightarrow> (\<lambda>x\<in> A. b x) = \<lambda>x\<in> A'. b' x"
  by (simp only: lambda_def cong add: repl_cong)

lemma lambda_eqE: "\<lbrakk>(\<lambda>x\<in> A. f x) = \<lambda>x\<in> A. g x; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
  by (auto elim: equalityE)

(*Does not work as simp rule*)
lemma lambda_times_split: "(\<lambda>x\<in> A \<times> B. f x) = (\<lambda>\<langle>a, b\<rangle> \<in> A \<times> B. f \<langle>a, b\<rangle>)"
  by (rule lambda_cong) auto


section \<open>Function application and \<beta>-reduction\<close>

definition "apply" :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> ("_ `_" [999, 1000] 999)
  where "f `x = (THE y. \<langle>x, y\<rangle> \<in> f)"

text \<open>
  Math-style function syntax \<open>f\<^bold>(x\<^bold>)\<close> (bolded parentheses). Import
  \<open>Function_Math_Syntax\<close> to also apply it to printing behavior.
\<close>

syntax
  "_math_appl"  :: \<open>set \<Rightarrow> args \<Rightarrow> set\<close> ("_\<^bold>'(_\<^bold>')" [999, 0])
translations
  "F\<^bold>(x, xs\<^bold>)" \<rightleftharpoons> "(F `x)\<^bold>(xs\<^bold>)"
  "F\<^bold>(x\<^bold>)" \<rightharpoonup> "F `x"

lemma beta [simp]: "a \<in> A \<Longrightarrow> (\<lambda>x\<in> A. b x) `a = b a"
  by (auto simp: lambda_def apply_def)

lemma beta_split [simp]:
  assumes "a \<in> A" "b \<in> B"
  shows "(\<lambda>p \<in> A \<times> B. (\<lambda>\<langle>x,y\<rangle>. P x y) p) `\<langle>a, b\<rangle> = P a b"
  using assms by auto


section \<open>Set-theoretic rules\<close>

lemma function_elem:
  assumes "f \<in> \<Prod>x\<in> A. (B x)" and "x \<in> A"
  shows "\<langle>x, f `x\<rangle> \<in> f"
proof -
  have ex1: "\<exists>!y. \<langle>x, y\<rangle> \<in> f" using assms Function_def by auto
  then obtain y where elem: "\<langle>x, y\<rangle> \<in> f" by auto
  with ex1 have "f `x = y" using apply_def by auto
  with elem show "\<langle>x, f `x\<rangle> \<in> f" by simp
qed

lemma function_uniq_val:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); \<langle>x, y\<rangle> \<in> f; \<langle>x, y'\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y = y'"
  unfolding Function_def by auto

lemma function_fiber: "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y \<in> B x"
  unfolding Function_def by auto

lemma function_relation [elim]:
  "f \<in> \<Prod>x\<in> A. (B x) \<Longrightarrow> f \<subseteq> A \<times> (\<Union>x \<in> A. B x)"
  unfolding Function_def by auto

lemma function_relation' [elim]:
  "f \<in> A \<rightarrow> B \<Longrightarrow> f \<subseteq> A \<times> B"
  using function_relation by auto

lemma function_dom [elim, simp]: "f \<in> \<Prod>x\<in> A. (B x) \<Longrightarrow> dom f = A"
  unfolding Function_def dom_def
  by (force intro: extensionality)

(*For rewriting*)
lemma function_dom_dom [simp]: "f \<in> \<Prod>x\<in> A. (B x) \<Longrightarrow> f \<in> \<Prod>x\<in> dom f. (B x)"
  by auto

lemma function_elem_dom: "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> x \<in> A"
  using domI function_dom by fastforce

lemma function_apply [simp]: "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> f `x = y"
  using domI function_dom function_elem function_uniq_val by fast

lemma function_elem_pair:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> p = \<langle>fst p, snd p\<rangle>"
  by (elim Pair_subset_elem) (rule function_relation)

lemma function_elem_fst:
  assumes "f \<in> \<Prod>x\<in> A. (B x)" "p \<in> f"
  shows "fst p \<in> A"
proof (rule function_elem_dom, fact)
  from assms have "p = \<langle>fst p, snd p\<rangle>" by (rule function_elem_pair)
  with assms show "\<langle>fst p, snd p\<rangle> \<in> f" by auto
qed

lemma function_elem_snd:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> snd p \<in> B (fst p)"
  unfolding Function_def by auto

lemma apply_to_fst:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> f `(fst p) = snd p"
  using function_elem_pair by auto

lemma function_elem_pair':
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> p = \<langle>fst p, f `(fst p)\<rangle>"
  using function_elem_pair function_apply apply_to_fst by fastforce

lemma function_graph [simp]:
  assumes "f \<in> \<Prod>x\<in> A. (B x)"
  shows "{\<langle>x, f `x\<rangle> | x \<in> A} = f"
proof (rule equalityI)
  fix p

  show "p \<in> f \<Longrightarrow> p \<in> {\<langle>x, f `x\<rangle> | x \<in> A}"
    by (auto intro!: function_elem_fst function_elem_pair' assms)

  assume "p \<in> {\<langle>x, f `x\<rangle> | x \<in> A}"
  then have *: "fst p \<in> A" and **: "\<langle>fst p, f `(fst p)\<rangle> = p" by auto
  show "p \<in> f" by (fact function_elem[OF assms *, simplified **])
qed

lemma function_empty_iff [iff]: "f \<in> \<Prod>x\<in> {}. (B x) \<longleftrightarrow> f = {}"
  unfolding Function_def by auto

lemma function_subset_Pair [dest]:
  "f \<in> \<Prod>x\<in> A. (B x) \<Longrightarrow> f \<subseteq> \<Sum>x \<in> A. (B x)"
  unfolding Function_def by auto

lemma function_forget:
  "f \<in> \<Prod>x\<in> A. (B x) \<Longrightarrow> f \<in> A \<rightarrow> (\<Union>x \<in> A. B x)"
  unfolding Function_def by auto

lemma function_elemE [elim]:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); p \<in> f; P p \<Longrightarrow> Q; P \<langle>fst p, f `(fst p)\<rangle>\<rbrakk> \<Longrightarrow> Q"
  using function_elem_pair' by auto

lemma function_subsetI:
  assumes
    "f \<in> \<Prod>x\<in> A. (B x)"
    "g \<in> \<Prod>x\<in> A'. (B' x)"
    "A \<subseteq> A'"
    "\<And>x. x \<in> A \<Longrightarrow> f `x = g `x"
  shows "f \<subseteq> g"
proof (rule subsetI, rule function_elemE, rule assms, assumption+)
  fix p assume "p \<in> f"
  hence 1: "fst p \<in> A'" and 2: "g `(fst p) = f `(fst p)"
    using assms function_elem_fst by auto
  from 1 assms(2) function_elem have "\<langle>fst p, g `(fst p)\<rangle> \<in> g" by auto
  thus "\<langle>fst p, f `(fst p)\<rangle> \<in> g" using 2 by simp
qed

lemma function_apply_eqI:
  assumes
    "f \<in> \<Prod>x\<in> A. (B x)"
    "g \<in> \<Prod>x\<in> A'. (B' x)"
    "f \<subseteq> g"
    "x \<in> A \<inter> A'"
  shows "f `x = g `x"
proof -
  have "\<langle>x, f `x\<rangle> \<in> g" and "\<langle>x, g `x\<rangle> \<in> g" using function_elem assms by auto
  thus ?thesis using function_uniq_val assms by auto
qed

lemma function_in_PiI:
  assumes
    "f \<subseteq> \<Sum>x\<in> A. (B x)"
    "\<And>x. x \<in> A \<Longrightarrow> \<exists>!y. \<langle>x, y\<rangle> \<in> f"
  shows "f \<in> \<Prod>x\<in> A. (B x)"
  unfolding Function_def using assms by auto

lemma function_empty_dom [simp]: "{} \<rightarrow> A = {{}}" by (auto intro: equalityI)

lemma function_empty_range [simp]: "A \<rightarrow> {} = (if A = {} then {{}} else {})"
  unfolding Function_def by (auto intro!: equalityI)

lemma empty_function [intro]: "{} \<in> {} \<rightarrow> X" by auto

lemma singleton_function [intro]: "y \<in> B \<Longrightarrow> {\<langle>x, y\<rangle>} \<in> {x} \<rightarrow> B"
  unfolding Function_def by auto

lemma function_singletons [simp]: "f \<in> {a} \<rightarrow> {b} \<Longrightarrow> f = {\<langle>a, b\<rangle>}"
  unfolding Function_def by auto

lemma cons_FunctionI:
  "\<lbrakk>f \<in> A \<rightarrow> B; x \<notin> A\<rbrakk> \<Longrightarrow> cons \<langle>x, y\<rangle> f \<in> A \<union> {x} \<rightarrow> B \<union> {y}"
  unfolding Function_def using dom_def by auto

lemma cons_FunctionI':
  "\<lbrakk>f \<in> A \<rightarrow> B; x \<notin> A; y \<in> B\<rbrakk> \<Longrightarrow> cons \<langle>x, y\<rangle> f \<in> A \<union> {x} \<rightarrow> B"
  apply (drule cons_FunctionI, assumption)
  apply (subst bin_union_singleton_absorb[symmetric, where ?t=B])
  by (auto simp: bin_union_ac)

lemma bin_union_FunctionI:
  "\<lbrakk>f \<in> A \<rightarrow> B; x \<notin> A\<rbrakk> \<Longrightarrow> {\<langle>x, y\<rangle>} \<union> f \<in> A \<union> {x} \<rightarrow> B \<union> {y}"
  unfolding Function_def using dom_def by auto


section \<open>Soft types and type theory-like rules\<close>

lemma FunctionI [intro!]:
  "(\<And>x. x \<in> A \<Longrightarrow> b x \<in> B x) \<Longrightarrow> (\<lambda>x\<in> A. b x) \<in> \<Prod>x\<in> A. (B x)"
  unfolding lambda_def Function_def by auto

corollary FunctionI' [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> b `x \<in> B x) \<Longrightarrow> (\<lambda>x\<in> A. b `x) \<in> \<Prod>x\<in> A. (B x)" ..

lemma split_FunctionI [intro]:
  assumes "\<And>x y. \<lbrakk>x \<in> X; y \<in> Y\<rbrakk> \<Longrightarrow> b x y \<in> B \<langle>x, y\<rangle>"
  shows "(\<lambda>\<langle>x, y\<rangle>\<in> X \<times> Y. b x y) \<in> \<Prod>p\<in> X \<times> Y. (B p)"
  using assms by auto

lemma FunctionE [elim]:
  assumes "f \<in> \<Prod>x\<in> A. (B x)" and "a \<in> A"
  shows "f `a \<in> B a"
  using function_fiber function_elem assms by auto

lemma Function_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> \<Prod>x\<in> A. (B x) = \<Prod>x\<in> A'. (B' x)"
  by (simp add: Function_def cong: Pair_cong)

lemma lambda_type [type]:
  "lambda: (A: set) \<Rightarrow> ((x: element A) \<Rightarrow> element (B x)) \<Rightarrow>
    element (\<Prod>x\<in> A. (B x))"
  by unfold_types auto

lemma lambda_function_typeI [derive]:
  assumes "f: (x: element A) \<Rightarrow> element (B x)"
  shows "(\<lambda>x \<in> A. f x): element \<Prod>x \<in> A. (B x)"
  by discharge_types

lemma lambda_function_typeI' [backward_derive]:
  assumes "\<And>x. (x: element A \<Longrightarrow> f x: element (B x))"
  shows "(\<lambda>x \<in> A. f x): element \<Prod>x \<in> A. (B x)"
  by (auto intro: lambda_function_typeI)

lemma apply_type [type]:
  "apply: element (\<Prod>x\<in> A. (B x)) \<Rightarrow> (x: element A) \<Rightarrow> element (B x)"
  by unfold_types auto

lemma id_function [intro]: "(\<lambda>x\<in> A. x) \<in> A \<rightarrow> A" by auto

lemma id_type [type]: "(\<lambda>x \<in> A. x): element (A \<rightarrow> A)" by unfold_types auto


section \<open>Function extensionality\<close>

lemma funext:
  assumes
    "f \<in> \<Prod>x\<in> A. (B x)"
    "g \<in> \<Prod>x\<in> A. (C x)"
    "\<And>x. x \<in> A \<Longrightarrow> f `x = g `x"
  shows
    "f = g"
  apply (rule subset_antisym)
  using assms function_subsetI by auto

lemma lambda_ext: assumes "g: element \<Prod>a \<in> A. (B a)"
  and "\<And>a. a \<in> A \<Longrightarrow> f a = g `a"
  shows "(\<lambda>a \<in> A. f a) = g"
  using assms unfolding lambda_def by unfold_types auto

lemma eta: "f \<in> \<Prod>x\<in> A. (B x) \<Longrightarrow> (\<lambda>x\<in> A. f `x) = f"
  by (rule funext) auto

lemma function_refine:
  assumes
    "f \<in> \<Prod>x\<in> A. (B x)"
    "\<And>x. x \<in> A \<Longrightarrow> f `x \<in> C x"
  shows
    "f \<in> \<Prod>x\<in> A. (C x)"
proof -
  have "(\<lambda>x\<in> A. f `x) \<in> \<Prod>x\<in> A. (C x)" using assms by auto
  moreover have "(\<lambda>x\<in> A. f `x) = f" using assms by (simp add: eta)
  ultimately show ?thesis by auto
qed

corollary function_enlarge_range:
  assumes
    "f \<in> \<Prod>x\<in> A. (B x)"
    "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x"
  shows
    "f \<in> \<Prod>x\<in> A. (C x)"
proof -
  from assms(1) have "\<And>x. x \<in> A \<Longrightarrow> f `x \<in> B x" by auto
  with assms(2) have "\<And>x. x \<in> A \<Longrightarrow> f `x \<in> C x" by auto
  hence "(\<lambda>x\<in> A. f `x) \<in> \<Prod>x\<in> A. (C x)" ..
  thus ?thesis using assms(1) eta by auto
qed

corollary function_enlarge_range': "\<lbrakk>f \<in> A \<rightarrow> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> f \<in> A \<rightarrow> C"
  by (rule function_enlarge_range)


section \<open>More set-theoretic rules\<close>

lemma Function_empty_iff [iff]: "A \<rightarrow> B = {} \<longleftrightarrow> A \<noteq> {} \<and> B = {}"
proof (rule iffI, rule conjI)
  assume "A \<rightarrow> B = {}" show "B = {}"
  proof (rule ccontr)
    assume "B \<noteq> {}"
    then obtain b where "(\<lambda>x\<in> A. b) \<in> A \<rightarrow> B" by auto
    with \<open>A \<rightarrow> B = {}\<close> show False by auto
  qed
qed auto

(*Larry: Such functions arise in non-standard datatypes, ZF/ex/Ntree for instance.*)
lemma Function_collect_iff:
  "f \<in> \<Prod>x\<in> A. {y \<in> B x | P x y} \<longleftrightarrow> f \<in> \<Prod>x\<in> A. (B x) \<and> (\<forall>x \<in> A. P x (f `x))"
  by (auto intro: function_refine dest: FunctionE)


section \<open>Injectivity and surjectivity\<close>

definition "injective f \<equiv> \<forall>x \<in> dom f. \<forall>x' \<in> dom f. f `x = f `x' \<longrightarrow> x = x'"

text \<open>Surjectivity has to be with respect to some specific codomain.\<close>

definition "surjective B f \<equiv> \<forall>y \<in> B. \<exists>x. \<langle>x, y\<rangle> \<in> f"

lemma surjectiveI:
  assumes
    "f \<in> A \<rightarrow> B"
    "(\<And>y. y \<in> B \<Longrightarrow> \<exists>x \<in> A. f `x = y)"
  shows "surjective B f"
unfolding surjective_def
proof
  fix y assume "y \<in> B"
  then obtain x where "x \<in> A" and "y = f `x" using assms by auto
  thus "\<exists>x. \<langle>x, y\<rangle> \<in> f" using assms by (auto intro: function_elem)
qed


section \<open>More function application\<close>

lemma apply_singleton [simp]: "{\<langle>x, y\<rangle>} `x = y"
  by (auto simp: apply_def)

lemma apply_pair1 [simp]: "x \<noteq> y \<Longrightarrow> {\<langle>x, a\<rangle>, \<langle>y, b\<rangle>} `x = a"
  by (auto simp: apply_def)

lemma apply_pair2 [simp]: "x \<noteq> y \<Longrightarrow> {\<langle>x, a\<rangle>, \<langle>y, b\<rangle>} `y = b"
  by (auto simp: apply_def)

lemma apply_cons_head [simp]:
  "x \<notin> dom A \<Longrightarrow> (cons \<langle>x, y\<rangle> A) `x = y"
  unfolding dom_def apply_def by (rule theI2) auto

lemma apply_cons_tail [simp]:
  "x \<noteq> y \<Longrightarrow> (cons \<langle>y, z\<rangle> A) `x = A `x"
  unfolding apply_def by auto

lemma apply_bin_union1 [simp]:
  "x \<notin> dom B \<Longrightarrow> (A \<union> B) `x = A `x"
  unfolding apply_def by (auto elim: not_in_domE)

lemma apply_bin_union2 [simp]:
  "x \<notin> dom A \<Longrightarrow> (A \<union> B) `x = B `x"
  unfolding apply_def by (auto elim: not_in_domE)


section \<open>More extensionality\<close>

lemma funext_iff:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); g \<in> \<Prod>x\<in> A. (C x)\<rbrakk> \<Longrightarrow> (\<forall>a \<in> A. f `a = g `a) \<longleftrightarrow> f = g"
  by (auto intro: funext)

(*Larry: Theorem by Mark Staples, proof by LCP.*)
lemma function_dom_imp_subset_iff_eq:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); g \<in> \<Prod>x\<in> A. (C x)\<rbrakk> \<Longrightarrow> f \<subseteq> g \<longleftrightarrow> (f = g)"
  by (blast dest: function_elem intro: funext function_apply[symmetric])

(*Every element of (Function A B) may be expressed as a lambda abstraction*)
lemma function_lambdaE:
  assumes
    "f \<in> \<Prod>x\<in> A. (B x)" and
    "\<And>b. \<lbrakk>\<forall>x \<in> A. b x \<in> B x; f = (\<lambda>x\<in> A. b x)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  by (rule assms(2)[of "apply f"]) (auto simp: assms(1) eta)

text \<open>Extend a function's domain by mapping new elements to the empty set.\<close>

definition triv_ext :: "set \<Rightarrow> set \<Rightarrow> set"
  where "triv_ext A f \<equiv> f \<union> (\<lambda>x\<in> (A \<setminus> dom f). {})"

lemma triv_ext_dom [simp]: "dom (triv_ext A f) = dom f \<union> A"
  unfolding triv_ext_def by (auto simp: bin_union_dom diff_partition')


section \<open>Composition\<close>

definition fun_comp :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> (infixr "\<circ>" 80)
  where "g \<circ> f = \<lambda>x\<in> dom f. g `(f `x)"

lemma compose_lambdas:
  "f: element A \<Rightarrow> element B \<Longrightarrow> (\<lambda>y \<in> B. g y) \<circ> (\<lambda>x\<in> A. f x) = \<lambda>x\<in> A. g (f x)"
  by (auto simp: fun_comp_def)

lemma compose_functions [intro]:
  assumes "f \<in> A \<rightarrow> B" and "g \<in> \<Prod>x\<in> B. (C x)"
  shows "g \<circ> f \<in> \<Prod>x\<in> A. (C (f `x))"
proof -
  have "dom f = A" using assms(1) ..
  with assms show ?thesis unfolding fun_comp_def by fast
qed

lemma compose_idr [simp]: "f \<in> \<Prod>x\<in> A. (B x) \<Longrightarrow> f \<circ> (\<lambda>x\<in> A. x) = f"
  unfolding fun_comp_def by (auto simp: eta)

lemma compose_idl [simp]: "f \<in> A \<rightarrow> B \<Longrightarrow> (\<lambda>x\<in> B. x) \<circ> f = f"
  unfolding fun_comp_def by (auto simp: eta)

lemma compose_assoc [simp]:
  assumes "f \<in> A \<rightarrow> B" "g \<in> B \<rightarrow> C"
  shows "h \<circ> g \<circ> f = (h \<circ> g) \<circ> f"
  unfolding fun_comp_def by auto

lemma fun_comp_type [derive]:
  assumes "f: element (A \<rightarrow> B)" "g: element (\<Prod>x\<in> B. (C x))"
  shows "g \<circ> f: element (\<Prod>x\<in> A. (C (f `x)))"
  by unfold_types (auto intro: assms)


section \<open>Restriction\<close>

definition restriction :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> (infix "\<restriction>" 100)
  where "f \<restriction> A = {p \<in> f | fst p \<in> A}"

lemma apply_restriction [simp]: "a \<in> A \<Longrightarrow> (f \<restriction> A) `a = f `a"
  unfolding restriction_def apply_def by auto

lemma restriction_dom: "dom (f \<restriction> A) = dom f \<inter> A"
  unfolding restriction_def dom_def by (auto intro: equalityI)

lemma restriction_function [intro]:
  "f \<in> A \<rightarrow> B \<Longrightarrow> f \<restriction> A' \<in> (A \<inter> A') \<rightarrow> B"
  unfolding restriction_def Function_def by auto

lemma restriction_function_subset [intro]:
  "\<lbrakk>f \<in> A \<rightarrow> B; A' \<subseteq> A\<rbrakk> \<Longrightarrow> f \<restriction> A' \<in> A' \<rightarrow> B"
  by (subst (4) bin_inter_subset_right_absorb[symmetric]) auto


section \<open>Gluing\<close>

definition "glue X = \<Union>X"

lemma glueI:
  assumes "\<And>f. f \<in> X \<Longrightarrow> \<exists>A. f \<in> A \<rightarrow> B"
      and "\<And>f g x. \<lbrakk>f \<in> X; g \<in> X; x \<in> dom f \<inter> dom g\<rbrakk> \<Longrightarrow> f `x = g `x"
  shows "glue X \<in> (\<Union>f\<in> X. dom f) \<rightarrow> B"
unfolding glue_def
proof (rule function_in_PiI)
  show "\<Union>X \<subseteq> (\<Union>f\<in> X. dom f) \<times> B"
    using assms(1) by (force simp: Function_def dom_def)

  fix x assume asm: "x \<in> (\<Union>f\<in> X. dom f)"
  show "\<exists>!y. \<langle>x, y\<rangle> \<in> \<Union>X"
  proof (rule ex_ex1I)
    from asm assms(1) obtain f A where
      f: "f \<in> X" "x \<in> dom f" and
      "f \<in> A \<rightarrow> B"
      by fastforce
    then have "\<langle>x, f `x\<rangle> \<in> \<Union>X" using function_elem by auto
    thus "\<exists>y. \<langle>x, y\<rangle> \<in> \<Union>X" ..

    have "\<And>y. \<langle>x, y\<rangle> \<in> \<Union>X \<Longrightarrow> y = f `x"
    proof -
      fix y assume asm: "\<langle>x, y\<rangle> \<in> \<Union>X"
      with assms(1) obtain g where
        g: "g \<in> X" "x \<in> dom g" and
        *: "y = g `x" by fastforce
      have "g `x = f `x" using assms(2) by (fast intro: f g)
      with * show "y = f `x" by simp
    qed
    thus "\<And>y y'. \<langle>x, y\<rangle> \<in> \<Union>X \<Longrightarrow> \<langle>x, y'\<rangle> \<in> \<Union>X \<Longrightarrow> y = y'" by auto
  qed
qed

lemma apply_glue:
  assumes "\<And>f. f \<in> X \<Longrightarrow> \<exists>A. f \<in> A \<rightarrow> B"
  and "\<And>f g. \<lbrakk>f \<in> X; g \<in> X; a \<in> dom f \<inter> dom g\<rbrakk> \<Longrightarrow> f `a = g `a"
  and "f \<in> X"
  and "a \<in> dom f"
  shows "(glue X) `a = f `a"
proof (subst apply_def, subst glue_def, subst union, rule the_equality)
  from assms(1)[OF assms(3)] obtain A where f_func: "f \<in> A \<rightarrow> B" ..
  with assms(4) have "a \<in> A" by simp
  from function_elem[OF f_func this] have "\<langle>a, f `a\<rangle> \<in> f" .
  show "\<exists>g. g \<in> X \<and> \<langle>a, f `a\<rangle> \<in> g" by (rule exI[where ?x=f]) auto
next
  fix b assume "\<exists>g. g \<in> X \<and> \<langle>a, b\<rangle> \<in> g"
  then obtain g where g_in_X: "g \<in> X" and "\<langle>a, b\<rangle> \<in> g" by auto
  from assms(1)[OF this(1)] obtain A where f_func: "g \<in> A \<rightarrow> B" ..
  with \<open>\<langle>a, b\<rangle> \<in> g\<close> have g_a_eq_b: "g `a = b" and "a \<in> dom g" by auto
  from this(2) and assms(4) have "a \<in> dom g \<inter> dom f" by simp
  from assms(2)[OF g_in_X assms(3) this] have "g `a = f `a" .
  with g_a_eq_b show "b = f `a" by simp
qed

lemma apply_glue_bin: assumes "f \<in> A \<rightarrow> B" "g \<in> A' \<rightarrow> B"
  and "a \<in> A"
  and "a \<in> A' \<Longrightarrow> f `a = g `a"
  shows "glue {f, g} `a = f `a"
proof (rule apply_glue)
  let ?G = "{f, g}"
  fix h i assume "h \<in> ?G" and "i \<in> ?G" and "a \<in> dom h \<inter> dom i"
  then show "h `a = i `a"
    by (cases "h = i") (auto intro: assms(4) assms(4)[symmetric])
qed auto

lemma apply_glue_bin': assumes "f \<in> A \<rightarrow> B" "g \<in> A' \<rightarrow> B"
  and "a \<in> A'"
  and "a \<in> A \<Longrightarrow> f `a = g `a"
  shows "glue {f, g} `a = g `a"
  by (subst cons_comm, rule apply_glue_bin[OF assms(2)]) (auto simp: assms)

lemma glue_pairI:
  assumes "f \<in> A \<rightarrow> B" "g \<in> A' \<rightarrow> B"
  and "\<And>a. \<lbrakk>a \<in> A \<inter> A'\<rbrakk> \<Longrightarrow> f `a = g `a"
  shows "glue {f, g} \<in> (A \<union> A') \<rightarrow> B" (is "glue ?X \<in> ?D \<rightarrow> B")
proof -
  have 1: "?D = (\<Union>f \<in> ?X. dom f)" using repl_cons bin_union_def by auto
  show ?thesis by (subst 1, rule glueI) (auto simp: assms)
qed


section \<open>Universes\<close>

lemma univ_Function_closed [intro]:
  assumes
    "A \<in> univ U"
    "\<And>x. x \<in> A \<Longrightarrow> B x \<in> univ U"
  shows
    "\<Prod>x\<in> A. (B x) \<in> univ U"
proof -
  let ?P = "powerset \<Sum>x\<in> A. (B x)"
  have "\<Prod>x\<in> A. (B x) \<subseteq> ?P" unfolding Function_def by (fact collect_subset)
  moreover have "?P \<in> univ U" using assms by auto
  ultimately show ?thesis by (auto intro: univ_transitive)
qed


end
