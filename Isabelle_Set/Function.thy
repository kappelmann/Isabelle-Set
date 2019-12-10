section \<open>Functions\<close>

theory Function
imports Relation

begin

text \<open>
  Functions are identified with their graphs. Function sets are formulated
  dependently by default.
\<close>

definition Function :: "[set, set \<Rightarrow> set] \<Rightarrow> set"
  where "Function A B \<equiv> {f \<in> Pow (\<Sum>x \<in> A. (B x)) | \<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f}"

syntax
  "_Function" :: "[pttrn, set, set] => set type" ("(2\<Prod>_\<in> _./ _)" [0, 0, 100])
translations
  "\<Prod>x\<in> A. B" \<rightleftharpoons> "CONST Function A (\<lambda>x. B)"

abbreviation "function" :: "[set, set] \<Rightarrow> set" (infixr "\<rightarrow>" 60)
  where "A \<rightarrow> B \<equiv> \<Prod>x\<in> A. B"


subsection \<open>Lambda\<close>

text \<open>Construct set-theoretic functions from HOL functions.\<close>

definition lambda :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "lambda A b \<equiv> {\<langle>x, b x\<rangle> | x \<in> A}"

syntax "_lam" :: "[pttrn, set, set] => set" ("(3\<lambda>_\<in> _./ _)" 60)
translations "\<lambda>x\<in> A. f" \<rightleftharpoons> "CONST lambda A (\<lambda>x. f)"

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
  by (simp only: lambda_def cong add: Repl_cong)

lemmas lambda_cong' [intro!] = lambda_cong[OF refl]

(*Generalized version of lambda_cong*)
lemma lambda_context:
  "\<lbrakk>P (\<lambda>x\<in> A. f x); \<And>x. x \<in> A \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> P (\<lambda>x\<in> A. g x)"
  by auto

lemma lambda_eqE: "\<lbrakk>(\<lambda>x\<in> A. f x) = \<lambda>x\<in> A. g x; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
  by (auto elim: equalityE)

(*Does not work as simp rule*)
lemma lambda_times_split: "(\<lambda>x\<in> A \<times> B. f x) = (\<lambda>\<langle>a, b\<rangle> \<in> A \<times> B. f \<langle>a, b\<rangle>)"
  by (rule lambda_cong) auto


subsection \<open>Function application and \<beta>-reduction\<close>

definition "apply" :: "set \<Rightarrow> set \<Rightarrow> set" ("_ `_" [999, 1000] 999)
  where "f `x = (THE y. \<langle>x, y\<rangle> \<in> f)"

lemma beta [simp]: "a \<in> A \<Longrightarrow> (\<lambda>x\<in> A. b x) `a = b a"
  by (auto simp: lambda_def apply_def)

lemma beta_split [simp]:
  assumes "a \<in> A" "b \<in> B"
  shows "(\<lambda>p \<in> A \<times> B. (\<lambda>\<langle>x,y\<rangle>. P x y) p) `\<langle>a, b\<rangle> = P a b"
  using assms by auto


subsection \<open>Rules\<close>

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

text \<open>Type theory-like rules:\<close>

lemma FunctionI [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> b x \<in> B x) \<Longrightarrow> (\<lambda>x\<in> A. b x) \<in> \<Prod>x\<in> A. (B x)"
  unfolding lambda_def Function_def by auto

text \<open>Set-theoretic lambda introduction:\<close>

corollary FunctionI' [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> b `x \<in> B x) \<Longrightarrow> (\<lambda>x\<in> A. b `x) \<in> \<Prod>x\<in> A. (B x)" ..

lemma FunctionE [elim]:
  assumes "f \<in> \<Prod>x\<in> A. (B x)" and "a \<in> A"
  shows "f `a \<in> B a"
  using function_fiber function_elem assms by auto

lemma function_relation [elim]:
  "f \<in> \<Prod>x\<in> A. (B x) \<Longrightarrow> f \<subseteq> A \<times> (\<Union>x \<in> A. B x)"
  unfolding Function_def by auto

lemma function_relation' [elim]:
  "f \<in> A \<rightarrow> B \<Longrightarrow> f \<subseteq> A \<times> B"
  using function_relation by auto

lemma function_dom [elim, simp]: "f \<in> \<Prod>x\<in> A. (B x) \<Longrightarrow> dom f = A"
  unfolding Function_def dom_def
  by (force intro: extensionality)

lemma function_elem_dom: "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> x \<in> A"
  using domI function_dom by fastforce

lemma function_apply [simp]: "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> f `x = y"
  using domI function_dom function_elem function_uniq_val by fast

lemma function_elem_opair:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> p = \<langle>fst p, snd p\<rangle>"
  by (elim Pair_subset_elem) (rule function_relation)

lemma function_elem_fst:
  assumes "f \<in> \<Prod>x\<in> A. (B x)" "p \<in> f"
  shows "fst p \<in> A"
proof (rule function_elem_dom, fact)
  from assms have "p = \<langle>fst p, snd p\<rangle>" by (rule function_elem_opair)
  with assms show "\<langle>fst p, snd p\<rangle> \<in> f" by auto
qed

lemma function_elem_snd:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> snd p \<in> B (fst p)"
  unfolding Function_def by auto

lemma apply_to_fst:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> f `(fst p) = snd p"
  using function_elem_opair by auto

lemma function_elem_opair':
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> p = \<langle>fst p, f `(fst p)\<rangle>"
  using function_elem_opair function_apply apply_to_fst by fastforce

lemma function_graph:
  assumes "f \<in> \<Prod>x\<in> A. (B x)"
  shows "f = {\<langle>x, f `x\<rangle> | x \<in> A}"
proof (rule equalityI)
  fix p

  show "p \<in> f \<Longrightarrow> p \<in> {\<langle>x, f `x\<rangle> | x \<in> A}"
    by (auto intro!: function_elem_fst function_elem_opair' assms)

  assume "p \<in> {\<langle>x, f `x\<rangle> | x \<in> A}"
  then have *: "fst p \<in> A" and **: "\<langle>fst p, f `(fst p)\<rangle> = p" by auto
  show "p \<in> f" by (fact function_elem[OF assms *, simplified **])
qed

lemma function_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> \<Prod>x\<in> A. (B x) = \<Prod>x\<in> A'. (B' x)"
  by (simp add: Function_def cong: Pair_cong)

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
  using function_elem_opair' by auto

lemma extend_function:
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

lemma funext:
  assumes
    "f \<in> \<Prod>x\<in> A. (B x)"
    "g \<in> \<Prod>x\<in> A. (C x)"
    "\<And>x. x \<in> A \<Longrightarrow> f `x = g `x"
  shows
    "f = g"
  apply (rule extensionality)
  using assms subset_refl extend_function by auto

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
  thus ?thesis by (simp add: eta)
qed

corollary function_enlarge_range': "\<lbrakk>f \<in> A \<rightarrow> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> f \<in> A \<rightarrow> C"
  by (rule function_enlarge_range)

(*
  Larry: Such functions arise in non-standard datatypes, ZF/ex/Ntree for
  instance.
*)
lemma function_collect_iff:
  "f \<in> \<Prod>x\<in> A. {y \<in> B x | P x y} \<longleftrightarrow> f \<in> \<Prod>x\<in> A. (B x) \<and> (\<forall>x \<in> A. P x (f `x))"
  by (auto intro: function_refine dest: FunctionE)

lemma id_function [intro]: "(\<lambda>x\<in> A. x) \<in> A \<rightarrow> A" by auto

lemma function_empty_dom [simp]: "{} \<rightarrow> A = {{}}" by (auto intro: equalityI)

lemma function_empty_range [simp]: "A \<rightarrow> {} = (if A = {} then {{}} else {})"
  unfolding Function_def by (auto intro!: equalityI)

lemma empty_function [intro]: "{} \<in> {} \<rightarrow> X" by auto
lemma empty_function_iff [iff]: "f \<in> {} \<rightarrow> X \<longleftrightarrow> f = {}" by auto

lemma Function_empty_iff [iff]: "A \<rightarrow> B = {} \<longleftrightarrow> A \<noteq> {} \<and> B = {}"
proof (rule iffI, rule conjI)
  assume "A \<rightarrow> B = {}" show "B = {}"
  proof (rule ccontr)
    assume "B \<noteq> {}"
    then obtain b where "(\<lambda>x\<in> A. b) \<in> A \<rightarrow> B" by auto
    with \<open>A \<rightarrow> B = {}\<close> show False by auto
  qed
qed auto

lemma singleton_function [intro]: "y \<in> B \<Longrightarrow> {\<langle>x, y\<rangle>} \<in> {x} \<rightarrow> B"
  unfolding Function_def by auto

lemma function_singletons [simp]: "f \<in> {a} \<rightarrow> {b} \<Longrightarrow> f = {\<langle>a, b\<rangle>}"
  unfolding Function_def by auto

lemma cons_functionI:
  "\<lbrakk>f \<in> A \<rightarrow> B; x \<notin> A\<rbrakk> \<Longrightarrow> cons \<langle>x, y\<rangle> f \<in> A \<union> {x} \<rightarrow> B \<union> {y}"
  unfolding Function_def using dom_def by auto

lemma bin_union_functionI:
  "\<lbrakk>f \<in> A \<rightarrow> B; x \<notin> A\<rbrakk> \<Longrightarrow> {\<langle>x, y\<rangle>} \<union> f \<in> A \<union> {x} \<rightarrow> B \<union> {y}"
  unfolding Function_def using dom_def by auto


subsection \<open>Injectivity and surjectivity\<close>

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


subsection \<open>More function application\<close>

lemma apply_singleton [simp]: "{\<langle>x, y\<rangle>} `x = y"
  by (auto simp: apply_def)

lemma apply_pair1 [simp]: "x \<noteq> y \<Longrightarrow> {\<langle>x, a\<rangle>, \<langle>y, b\<rangle>} `x = a"
  by (auto simp: apply_def)

lemma apply_pair2 [simp]: "x \<noteq> y \<Longrightarrow> {\<langle>x, a\<rangle>, \<langle>y, b\<rangle>} `y = b"
  by (auto simp: apply_def)

lemma apply_cons_head:
  "x \<notin> dom A \<Longrightarrow> (cons \<langle>x, y\<rangle> A) `x = y"
  unfolding dom_def apply_def by (rule theI2) auto

lemma apply_cons_tail:
  "x \<noteq> y \<Longrightarrow> (cons \<langle>y, z\<rangle> A) `x = A `x"
  unfolding apply_def by auto


subsection \<open>More function extensionality\<close>

lemma funext_iff:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); g \<in> \<Prod>x\<in> A. (C x)\<rbrakk> \<Longrightarrow> (\<forall>a \<in> A. f `a = g `a) \<longleftrightarrow> f = g"
  by (auto intro: funext)

(*Larry: Theorem by Mark Staples, proof by LCP.*)
lemma extend_function_eq:
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); g \<in> \<Prod>x\<in> A. (C x)\<rbrakk> \<Longrightarrow> f \<subseteq> g \<longleftrightarrow> (f = g)"
  by (blast dest: function_elem intro: funext function_apply[symmetric])

(*Every element of (Function A B) may be expressed as a lambda abstraction*)
lemma function_lambdaE:
  assumes
    "f \<in> \<Prod>x\<in> A. (B x)" and
    "\<And>b. \<lbrakk>\<forall>x \<in> A. b x \<in> B x; f = (\<lambda>x\<in> A. b x)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  by(auto intro!: assms FunctionE simp: eta)

text \<open>Extend a function's domain by mapping new elements to the empty set.\<close>

definition triv_ext :: "set \<Rightarrow> set \<Rightarrow> set"
  where "triv_ext A f \<equiv> f \<union> (\<lambda>x\<in> (A \<setminus> dom f). {})"

lemma triv_ext_dom [simp]: "dom (triv_ext A f) = dom f \<union> A"
  unfolding triv_ext_def by (auto simp: bin_union_dom diff_partition')


subsection \<open>Composition\<close>

definition fun_comp :: \<open>set \<Rightarrow> set \<Rightarrow> set\<close> (infixr "\<circ>" 80)
  where "g \<circ> f = \<lambda>x\<in> dom f. g `(f `x)"

lemma compose_lambdas:
  "f : element A \<Rightarrow> element B \<Longrightarrow> (\<lambda>y \<in> B. g y) \<circ> (\<lambda>x\<in> A. f x) = \<lambda>x\<in> A. g (f x)"
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
  unfolding fun_comp_def
  by (force intro: lambda_context beta[symmetric] eta)

text \<open>
  The following proof is mostly rewriting, with some peeking into the local
  contexts of lambda terms. Automation still doesn't do these kinds of proofs
  very well.
\<close>

lemma compose_assoc:
  assumes "f \<in> A \<rightarrow> B" "g \<in> B \<rightarrow> C"
  shows "h \<circ> g \<circ> f = (h \<circ> g) \<circ> f"
  unfolding fun_comp_def
  apply (auto intro: assms)
  apply (subst beta)
  using assms by auto


subsection \<open>Universes\<close>

lemma Univ_Function_closed [intro]:
  assumes
    "A \<in> Univ U"
    "\<And>x. x \<in> A \<Longrightarrow> B x \<in> Univ U"
  shows
    "\<Prod>x\<in> A. (B x) \<in> Univ U"
proof -
  let ?P = "Pow \<Sum>x\<in> A. (B x)"
  have "\<Prod>x\<in> A. (B x) \<subseteq> ?P" unfolding Function_def by (fact collect_subset)
  moreover have "?P \<in> Univ U" using assms by auto
  ultimately show ?thesis by (auto intro: Univ_transitive)
qed


subsection \<open>Soft typing\<close>

lemma lambda_simple_type [type]:
  "lambda : (A : set) \<Rightarrow> (element A \<Rightarrow> element B) \<Rightarrow> element (A \<rightarrow> B)"
  by unfold_types auto

lemma apply_simple_type [type]:
  "apply : element (A \<rightarrow> B) \<Rightarrow> element A \<Rightarrow> element B"
  by unfold_types auto

lemma apply_dep_type:
  "apply : element (\<Prod>x\<in> A. (B x)) \<Rightarrow> (x : element A) \<Rightarrow> element (B x)"
  by unfold_types auto

(* text \<open>Class of all functions\<close>

definition uniq_valued :: "set \<Rightarrow> bool"
  where "uniq_valued R \<equiv> \<forall>x y y'. \<langle>x, y\<rangle> \<in> R \<and> \<langle>x, y'\<rangle> \<in> R \<longrightarrow> y = y'"

definition function :: "set type"
  where function_typedef: "function \<equiv> uniq_valued \<sqdot> relation"

definition total :: "set \<Rightarrow> set \<Rightarrow> bool" ("(_-total)" [1000])
  where "A-total \<equiv> \<lambda>f. dom f = A"

lemma Function_relation_type [elim]: "f \<in> \<Prod>x\<in> A. (B x) \<Longrightarrow> f : relation"
  by (drule function_rel, drule relations_relation_type) unfold_types

lemma Function_function_type [elim]: "f \<in> Function A B \<Longrightarrow> f : A-total \<sqdot> function"
  unfolding function_typedef uniq_valued_def total_def adjective_def
  by unfold_types auto

lemma function_function_type [elim]: "f \<in> A \<rightarrow> B \<Longrightarrow> f : A-total \<sqdot> B-valued \<sqdot> function"
  unfolding function_typedef uniq_valued_def total_def valued_def adjective_def
  by (unfold_types, auto) (insert range_subset, blast)
*)


subsection \<open>Automation\<close>

text \<open>Ad-hoc automation for set-theoretic functions.\<close>

method beta uses add = (subst function_apply; (auto intro: add)?)

text \<open>As a tactic:\<close>

ML \<open>
fun beta_tac ths ctxt =
  SUBGOAL (fn (_, i) =>
    EqSubst.eqsubst_tac ctxt [0] @{thms function_apply} i
    THEN ALLGOALS (resolve_tac ctxt ths))
\<close>

text \<open>Evaluate \<open>f `a\<close> where f is given explicitly as a graph of pairs:\<close>

method eval_graph = ((subst function_apply; auto?), (rule cons_functionI)+, auto)

text \<open>A better approach would be to set up the simplifier.\<close>

(* Josh: Can't get this to work yet... *)

(*
lemma apply_function':
  "\<lbrakk>f \<in> \<Prod>x\<in> A. (B x); \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> f `x \<equiv> y"
  by auto

simproc_setup beta ("f `x") = \<open>fn _ => fn _ => fn ct =>
  let
    val Const (\<^const_name>\<open>apply\<close>, _) $ f $ a = Thm.term_of ct
  in
    (@{print} f; @{print} a; SOME @{thm apply_function'})
  end\<close>

ML \<open>
val beta_reduction_simp_solver =
  let
    fun solver ctxt =
      let
        val thms =
          dest_ss (simpset_of ctxt)
            |> #simps
            |> map snd
        val _ = (@{print} thms)
      in
        simp_tac (empty_simpset ctxt addsimps thms)
      end
  in
    map_theory_simpset (fn ctxt => ctxt
      addSolver (mk_solver "beta-reduce functions" solver))
  end
\<close>
setup \<open>beta_reduction_simp_solver\<close>
*)

lemma test:
  assumes "\<langle>a, b\<rangle> \<in> f" "f \<in> A \<rightarrow> B" "b : T"
  shows "f `a : T"
  \<comment>\<open>Can't get this to work\<close>
  (* by (simp add: assms) *)
  \<comment>\<open>This works, but had to instantiate the value to which we want to rewrite f `a...\<close>
  (* apply (simp add: assms function_apply[of _ A "\<lambda>_. B" _ b]) *)
  using assms by beta


end
