section \<open>Function\<close>

text \<open>Function are formulated dependently, with nondependent functions as a special case.\<close>

theory Function
imports Relation

begin

subsection \<open>Function spaces\<close>

definition Function :: "[set, set \<Rightarrow> set] \<Rightarrow> set"
  where "Function A B \<equiv> {f \<in> Pow (\<Sum>x \<in> A. (B x)) | \<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f}"

syntax "_Function" :: "[pttrn, set, set] => set type" ("(3\<Prod>_ \<in> _./ _)" [0, 0, 100])
translations "\<Prod>x \<in> A. B" \<rightleftharpoons> "CONST Function A (\<lambda>x. B)"

abbreviation "functions" :: "[set, set] \<Rightarrow> set" (infixr "\<rightarrow>" 60)
  where "A \<rightarrow> B \<equiv> \<Prod>x \<in> A. B"


subsection \<open>Lambda abstraction and application\<close>

definition lambda :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "lambda A b \<equiv> {\<langle>x, b x\<rangle> | x \<in> A}"

syntax "_lam" :: "[pttrn, set, set] => set" ("(3\<lambda>_ \<in> _./ _)" 200)
translations "\<lambda>x \<in> A. f" \<rightleftharpoons> "CONST lambda A (\<lambda>x. f)"

definition "apply" :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "`" 90)
  where "f`x = (THE y. \<langle>x, y\<rangle> \<in> f)"

lemma lambdaI [intro]: "a \<in> A \<Longrightarrow> \<langle>a, b a\<rangle> \<in> \<lambda>x \<in> A. b x"
  unfolding lambda_def by auto

lemma lambdaE [elim]: "\<lbrakk>p \<in> \<lambda>x \<in> A. b x; \<And>x. \<lbrakk>x \<in> A; p = \<langle>x, b x\<rangle>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: lambda_def, blast)

lemma lambdaD [dest]: "\<lbrakk>\<langle>a, c\<rangle> \<in> \<lambda>x \<in> A. b x\<rbrakk> \<Longrightarrow> c = b a"
  by auto

lemma beta [simp]: "a \<in> A \<Longrightarrow> (\<lambda>x \<in> A. b x) ` a = b a"
  by (auto simp: lambda_def apply_def)

lemma lambda_dom [simp]: "dom (\<lambda>x \<in> A. b x) = A"
  by (auto simp: lambda_def)

lemma lambda_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> b x = b' x\<rbrakk> \<Longrightarrow> (\<lambda>x \<in> A. b x) = \<lambda>x \<in> A'. b' x"
  by (simp only: lambda_def cong add: Repl_cong)

lemma lambda_eqE: "\<lbrakk>(\<lambda>x \<in> A. f x) = \<lambda>x \<in> A. g x; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
  by (auto elim: equalityE)

lemma apply_singleton [simp]: "{\<langle>x, y\<rangle>} ` x = y"
  by (auto simp: apply_def)

lemma apply_pair1 [simp]: "x \<noteq> y \<Longrightarrow> {\<langle>x, a\<rangle>, \<langle>y, b\<rangle>} ` x = a"
  by (auto simp: apply_def)

lemma apply_pair2 [simp]: "x \<noteq> y \<Longrightarrow> {\<langle>x, a\<rangle>, \<langle>y, b\<rangle>} ` y = b"
  by (auto simp: apply_def)

lemma beta_split [simp]:
  assumes "a \<in> A" "b \<in> B"
  shows "(\<lambda>p \<in> A \<times> B. (\<lambda>\<langle>x,y\<rangle>. P x y) p) ` \<langle>a, b\<rangle> = P a b"
  using assms by auto

lemma beta_split_typed [simp]:
  "\<lbrakk>a : element A; b : element B \<rbrakk> \<Longrightarrow> (\<lambda>p \<in> A \<times> B. (\<lambda>\<langle>x,y\<rangle>. P x y) p) ` \<langle>a, b\<rangle> = P a b"
  by squash_types (fact beta_split)

(* does not work as simp rule *)
lemma lambda_times_split: "(\<lambda>x \<in> A \<times> B. f x) = (\<lambda>\<langle>a, b\<rangle> \<in> A \<times> B. f \<langle>a, b\<rangle>)"
  by (rule lambda_cong) auto
  

subsection \<open>Rules for functions\<close>

lemma function_rel [elim]: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f \<subseteq> A \<times> (\<Union>x \<in> A. (B x))"
  unfolding Function_def by auto

lemma function_rel' [elim]: "f \<in> A \<rightarrow> B \<Longrightarrow> f \<subseteq> A \<times> B"
  using function_rel by auto

lemma uniq_val_imp: "\<lbrakk>\<exists>!y. \<langle>x, y\<rangle> \<in> f; x \<in> A\<rbrakk> \<Longrightarrow> \<langle>x, f`x\<rangle> \<in> f"
proof -
  assume ex: "\<exists>!y. \<langle>x, y\<rangle> \<in> f" and "x \<in> A"
  then obtain y where mem: "\<langle>x, y\<rangle> \<in> f" by auto
  with ex have "f`x = y" using apply_def by auto
  with mem show "\<langle>x, f`x\<rangle> \<in> f" by simp
qed

lemma function_mems: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); x \<in> A\<rbrakk> \<Longrightarrow> \<langle>x, f`x\<rangle> \<in> f"
  unfolding Function_def
  by (drule collectD2, drule Bspec, auto intro: uniq_val_imp)

lemma function_dom [elim]:
  "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> dom f = A"
apply ((rule extensionality dom_subset function_rel)+, auto)
proof (simp only: Function_def, drule collectD2)
  fix x assume "x \<in> A" and "\<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f"
  then obtain y where "\<langle>x, y\<rangle> \<in> f" by auto
  thus "x \<in> dom f" using domI by auto
qed

lemma function_uniq_val [elim]:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<langle>x, y\<rangle> \<in> f; \<langle>x, y'\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y = y'"
unfolding Function_def by auto

lemma function_fiber: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y \<in> B x"
  unfolding Function_def by auto

lemma FunctionI [intro]:
  assumes
    f_relation: "f \<subseteq> A \<times> (\<Union>x \<in> A. (B x))" and
    uniq_val: "\<And>x. x \<in> A \<Longrightarrow> \<exists>!y. \<langle>x, y\<rangle> \<in> f" and
    stratified: "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> B x"
  shows "f \<in> \<Prod>x \<in> A. (B x)"
unfolding Function_def proof (auto, rule PairI2)
  fix p assume asm: "p \<in> f"

  thus "p = \<langle>fst p, snd p\<rangle>" using f_relation by auto
  hence *: "\<langle>fst p, snd p\<rangle> \<in> f" using asm by auto

  show fst_elem: "fst p \<in> A" using f_relation asm by auto

  have "\<langle>fst p, f`(fst p)\<rangle> \<in> f"
    using uniq_val_imp uniq_val[OF \<open>fst p \<in> A\<close>] fst_elem
    by auto
  hence eq: "snd p = f`(fst p)" using uniq_val[OF \<open>fst p \<in> A\<close>] * by auto 

  have "f`(fst p) \<in> B (fst p)" using fst_elem stratified by auto
  thus "snd p \<in> B (fst p)" using eq by simp
next
  fix x assume asm: "x \<in> A"
  thus "\<exists>y. \<langle>x, y\<rangle> \<in> f" using uniq_val by blast

  show "\<And>y y'. \<lbrakk>\<langle>x, y\<rangle> \<in> f; \<langle>x, y'\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y = y'" using uniq_val asm by auto
qed

(* LCP: Conclusion is flexible -- use rule_tac or else FunctionE' below! *)
lemma FunctionE [elim]:
  assumes "f \<in> \<Prod>x \<in> A. (B x)" and "x \<in> A"
  shows "f`x \<in> B x"
proof -
  from assms function_mems have "\<langle>x, f`x\<rangle> \<in> f" by auto
  moreover have "f \<subseteq> \<Sum>x \<in> A. (B x)" using assms(1) unfolding Function_def by auto
  ultimately show "f`x \<in> B x" by auto
qed

(* LCP: This version is acceptable to the simplifer *)
lemma FunctionE' [elim]: "\<lbrakk>f \<in> A \<rightarrow> B; a \<in> A\<rbrakk> \<Longrightarrow> f`a \<in> B"
  by (fact FunctionE)

lemma empty_function [intro]: "{} \<in> {} \<rightarrow> B"
  by auto

lemma empty_function_iff [iff]: "f \<in> {} \<rightarrow> B \<longleftrightarrow> f = {}"
  unfolding Function_def by auto

lemma singleton_functionI [intro]: "y \<in> B \<Longrightarrow> {\<langle>x, y\<rangle>} \<in> {x} \<rightarrow> B"
  unfolding Function_def by auto

lemma lambda_function [intro]: "(\<lambda>x \<in> A. b x) \<in> A \<rightarrow> {b x | x \<in> A}"
  unfolding lambda_def Function_def by auto

lemma apply_function [simp]: "\<lbrakk>\<langle>x, y\<rangle> \<in> f; f \<in> \<Prod>x \<in> A. (B x)\<rbrakk> \<Longrightarrow> f`x = y"
  using apply_def FunctionE by auto

lemma apply_to_fst:
  assumes "f \<in> \<Prod>x \<in> A. (B x)" and "p \<in> f"
  shows "f`(fst p) = snd p"
proof -
  have "fst p \<in> A" using function_rel[OF assms(1)] assms(2) by auto
  hence "\<langle>fst p, f`(fst p)\<rangle> \<in> f" using assms function_mems by auto
  moreover have "\<langle>fst p, snd p\<rangle> \<in> f" using assms unfolding Function_def by auto
  ultimately show "f`(fst p) = snd p" using function_uniq_val assms by auto
qed

lemma function_opair:
  assumes "f \<in> \<Prod>x \<in> A. (B x)" and "p \<in> f"
  shows "\<langle>fst p, f ` fst p\<rangle> = p"
proof -
  have "p = \<langle>fst p, snd p\<rangle>"
    using function_rel[OF assms(1)] assms(2) prod_mem_conv
    by auto
  also have "\<langle>fst p, snd p\<rangle> = \<langle>fst p, f ` fst p\<rangle>" using assms apply_to_fst by auto
  finally show "\<langle>fst p, f ` fst p\<rangle> = p" by simp
qed

lemma function_graph: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f = {\<langle>x, f`x\<rangle> | x \<in> A}"
proof -
  assume f [simp]: "f \<in> \<Prod>x \<in> A. (B x)"
  then have f_subs: "f \<subseteq> A \<times> \<Union>{B x | x \<in> A}" by (rule function_rel)

  show "f = {\<langle>x, f`x\<rangle> | x \<in> A}"
  proof (rule equalityI2)
    fix p assume "p \<in> f"
    from function_opair[OF f this]
    have p: "p = \<langle>fst p, f ` fst p\<rangle>" by simp
    from f_subs `p \<in> f` have "fst p \<in> A" by auto
    then show "p \<in> {\<langle>x, f`x\<rangle> | x \<in> A}"
      by (subst p) auto
  next
    fix p assume "p \<in> {\<langle>x, f`x\<rangle> | x \<in> A}"
    then have p_eq: "p = \<langle>fst p, f`fst p\<rangle>" and fst_A: "fst p \<in> A" by auto
    then show "p \<in> f" by (subst p_eq) (rule function_mems[OF f])
  qed
qed

lemma function_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> \<Prod>x \<in> A. (B x) = \<Prod>x \<in> A'. (B' x)"
  by (simp add: Function_def cong: Pair_cong)

lemma function_fst [elim]: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> fst p \<in> A"
  unfolding Function_def by auto

lemma function_snd [elim]: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> snd p \<in> B (fst p)"
  unfolding Function_def by auto

lemma function_opair_fst: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<langle>a, b\<rangle> \<in> f\<rbrakk> \<Longrightarrow> a \<in> A"
  unfolding Function_def by auto

lemma function_empty_iff [iff]: "f \<in> \<Prod>x \<in> {}. (B x) \<longleftrightarrow> f = {}"
  unfolding Function_def by auto

(* Is [dest] needed here? *)
lemma function_subset_Pair [dest]:
  "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f \<subseteq> \<Sum>x \<in> A. (B x)"
  unfolding Function_def by auto

(* Or here? *)
lemma function_forget [dest]:
  "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f \<in> A \<rightarrow> (\<Union>x \<in> A. B x)"
  unfolding Function_def by auto

lemma function_refine:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x\<rbrakk> \<Longrightarrow> f \<in> \<Prod>x \<in> A. (C x)"
proof (rule FunctionI, auto)
  assume assms: "f \<in> \<Prod>x \<in> A. (B x)" "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x"

  { fix p assume p_elem: "p \<in> f"
    show "p \<in> A \<times> (\<Union>x \<in> A. C x)"
    apply (intro PairI2)
    apply (auto intro: assms(1) p_elem function_opair function_fst sym)
    proof rule+
      show "fst p \<in> A" using assms(1) p_elem by auto
      thus "f`(fst p) \<in> C (fst p)" using assms(2) by auto
    qed simp
  }

  fix x assume "x \<in> A"
  thus "\<exists>y. \<langle>x, y\<rangle> \<in> f" using assms(1) by (auto intro: function_mems ex1_implies_ex)
qed

corollary function_enlarge_rng:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x\<rbrakk> \<Longrightarrow> f \<in> \<Prod>x \<in> A. (C x)"
proof -
  assume assms: "f \<in> \<Prod>x \<in> A. (B x)" and "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x"
  hence "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x" by (auto intro: FunctionE)
  thus "f \<in> \<Prod>x \<in> A. (C x)" using function_refine assms by blast
qed

corollary function_enlarge_rng': "\<lbrakk>f \<in> A \<rightarrow> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> f \<in> A \<rightarrow> C"
  by (rule function_enlarge_rng)

(* LCP: Such functions arise in non-standard datatypes, ZF/ex/Ntree for instance *)
lemma function_collect_iff:
  "f \<in> \<Prod>x \<in> A. {y \<in> B x | P x y} \<longleftrightarrow> f \<in> \<Prod>x \<in> A. (B x) \<and> (\<forall>x \<in> A. P x (f`x))"
  by (auto intro: function_refine dest: FunctionE)

lemma function_lambdaI [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> b x \<in> B x) \<Longrightarrow> (\<lambda>x \<in> A. b x) \<in> \<Prod>x \<in> A. (B x)"
  unfolding Function_def using collect_relT by auto

lemma function_empty_dom' [simp]: "{} \<rightarrow> A = {{}}" by (rule extensionality) auto

lemma function_empty_rng' [simp]: "A \<rightarrow> {} = (if A = {} then {{}} else {})"
  by (auto simp: Function_def, rule extensionality, auto, rule, auto)

lemma function_singletons [simp]: "{a} \<rightarrow> {b} = {{\<langle>a, b\<rangle>}}"
proof (rule extensionality, auto)
  fix f assume asm: "f \<in> {a} \<rightarrow> {b}"
  with function_graph
  have "f = {\<langle>x, f`x\<rangle> | x \<in> {a}}" by auto
  hence 1: "f = {\<langle>a, f`a\<rangle>}" using Repl_singleton by auto
  have "a \<in> {a}" by auto
  hence 2: "f`a \<in> {b}" using asm FunctionE by blast
  from 1 2 show "f = {\<langle>a, b\<rangle>}" by simp
qed

lemma Function_empty_iff' [iff]: "A \<rightarrow> X = {} \<longleftrightarrow> X = {} \<and> A \<noteq> {}"
proof auto
  assume "A \<rightarrow> X = {}" hence "A \<noteq> {}" by auto
  { assume "X \<noteq> {}"
    then obtain c where "c \<in> X" using \<open>A \<noteq> {}\<close> by blast
    hence "(\<lambda>x \<in> A. c) \<in> A \<rightarrow> X" by auto
    with \<open>A \<rightarrow> X = {}\<close> have False by auto
  }
  thus "X = {}" by auto
qed


subsection \<open>Function extensionality\<close>

lemma extend_function:
  assumes
    "f \<in> \<Prod>x \<in> A. (B x)" "g \<in> \<Prod>x \<in> C. (D x)"
    "A \<subseteq> C"
    "\<And>x. x \<in> A \<Longrightarrow> f`x = g`x"
  shows "f \<subseteq> g"
proof
  fix p assume asm: "p \<in> f"
  hence p_comp: "\<langle>fst p, f`(fst p)\<rangle> = p"
    using function_opair assms(1) by auto

  have p_mem_A: "fst p \<in> A" using asm assms(1) by auto
  hence eq: "g`(fst p) = f`(fst p)" using assms(4) by auto

  from assms(3) p_mem_A have p_mem_C: "fst p \<in> C" ..
  hence "\<langle>fst p, g`(fst p)\<rangle> \<in> g" using function_mems[OF assms(2)] by auto
  with eq p_comp show "p \<in> g" by auto
qed

lemma function_extensionality:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); g \<in> \<Prod>x \<in> A. (C x); \<And>x. x \<in> A \<Longrightarrow> f`x = g`x\<rbrakk> \<Longrightarrow> f = g"
  apply (rule extensionality)
  using extend_function[where ?A=A and ?C=A] subset_refl by auto

lemma eta [simp]: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> (\<lambda>x \<in> A. (f`x)) = f"
  by (auto intro: function_extensionality)

lemma function_extensionality_iff:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); g \<in> \<Prod>x \<in> A. (C x)\<rbrakk> \<Longrightarrow> (\<forall>a \<in> A. f`a = g`a) \<longleftrightarrow> f = g"
  by (auto intro: function_extensionality)

(* LCP: thm by Mark Staples, proof by lcp *)
lemma extend_function_eq:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); g \<in> \<Prod>x \<in> A. (C x)\<rbrakk> \<Longrightarrow> f \<subseteq> g \<longleftrightarrow> (f = g)"
  by (blast dest: function_mems intro: function_extensionality apply_function[symmetric])

(* LCP: Every element of (Function A B) may be expressed as a lambda abstraction! *)
lemma function_lambdaE:
  assumes
    major: "f \<in> \<Prod>x \<in> A. (B x)" and
    minor: "\<And>b. \<lbrakk>\<forall>x \<in> A. b x \<in> B x; f = (\<lambda>x \<in> A. b x)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  apply (rule minor)
  apply (rule_tac [2] eta[symmetric])
  apply (blast intro: major FunctionE)+
  apply fact
  done


subsection \<open>Soft typing\<close>

lemma lambda_simple_type [type]:
  "lambda : (A : set) \<Rightarrow> (element A \<Rightarrow> element B) \<Rightarrow> element (A \<rightarrow> B)"
  by squash_types auto

lemma apply_simple_type [type]:
  "(`) : element (A \<rightarrow> B) \<Rightarrow> element A \<Rightarrow> element B"
  by squash_types auto


(* text \<open>Class of all functions\<close>

definition uniq_valued :: "set \<Rightarrow> bool"
  where "uniq_valued R \<equiv> \<forall>x y y'. \<langle>x, y\<rangle> \<in> R \<and> \<langle>x, y'\<rangle> \<in> R \<longrightarrow> y = y'"

definition function :: "set type"
  where function_typedef: "function \<equiv> uniq_valued \<cdot> relation"

definition total :: "set \<Rightarrow> set \<Rightarrow> bool" ("(_-total)" [1000])
  where "A-total \<equiv> \<lambda>f. dom f = A"

lemma Function_relation_type [elim]: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f : relation"
  by (drule function_rel, drule relations_relation_type) squash_types

lemma Function_function_type [elim]: "f \<in> Function A B \<Longrightarrow> f : A-total \<cdot> function"
  unfolding function_typedef uniq_valued_def total_def adjective_def
  by squash_types auto

lemma functions_function_type [elim]: "f \<in> A \<rightarrow> B \<Longrightarrow> f : A-total \<cdot> B-valued \<cdot> function"
  unfolding function_typedef uniq_valued_def total_def valued_def adjective_def
  by (squash_types, auto) (insert range_subset, blast)
*)


end
