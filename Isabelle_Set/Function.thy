(*
Title:   Function.thy
Authors: Alexander Krauss and Joshua Chen
Date:    Jun 2019

Based on earlier work in Isabelle/ZF by Larry Paulson.
*)

section \<open>Functions, lambda abstraction, and dependent function spaces\<close>

theory Function
imports Relation

begin

subsection \<open>Function spaces\<close>

text \<open>...formulated dependently.\<close>

definition Pi :: "[set, set \<Rightarrow> set] \<Rightarrow> set"
  where "Pi A B \<equiv> {f \<in> Pow (\<Coprod>x \<in> A. (B x)) | \<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f}"

syntax "_PROD" :: "[pttrn, set, set] => set type" ("(3\<Prod>_ \<in> _./ _)" [0, 0, 100])
translations "\<Prod>x \<in> A. B" \<rightleftharpoons> "CONST Pi A (\<lambda>x. B)"

abbreviation "nondep_functions" :: "[set, set] \<Rightarrow> set" (infixr "\<rightarrow>" 60)
  where "A \<rightarrow> B \<equiv> \<Prod>x \<in> A. B"


subsection \<open>Lambda abstraction and application\<close>

definition Lambda :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "Lambda A b \<equiv> {\<langle>x, b x\<rangle> | x \<in> A}"

syntax "_lam" :: "[pttrn, set, set] => set" ("(3\<lambda>_ \<in> _./ _)" 200)
translations "\<lambda>x \<in> A. f" \<rightleftharpoons> "CONST Lambda A (\<lambda>x. f)"

definition "apply" :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "`" 90)
  where "f`x = (THE y. \<langle>x, y\<rangle> \<in> f)"


lemma LambdaI [intro]: "a \<in> A \<Longrightarrow> \<langle>a, b a\<rangle> \<in> \<lambda>x \<in> A. b x"
  unfolding Lambda_def by auto

lemma LambdaE [elim]: "\<lbrakk>p \<in> \<lambda>x \<in> A. b x; \<And>x. \<lbrakk>x \<in> A; p = \<langle>x, b x\<rangle>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: Lambda_def, blast)

lemma LambdaD [dest]: "\<lbrakk>\<langle>a, c\<rangle> \<in> \<lambda>x \<in> A. b x\<rbrakk> \<Longrightarrow> c = b a"
  by auto

lemma beta [simp]: "a \<in> A \<Longrightarrow> (\<lambda>x \<in> A. b x) ` a = b a"
  by (auto simp: Lambda_def apply_def)

lemma Lambda_domain [simp]: "domain (\<lambda>x \<in> A. b x) = A"
  by (auto simp: Lambda_def)

lemma Lambda_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> b x = b' x\<rbrakk> \<Longrightarrow> (\<lambda>x \<in> A. b x) = \<lambda>x \<in> A'. b' x"
  by (simp only: Lambda_def cong add: Repl_cong)

lemma Lambda_eqE: "\<lbrakk>(\<lambda>x \<in> A. f x) = \<lambda>x \<in> A. g x; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
  by (auto elim: equalityE)


subsection \<open>Rules for functions\<close>

lemma functions_are_relations [elim]: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f \<in> relations A (\<Union>x \<in> A. (B x))"
  unfolding Pi_def by auto

text \<open>The following lemmas are useful.\<close>

lemma uniq_val_imp: "\<lbrakk>\<exists>!y. \<langle>x, y\<rangle> \<in> f; x \<in> A\<rbrakk> \<Longrightarrow> \<langle>x, f`x\<rangle> \<in> f"
proof -
  assume ex: "\<exists>!y. \<langle>x, y\<rangle> \<in> f" and "x \<in> A"
  then obtain y where elem: "\<langle>x, y\<rangle> \<in> f" by auto
  with ex have "f`x = y" using apply_def by auto
  with elem show "\<langle>x, f`x\<rangle> \<in> f" by simp
qed

lemma function_elems: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); x \<in> A\<rbrakk> \<Longrightarrow> \<langle>x, f`x\<rangle> \<in> f"
  unfolding Pi_def
  by (drule CollectD2, drule Bspec, auto intro: uniq_val_imp)

lemma function_domain [elim]:
  "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> domain f = A"
apply ((rule extensionality domain_subset functions_are_relations)+, auto)
proof (simp only: Pi_def, drule CollectD2)
  fix x assume "x \<in> A" and "\<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f"
  then obtain y where "\<langle>x, y\<rangle> \<in> f" by auto
  thus "x \<in> domain f" using domainI by auto
qed

lemma function_uniq_val [elim]:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<langle>x, y\<rangle> \<in> f; \<langle>x, y'\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y = y'"
unfolding Pi_def by auto

lemma function_fibered: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y \<in> B x"
  unfolding Pi_def by auto

lemma functionI [intro]:
  assumes
    f_relation: "f \<in> relations A (\<Union>x \<in> A. (B x))" and
    uniq_val: "\<And>x. x \<in> A \<Longrightarrow> \<exists>!y. \<langle>x, y\<rangle> \<in> f" and
    stratified: "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> B x"
  shows "f \<in> \<Prod>x \<in> A. (B x)"
unfolding Pi_def proof (auto, rule DUnionI2)
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

(* LCP: Conclusion is flexible -- use rule_tac or else nondep_functionE below! *)
lemma functionE:
  assumes "f \<in> \<Prod>x \<in> A. (B x)" and "x \<in> A"
  shows "f`x \<in> B x"
proof -
  from assms function_elems have "\<langle>x, f`x\<rangle> \<in> f" by auto
  moreover have "f \<subseteq> \<Coprod>x \<in> A. (B x)" using assms(1) unfolding Pi_def by auto
  ultimately show "f`x \<in> B x" by auto
qed

(* LCP: This version is acceptable to the simplifer *)
lemma nondep_functionE: "\<lbrakk>f \<in> A \<rightarrow> B; a \<in> A\<rbrakk> \<Longrightarrow> f`a \<in> B"
  by (fact functionE)


lemma empty_function [intro]: "{} \<in> {} \<rightarrow> B"
  by auto

lemma empty_function_iff [iff]: "f \<in> {} \<rightarrow> B \<longleftrightarrow> f = {}"
  unfolding Pi_def by auto

lemma singleton_functionI [intro]: "y \<in> B \<Longrightarrow> {\<langle>x, y\<rangle>} \<in> {x} \<rightarrow> B"
  unfolding Pi_def by auto

lemma Lambda_function [intro]: "(\<lambda>x \<in> A. b x) \<in> A \<rightarrow> {b x | x \<in> A}"
  unfolding Lambda_def Pi_def by auto

lemma function_apply_conv [simp]: "\<lbrakk>\<langle>x, y\<rangle> \<in> f; f \<in> \<Prod>x \<in> A. (B x)\<rbrakk> \<Longrightarrow> f`x = y"
  using apply_def functionE by auto

lemma function_val_conv:
  assumes "f \<in> \<Prod>x \<in> A. (B x)" and "p \<in> f"
  shows "f`(fst p) = snd p"
proof -
  have "fst p \<in> A" using functions_are_relations[OF assms(1)] assms(2) by auto
  hence "\<langle>fst p, f`(fst p)\<rangle> \<in> f" using assms function_elems by auto
  moreover have "\<langle>fst p, snd p\<rangle> \<in> f" using assms unfolding Pi_def by auto
  ultimately show "f`(fst p) = snd p" using function_uniq_val assms by auto
qed

lemma function_elems_conv [simp]:
  assumes "f \<in> \<Prod>x \<in> A. (B x)" and "p \<in> f"
  shows "\<langle>fst p, f ` fst p\<rangle> = p"
proof -
  have "p = \<langle>fst p, snd p\<rangle>"
    using functions_are_relations[OF assms(1)] assms(2) relation_elem_conv
    by auto
  also have "\<langle>fst p, snd p\<rangle> = \<langle>fst p, f ` fst p\<rangle>" using assms function_val_conv by auto
  finally show "\<langle>fst p, f ` fst p\<rangle> = p" by simp
qed

lemma function_graph: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f = {\<langle>x, f`x\<rangle> | x \<in> A}"
  by (extensionality, rule,
    auto dest: functions_are_relations intro: relations_fst function_elems)

lemma Pi_cong [cong]: "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> \<Prod>x \<in> A. (B x) = \<Prod>x \<in> A'. (B' x)"
  by (simp add: Pi_def cong: DUnion_cong)

lemma function_fst [elim]: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> fst p \<in> A"
  unfolding Pi_def by auto

lemma function_snd [elim]: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> snd p \<in> B (fst p)"
  unfolding Pi_def by auto

lemma function_pair_fst: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<langle>a, b\<rangle> \<in> f\<rbrakk> \<Longrightarrow> a \<in> A"
  unfolding Pi_def by auto

lemma function_empty_iff [iff]: "f \<in> \<Prod>x \<in> {}. (B x) \<longleftrightarrow> f = {}"
  unfolding Pi_def by auto

lemma function_carrier [dest]: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f \<subseteq> \<Coprod>x \<in> A. (B x)"
  unfolding Pi_def by auto

lemma function_forget [dest]: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f \<in> A \<rightarrow> \<Union>x \<in> A. (B x)"
  unfolding Pi_def by auto

lemma function_refine: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x\<rbrakk> \<Longrightarrow> f \<in> \<Prod>x \<in> A. (C x)"
proof (rule functionI; auto)
  assume assms: "f \<in> \<Prod>x \<in> A. (B x)" "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x"

  { fix p assume p_elem: "p \<in> f"
    show "p \<in> A \<times> \<Union>x \<in> A. (C x)"
    apply (intro DUnionI2)
    apply (auto intro: assms(1) p_elem function_elems_conv function_fst sym)
    proof rule+
      show "fst p \<in> A" using assms(1) p_elem by auto
      thus "f`(fst p) \<in> C (fst p)" using assms(2) by auto
    qed simp
  }

  fix x assume "x \<in> A"
  thus "\<exists>y. \<langle>x, y\<rangle> \<in> f" using assms(1) by (auto intro: function_elems ex1_implies_ex)
qed

corollary function_enlarge_range:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x\<rbrakk> \<Longrightarrow> f \<in> \<Prod>x \<in> A. (C x)"
proof -
  assume assms: "f \<in> \<Prod>x \<in> A. (B x)" and "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x"
  hence "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x" by (auto intro: functionE)
  thus "f \<in> \<Prod>x \<in> A. (C x)" using function_refine assms by blast
qed

corollary nondep_function_enlarge_range: "\<lbrakk>f \<in> A \<rightarrow> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> f \<in> A \<rightarrow> C"
  by (rule function_enlarge_range)

(* LCP: Such functions arise in non-standard datatypes, ZF/ex/Ntree for instance *)
lemma function_Collect_iff:
  "f \<in> \<Prod>x \<in> A. {y \<in> B x | P x y} \<longleftrightarrow> f \<in> \<Prod>x \<in> A. (B x) \<and> (\<forall>x \<in> A. P x (f`x))"
  by (auto intro: function_refine dest: functionE)

lemma function_LambdaI [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> b x \<in> B x) \<Longrightarrow> (\<lambda>x \<in> A. b x) \<in> \<Prod>x \<in> A. (B x)"
  unfolding Pi_def using Collect_relation by auto

lemma function_empty_domain [simp]: "{} \<rightarrow> A = {{}}" by extensionality

lemma function_empty_range [simp]: "A \<rightarrow> {} = (if A = {} then {{}} else {})"
  by (auto simp: Pi_def, extensionality, rule, auto)

lemma singleton_function_conv [simp]: "{a} \<rightarrow> {b} = {{\<langle>a, b\<rangle>}}"
proof extensionality
  fix f assume asm: "f \<in> {a} \<rightarrow> {b}"
  with function_graph
  have "f = {\<langle>x, f`x\<rangle> | x \<in> {a}}" by auto
  hence 1: "f = {\<langle>a, f`a\<rangle>}" using Repl_singleton by auto
  have "a \<in> {a}" by auto
  hence 2: "f`a \<in> {b}" using asm functionE by blast
  from 1 2 show "f = {\<langle>a, b\<rangle>}" by simp
qed

lemma nondep_fs_empty_iff [iff]: "A \<rightarrow> X = {} \<longleftrightarrow> X = {} \<and> A \<noteq> {}"
proof auto
  assume "A \<rightarrow> X = {}" hence "A \<noteq> {}" by auto
  { assume "X \<noteq> {}"
    then obtain c where "c \<in> X" using \<open>A \<noteq> {}\<close> by blast
    hence "(\<lambda>x \<in> A. c) \<in> A \<rightarrow> X" by stauto
    with \<open>A \<rightarrow> X = {}\<close> have False by auto
  }
  thus "X = {}" by auto
qed


subsection \<open>Function extensionality\<close>

lemma function_subset:
  assumes
    "f \<in> \<Prod>x \<in> A. (B x)" "g \<in> \<Prod>x \<in> C. (D x)"
    "A \<subseteq> C"
    "\<And>x. x \<in> A \<Longrightarrow> f`x = g`x"
  shows "f \<subseteq> g"
proof
  fix p assume asm: "p \<in> f"
  hence p_comp: "\<langle>fst p, f`(fst p)\<rangle> = p"
    using function_elems_conv assms(1) by auto

  have p_elem_A: "fst p \<in> A" using asm assms(1) by auto
  hence eq: "g`(fst p) = f`(fst p)" using assms(4) by auto

  from assms(3) p_elem_A have p_elem_C: "fst p \<in> C" ..
  hence "\<langle>fst p, g`(fst p)\<rangle> \<in> g" using function_elems[OF assms(2)] by auto
  with eq p_comp show "p \<in> g" by auto
qed

lemma funext:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); g \<in> \<Prod>x \<in> A. (C x); \<And>x. x \<in> A \<Longrightarrow> f`x = g`x\<rbrakk> \<Longrightarrow> f = g"
  apply (rule extensionality)
  using function_subset[where ?A=A and ?C=A] subset_refl by auto

lemma eta [simp]: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> (\<lambda>x \<in> A. (f`x)) = f"
  by (auto intro: funext)

lemma funext_iff:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); g \<in> \<Prod>x \<in> A. (C x)\<rbrakk> \<Longrightarrow> (\<forall>a \<in> A. f`a = g`a) \<longleftrightarrow> f = g"
  by (auto intro: funext)

(* LCP: thm by Mark Staples, proof by lcp *)
lemma function_subset_eq: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); g \<in> \<Prod>x \<in> A. (C x)\<rbrakk> \<Longrightarrow> f \<subseteq> g \<longleftrightarrow> (f = g)"
  by (blast dest: function_elems intro: funext function_apply_conv[symmetric])


(* LCP: Every element of (Pi A B) may be expressed as a lambda abstraction! *)
lemma function_LambdaE:
  assumes
    major: "f \<in> \<Prod>x \<in> A. (B x)" and
    minor: "\<And>b. \<lbrakk>\<forall>x \<in> A. b x \<in> B x; f = (\<lambda>x \<in> A. b x)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  apply (rule minor)
  apply (rule_tac [2] eta[symmetric])
  apply (blast intro: major functionE)+
  apply fact
  done


end
