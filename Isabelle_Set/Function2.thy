(*
Title:   Function2.thy
Authors: Alexander Krauss and Joshua Chen
Date:    Jun 2019

Based on earlier work in Isabelle/ZF by Larry Paulson.
*)

section \<open>Functions, lambda abstraction, and dependent function spaces\<close>

theory Function2
imports Relations

begin

subsection \<open>Function soft type\<close>

definition function :: "[set, set] \<Rightarrow> set type" (infixr "\<rightarrow>" 60)
  where function_typedef:
  "A \<rightarrow> B \<equiv>
      relation A B
    \<bar> Type (\<lambda>f. domain f = A \<and> (\<forall>x y y'. \<langle>x, y\<rangle> \<in> f \<and> \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y'))"

lemma function_type_iff [iff_st]:
  "f : A \<rightarrow> B \<longleftrightarrow>
    f : relation A B \<and> domain f = A \<and> (\<forall>x y y'. \<langle>x, y\<rangle> \<in> f \<and> \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y')"
  using function_typedef by stauto

lemma function_typeI [intro_st]:
  assumes
    "f: relation A B"
    "domain f = A"
    "\<And>x y y'. \<lbrakk>\<langle>x, y\<rangle> \<in> f; \<langle>x, y'\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y = y'"
  shows "f : A \<rightarrow> B"
  using assms function_type_iff by auto

lemma function_type_iff_ex1:
  "f : A \<rightarrow> B \<longleftrightarrow> f : relation A B \<and> (\<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f)"
proof auto
  assume f_fun: "f : A \<rightarrow> B"
  thus f_rel: "f : relation A B" by stauto

  fix x assume asm: "x \<in> A"
  have "domain f = A" using f_fun by stauto
  hence "x \<in> domain f" using asm by simp
  thus "\<exists>y. \<langle>x, y\<rangle> \<in> f" using f_rel by (intro domainE)

  fix y y' assume "\<langle>x, y\<rangle> \<in> f" and "\<langle>x, y'\<rangle> \<in> f"
  thus "y = y'" using f_fun function_type_iff by auto
next
  assume f_rel: "f : relation A B" and uniq: "\<forall>x \<in> A. \<exists>!y. \<langle>x, y\<rangle> \<in> f"
  hence "\<forall>x \<in> A. (\<exists>y. \<langle>x, y\<rangle> \<in> f)" by auto
  hence "A \<subseteq> domain f" using f_rel by (auto intro: domainI)
  moreover have "domain f \<subseteq> A" using f_rel domain_subset by auto
  ultimately have "domain f = A" by extensionality
  thus "f : A \<rightarrow> B" using f_rel uniq by stauto
qed

lemma function_domainE [elim]: "\<lbrakk>f : A \<rightarrow> B; x \<in> A\<rbrakk> \<Longrightarrow> \<exists>!y. \<langle>x, y\<rangle> \<in> f"
  using function_type_iff_ex1 by auto

lemma function_uniq_val [elim]: "\<lbrakk>f : A \<rightarrow> B; \<langle>x, y\<rangle> \<in> f; \<langle>x, y'\<rangle> \<in> f\<rbrakk> \<Longrightarrow> y = y'"
  using function_type_iff by auto

lemma function_is_relation [subtype]: "A \<rightarrow> B \<prec> relation A B"
  by stauto

lemma empty_function [intro]: "{} : {} \<rightarrow> B"
  by stauto

lemma empty_function_iff [iff]: "f : {} \<rightarrow> B \<longleftrightarrow> f = {}"
  by stauto

lemma singleton_function [intro]: "y \<in> B \<Longrightarrow> {\<langle>x, y\<rangle>} : {x} \<rightarrow> B"
  by stauto


subsection \<open>Lambda abstraction and application\<close>

definition Lambda :: "set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set"
  where "Lambda A b \<equiv> {\<langle>x, b x\<rangle>. x \<in> A}"

syntax "_lam" :: "[pttrn, set, set] => set" ("(3\<lambda>_ \<in> _./ _)" 200)
translations "\<lambda>x \<in> A. f" \<rightleftharpoons> "CONST Lambda A (\<lambda>x. f)"

definition "apply" :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "`" 90)
  where "f`x = (THE y. \<langle>x, y\<rangle> \<in> f)"


lemma Lambda_elemI [intro]: "a \<in> A \<Longrightarrow> \<langle>a, b a\<rangle> \<in> \<lambda>x \<in> A. b x"
  unfolding Lambda_def by auto

lemma Lambda_elemE [elim]: "\<lbrakk>p \<in> \<lambda>x \<in> A. b x; \<And>x. \<lbrakk>x \<in> A; p = \<langle>x, b x\<rangle>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (simp add: Lambda_def, blast)

lemma Lambda_elemD [dest]: "\<lbrakk>\<langle>a, c\<rangle> \<in> \<lambda>x \<in> A. b x\<rbrakk> \<Longrightarrow> c = b a"
  by auto

lemma Lambda_function [intro_st]: "(\<lambda>x \<in> A. b x) : A \<rightarrow> {b x | x \<in> A}"
  unfolding Lambda_def by stauto

lemma beta [simp]: "a \<in> A \<Longrightarrow> (\<lambda>x \<in> A. b x) ` a = b a"
  by (auto simp: Lambda_def apply_def)

lemma Lambda_domain [simp]: "domain(\<lambda>x \<in> A. b x) = A"
  by (auto simp: Lambda_def)

lemma Lambda_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> b x = b' x\<rbrakk> \<Longrightarrow> (\<lambda>x \<in> A. b x) = \<lambda>x \<in> A'. b' x"
  by (simp only: Lambda_def cong add: Repl_cong)

lemma Lambda_eqE: "\<lbrakk>(\<lambda>x \<in> A. f x) = \<lambda>x \<in> A. g x; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
  by (auto elim: equalityE)


lemma function_apply_conv [simp]: "\<lbrakk>f : A \<rightarrow> B; \<langle>x, y\<rangle> \<in> f\<rbrakk> \<Longrightarrow> f`x = y"
  using apply_def function_domainE by stauto

lemma function_elemI [intro]: "\<lbrakk>f : A \<rightarrow> B; x \<in> A\<rbrakk> \<Longrightarrow> \<langle>x, f`x\<rangle> \<in> f"
proof -
  assume asm: "f : A \<rightarrow> B" and "x \<in> A"
  then obtain y where "\<langle>x, y\<rangle> \<in> f" using function_domainE by blast
  thus "\<langle>x, f`x\<rangle> \<in> f" using asm by auto
qed

lemma function_elems_conv [simp]: "\<lbrakk>f : A \<rightarrow> B; p \<in> f\<rbrakk> \<Longrightarrow> p = \<langle>fst p, f ` fst p\<rangle>"
proof -
  assume assms: "f : A \<rightarrow> B" "p \<in> f"
  hence *: "\<langle>fst p, snd p\<rangle> \<in> f" by stauto
  have "p = \<langle>fst p, snd p\<rangle>" using assms by stauto
  also have "\<langle>fst p, snd p\<rangle> = \<langle>fst p, f ` fst p\<rangle>" using assms * by auto
  finally show "p = \<langle>fst p, f ` fst p\<rangle>" by simp
qed

lemma function_graph: "f : A \<rightarrow> B \<Longrightarrow> f = {\<langle>x, f`x\<rangle> | x \<in> A}"
  by (extensionality, rule, auto, insert DUnion_fst, stauto+)

lemma function_typeE [elim]: "\<lbrakk>f : A \<rightarrow> B; x \<in> A\<rbrakk> \<Longrightarrow> f`x \<in> B"
proof -
  assume assms: "f : A \<rightarrow> B" "x \<in> A"
  hence uniq: "\<exists>!y. \<langle>x, y\<rangle> \<in> f"
    using function_domainE by auto
  then obtain y where "\<langle>x, y\<rangle> \<in> f" and "y \<in> B"
    using assms rangeI range_subset by stauto
  hence "f`x = y" using apply_def uniq by auto
  with \<open>y \<in> B\<close> show "f`x \<in> B" by auto
qed


subsection \<open>Function spaces\<close>

text \<open>We formulate function spaces dependently.\<close>

definition Pi :: "[set, set \<Rightarrow> set] \<Rightarrow> set"
  where "Pi A B \<equiv> {f \<in> Pow (\<Coprod>x \<in> A. (B x)) | f : A \<rightarrow> (\<Union>x \<in> A. (B x))}"

syntax "_PROD" :: "[pttrn, set, set] => set" ("(3\<Prod>_ \<in> _./ _)" [0, 0, 100])
translations "\<Prod>x \<in> A. B" \<rightleftharpoons> "CONST Pi A (\<lambda>x. B)"


text \<open>Nondependent function spaces:\<close>

abbreviation fun :: "set \<Rightarrow> set \<Rightarrow> set" (infixr "\<rightarrow>" 60)
  where "A \<rightarrow> B \<equiv> Pi A (\<lambda>_. B)"

lemma fun_function_iff [iff]: "f \<in> A \<rightarrow> B \<longleftrightarrow> f : A \<rightarrow> B"
  unfolding Pi_def by stauto


lemma PiE [intro]:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); x \<in> A\<rbrakk> \<Longrightarrow> f`x \<in> B x"
  unfolding Pi_def by auto

lemma funE: "\<lbrakk>f \<in> A \<rightarrow> B; a \<in> A\<rbrakk> \<Longrightarrow> f`a \<in> B"
  by (fact PiE)

lemma Pi_type_iff [iff_st]:
  "f \<in> \<Prod>x \<in> A. (B x) \<longleftrightarrow> f : A \<rightarrow> (\<Union>x \<in> A. (B x)) \<and> (\<forall>x \<in> A. f`x \<in> B x)"
proof (auto simp: Pi_def)
  assume
  f_fun: "f : A \<rightarrow> (\<Union>x \<in> A. (B x))" and
  f_stratified: "\<forall>x \<in> A. f`x \<in> B x"

  fix p assume p_elem: "p \<in> f"
  show "p \<in> \<Coprod>x \<in> A. (B x)"
  proof (rule DUnionI2)
    show "p = \<langle>fst p, f ` fst p\<rangle>" using p_elem f_fun by auto
    show "fst p \<in> A" using p_elem f_fun by stauto
    thus "f ` fst p \<in> B (fst p)" using f_stratified by auto
  qed
qed

lemma PiI [intro]: "\<lbrakk>f : A \<rightarrow> (\<Union>x \<in> A. (B x)); \<And>x. x \<in> A \<Longrightarrow> f`x \<in> B x\<rbrakk> \<Longrightarrow> f \<in> \<Prod>x \<in> A. (B x)"
  by stauto

lemma Pi_cong [cong]: "\<lbrakk>A = A'; \<And>x. x \<in> A \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> \<Prod>x \<in> A. (B x) = \<Prod>x \<in> A'. (B' x)"
  by (simp add: Pi_def cong: DUnion_cong)

lemma Pi_fst [elim]: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> fst p \<in> A"
  by stauto

lemma Pi_snd [elim]: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> snd p \<in> B (fst p)"
  using Pi_def by auto

lemma Pi_pair_fst: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<langle>a, b\<rangle> \<in> f\<rbrakk> \<Longrightarrow> a \<in> A"
  by stauto

lemma Pi_pair_snd: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<langle>a, b\<rangle> \<in> f\<rbrakk> \<Longrightarrow> b \<in> B a"
  by stauto

lemma Pi_apply_conv [simp]: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<langle>a, b\<rangle> \<in> f\<rbrakk> \<Longrightarrow> f`a = b"
  by stauto

lemma Pi_elemI [elim]: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); a \<in> A\<rbrakk> \<Longrightarrow> \<langle>a, f`a\<rangle> \<in> f"
  by stauto

lemma Pi_elems_conv [simp]: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); p \<in> f\<rbrakk> \<Longrightarrow> p = \<langle>fst p, f ` fst p\<rangle>"
  by stauto

lemma Pi_elem_iff: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> \<langle>a, b\<rangle> \<in> f \<longleftrightarrow> a \<in> A \<and> f`a = b"
  by stauto

lemma Pi_uniqueness: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<langle>a, b\<rangle> \<in> f; \<langle>a, c\<rangle> \<in> f\<rbrakk> \<Longrightarrow> b = c"
  by stauto

lemma Pi_empty_iff [iff]: "f \<in> \<Prod>x \<in> {}. (B x) \<longleftrightarrow> f = {}"
  by stauto

lemma Pi_carrier [dest]: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f \<subseteq> \<Coprod>x \<in> A. (B x)"
  using Pi_def by auto

lemma Pi_forget [dest]: "f \<in> \<Prod>x \<in> A. (B x) \<Longrightarrow> f : A \<rightarrow> \<Union>x \<in> A. (B x)"
  by stauto

lemma Pi_refine: "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x\<rbrakk> \<Longrightarrow> f \<in> \<Prod>x \<in> A. (C x)"
proof (rule; auto?)
  assume assms: "f \<in> \<Prod>x \<in> A. (B x)" "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x"
  show "f : A \<rightarrow> \<Union>x \<in> A. (C x)"
  proof (rule function_typeI, rule subset_typeI, auto)
    fix p assume "p \<in> f"
    hence 1: "p = \<langle>fst p, f ` fst p\<rangle>"
      and 2: "fst p \<in> A" using assms(1) by auto
    hence 3: "f ` fst p \<in> C (fst p)" using assms(2) by auto
    from 1 2 3 show "p \<in> A \<times> \<Union>x \<in> A. (C x)" by auto
  qed (insert assms(1), stauto, auto)
qed

corollary Pi_weaken:
  "\<lbrakk>f \<in> \<Prod>x \<in> A. (B x); \<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x\<rbrakk> \<Longrightarrow> f \<in> \<Prod>x \<in> A. (C x)"
proof -
  assume assms: "f \<in> \<Prod>x \<in> A. (B x)" and "\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x"
  hence "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> C x" by auto
  thus "f \<in> \<Prod>x \<in> A. (C x)" using Pi_refine assms by blast
qed

lemma fun_weaken: "\<lbrakk>f : A \<rightarrow> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> f : A \<rightarrow> C"
  by stauto

(* LCP: Such functions arise in non-standard datatypes, ZF/ex/Ntree for instance *)
lemma Pi_Collect_iff:
  "f \<in> \<Prod>x \<in> A. {y \<in> B x | P x y} \<longleftrightarrow> f \<in> \<Prod>x \<in> A. (B x) \<and> (\<forall>x \<in> A. P x (f`x))"
  by (auto, stauto) (blast intro: Pi_refine dest: PiE)

lemma Pi_LambdaI [intro]:
  "(\<And>x. x \<in> A \<Longrightarrow> b x \<in> B x) \<Longrightarrow> (\<lambda>x \<in> A. b x) \<in> \<Prod>x \<in> A. (B x)"
  using Pi_def Lambda_def Collect_relation by stauto

lemma fun_empty_domain [simp]: "{} \<rightarrow> A = {{}}" by extensionality

lemma Pi_empty_range [simp]: "A \<rightarrow> {} = (if A = {} then {{}} else {})"
  by auto (unfold Pi_def, blast)

lemma singleton_fun [simp]: "{a} \<rightarrow> {b} = {{\<langle>a, b\<rangle>}}"
proof extensionality
  fix f assume asm: "f : {a} \<rightarrow> {b}"
  with function_graph
  have "f = {\<langle>x, f`x\<rangle> | x \<in> {a}}" by auto
  hence 1: "f = {\<langle>a, f`a\<rangle>}" using Repl_singleton by auto
  have "a \<in> {a}" by auto
  hence 2: "f`a \<in> {b}" using asm function_typeE by blast
  from 1 2 show "f = {\<langle>a, b\<rangle>}" by simp
qed

lemma fun_empty_iff [iff]: "A \<rightarrow> X = {} \<longleftrightarrow> X = {} \<and> A \<noteq> {}"
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

(*

(*LCP: Semi-extensionality!*)

lemma fun_subset:
    "\<lbrakk>f \<in> Pi A B;  g \<in> Pi C D;  A\<subseteq>C;
        !!x. x \<in> A \<Longrightarrow> f`x = g`x      \<rbrakk> \<Longrightarrow> f\<subseteq>g"
by (force dest: Pi_memberD intro: apply_Pair)

lemma fun_extension:
    "\<lbrakk>f \<in> Pi A B; g \<in> Pi A D;
        !!x. x \<in> A \<Longrightarrow> f`x = g`x \<rbrakk> \<Longrightarrow> f=g"
by (blast del: subsetI intro: subset_refl sym fun_subset)

lemma eta [simp]: "f \<in> Pi A B \<Longrightarrow> (\<lambda>x\<in>A. f`x) = f"
apply (rule fun_extension)
apply (auto simp add: lam_type apply_type beta)
done

lemma fun_extension_iff:
     "\<lbrakk>f \<in> Pi A B; g \<in> Pi A C\<rbrakk> \<Longrightarrow> (\<forall>a\<in>A. f`a = g`a) \<longleftrightarrow> f=g"
by (blast intro: fun_extension)

(*thm by Mark Staples, proof by lcp*)
lemma fun_subset_eq: "\<lbrakk>f \<in> Pi A B; g \<in> Pi A C\<rbrakk> \<Longrightarrow> f \<subseteq> g \<longleftrightarrow> (f = g)"
by (blast dest: apply_Pair
          intro: fun_extension apply_equality [symmetric])


(*Every element of Pi(A,B) may be expressed as a lambda abstraction!*)
lemma Pi_lamE:
  assumes major: "f \<in> Pi A B"
      and minor: "!!b. \<lbrakk>\<forall>x\<in>A. b(x)\<in>B(x);  f = (\<lambda>x\<in>A. b(x))\<rbrakk> \<Longrightarrow> P"
  shows "P"
apply (rule minor)
apply (rule_tac [2] eta [symmetric])
apply (blast intro: major apply_type)+
done

*)


end
