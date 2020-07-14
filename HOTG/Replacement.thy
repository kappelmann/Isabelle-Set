section \<open>Replacement\<close>

theory Replacement
imports
  Bounded_Quantifiers
  Equality
begin

section \<open>Replacement\<close>

syntax
  "_repl" :: \<open>[set, pttrn, set] => set\<close> ("(1{_ ./ _ \<in> _})")
  "_repl" :: \<open>[set, pttrn, set] => set\<close> ("(1{_ |/ _ \<in> _})")
translations
  "{y | x \<in> A}" \<rightleftharpoons> "CONST repl A (\<lambda>x. y)"
  "{y . x \<in> A}" \<rightharpoonup> "CONST repl A (\<lambda>x. y)"

lemma replI: "a \<in> A \<Longrightarrow> f a \<in> {f x. x \<in> A}"
  by (unfold replacement) auto

(*LP: Useful for coinduction proofs*)
lemma RepFun_eqI [intro]: "\<lbrakk>b = f a; a \<in> A\<rbrakk> \<Longrightarrow> b \<in> {f x. x \<in> A}"
  apply (erule ssubst)
  apply (erule replI)
  done

(*The converse of the above*)
lemma replD:  "b \<in> {f x | x \<in> A} \<Longrightarrow> \<exists>a \<in> A. b = f a"
  by auto

lemma replE [elim!]:
  "\<lbrakk>b \<in> {f x. x \<in> A}; \<And>x. \<lbrakk>x \<in> A; b = f x\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma repl_cong [cong]:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> {f x. x \<in> A} = {g x. x \<in> B}"
  by (rule extensionality) auto

lemma repl_comp [simp]: "{g b | b \<in> {f a | a \<in> A}} = {g (f a) | a \<in> A}"
  by (rule extensionality) auto

lemma repl_triv [simp]: "{x. x \<in> A} = A"
  by (rule extensionality) auto

lemma repl_empty [simp]: "{f x. x \<in> {}} = {}"
  by (rule extensionality) auto

lemma repl_is_empty [iff]: "{f x. x \<in> A} = {} \<longleftrightarrow> A = {}"
  by (auto dest: equalityD intro!: equalityI')


end
