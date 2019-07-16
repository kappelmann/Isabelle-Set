section \<open>Soft types for HOL\<close>

theory Soft_Types_HOL
imports
  HOL.HOL
  Implicit_Arguments
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"

begin

text \<open>This theory introduces a generic notion of soft types, based on HOL predicates.\<close>

declare[[eta_contract=false]]


subsection \<open>Basic definitions\<close>

text \<open>Soft types are just predicates, but expressed as a different type:\<close>

typedecl 'a type

axiomatization
  Type :: "('a \<Rightarrow> bool) \<Rightarrow> 'a type" and
  pred_of :: "'a type \<Rightarrow> 'a \<Rightarrow> bool"
where
  pred_of_type: "pred_of (Type t) \<equiv> t"

definition has_type :: "'a \<Rightarrow> 'a type \<Rightarrow> bool" (infix ":" 45)
  where "x : T \<equiv> pred_of T x"

lemma has_type_iff: "x : Type P \<longleftrightarrow> P x"
  unfolding has_type_def by (simp only: pred_of_type)


subsection \<open>Bounded quantifiers\<close>

definition Soft_Ball :: "'a type \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Soft_Ball A P \<equiv> (\<forall>x. x : A \<longrightarrow> P x)"

definition Soft_Bex :: "'a type \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Soft_Bex A P \<equiv> (\<exists>x. x : A \<and> P x)"

syntax
  "_Soft_Ball" :: "[pttrn, 'a type, bool] \<Rightarrow> bool"  ("(3\<forall>_ : _./ _)" 10)
  "_Soft_Bex"  :: "[pttrn, 'a type, bool] \<Rightarrow> bool"  ("(3\<exists>_ : _./ _)" 10)
translations
  "\<forall>x : A. P" \<rightleftharpoons> "CONST Soft_Ball A (\<lambda>x. P)"
  "\<exists>x : A. P" \<rightleftharpoons> "CONST Soft_Bex A (\<lambda>x. P)"


lemma Soft_BallI [intro]: "(\<And>x. x : A \<Longrightarrow> P x) \<Longrightarrow> \<forall>x : A. P x"
  unfolding Soft_Ball_def by auto

lemma Soft_BallE [elim]: "\<lbrakk>\<forall>x : A. P x; \<And>x. (x : A \<Longrightarrow> P x) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding Soft_Ball_def by auto

lemma Soft_BallE' [elim]: "\<lbrakk>\<forall>x : A. P x; x : A\<rbrakk> \<Longrightarrow> P x"
  unfolding Soft_Ball_def by auto

lemma Soft_BexI [intro]: "\<lbrakk>x : A; P x\<rbrakk> \<Longrightarrow> \<exists>x : A. P x"
  unfolding Soft_Bex_def by auto

lemma Soft_BexE [elim]: "\<lbrakk>\<exists>x : A. P x; \<And>x. \<lbrakk>x : A; P x\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding Soft_Bex_def by auto


subsection \<open>Pi types\<close>

text \<open>Soft-types for meta-level functions.\<close>

definition Pi_type :: "'a type \<Rightarrow> ('a \<Rightarrow> 'b type) \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where Pi_typedef: "Pi_type \<sigma> \<tau> \<equiv> Type (\<lambda>f. \<forall>x : \<sigma>. f x : \<tau> x)"

abbreviation function_type :: "'a type \<Rightarrow> 'b type \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where "function_type A B \<equiv> Pi_type A (\<lambda>_. B)"

syntax
  "_telescope" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<Rightarrow>" 50)
translations
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>x. B)"
  "A \<Rightarrow> B" \<rightleftharpoons> "CONST function_type A B"

text \<open>
We write \<^term>\<open>(x : A) \<Rightarrow> B x\<close> for the dependent function type and simply \<^term>\<open>A \<Rightarrow> B\<close> for the
non-dependent version.
\<close>

lemma Pi_type_iff: "f : (x : \<sigma>) \<Rightarrow> \<tau> x \<longleftrightarrow> (\<forall>x. x : \<sigma> \<longrightarrow> f x : \<tau> x)"
  unfolding Pi_typedef by (auto iff: has_type_iff)

lemma
  Pi_typeI [intro!]: "(\<And>x. x : A \<Longrightarrow> f x : B x) \<Longrightarrow> f : (x : A) \<Rightarrow> B x" and

  Pi_typeE [elim]: "\<lbrakk>f : (x : A) \<Rightarrow> B x; x : A\<rbrakk> \<Longrightarrow> f x : B x"

  by (auto iff: Pi_type_iff)


subsection \<open>Intersections\<close>

definition Int_type :: "'a type \<Rightarrow> 'a type \<Rightarrow> 'a type" (infixl "\<bar>" 55)
  where Int_typedef: "A \<bar> B \<equiv> Type (\<lambda>x. x : A \<and> x : B)"

lemma Int_type_iff: "x : A \<bar> B \<longleftrightarrow> x : A \<and> x : B"
  unfolding Int_typedef by (simp only: has_type_iff)

lemma
  Int_typeI [intro]: "x : A \<Longrightarrow> x : B \<Longrightarrow> x : A \<bar> B" and

  Int_typeD1: "x : A \<bar> B \<Longrightarrow> x : A" and

  Int_typeD2: "x : A \<bar> B \<Longrightarrow> x : B"

  by (auto iff: Int_type_iff)


subsection \<open>Subtypes\<close>

definition subtype :: "'a type \<Rightarrow> 'a type \<Rightarrow> bool" (infix "\<prec>" 50)
  where subtype_iff:  "A \<prec> B \<longleftrightarrow> (\<forall>x : A. x : B)"

lemma subtypeI [intro]: "(\<And>x. x : A \<Longrightarrow> x : B) \<Longrightarrow> A \<prec> B"
  by (auto iff: subtype_iff)

lemma subtypeE [elim]: "\<lbrakk>A \<prec> B; \<And>x. (x : B \<Longrightarrow> P); x : A\<rbrakk> \<Longrightarrow> P"
  by (auto dest!: Soft_BallI iff: subtype_iff)

lemma subtypeE' [elim]: "\<lbrakk>A \<prec> B; x : A\<rbrakk> \<Longrightarrow> x : B"
  by (auto iff: subtype_iff)


subsection \<open>The ``any'' type\<close>

text \<open>Used, for example, to reflect rigid types back into the soft type system.\<close>

definition any :: "'a type"
  where any_typedef: "any \<equiv> Type (\<lambda>_. True)"

lemma any_typeI [intro]: "x : any"
  unfolding any_typedef by (simp only: has_type_iff)

abbreviation bool :: "bool type"
  where "bool \<equiv> any"


subsection \<open>Type annotations\<close>

definition with_type :: "'a \<Rightarrow> 'a type \<Rightarrow> 'a" (infixl ":>" 50)
  where "with_type x A \<equiv> x"

text \<open>\<^term>\<open>x :> A\<close> annotates \<open>x\<close> with type \<open>A\<close>.\<close>


subsection \<open>Adjectives\<close>

text \<open>We allow adjectives—in the form of predicates—to modify types.\<close>

definition adjective :: "['a \<Rightarrow> bool, 'a type] \<Rightarrow> 'a type" (infixr "\<cdot>" 56)
  where "adj \<cdot> type \<equiv> Type (\<lambda>x. adj x) \<bar> type"

lemma adjective_iff: "x : adj \<cdot> type \<longleftrightarrow> adj x \<and> x : type"
  unfolding adjective_def by (simp only: Int_type_iff has_type_iff)

lemma
  adj_spec: "x : adj \<cdot> type \<Longrightarrow> adj x" and

  type_spec: "x : adj \<cdot> type \<Longrightarrow> x : type"

  by (simp_all only: adjective_iff)


subsection \<open>Type complement\<close>

text \<open>``non'' modifier gives the complement of a predicate.\<close>

definition non :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("non-_" [1000])
  where "non-P \<equiv> \<lambda>x. \<not> P x"


subsection \<open>Tooling and automation\<close>

declare atomize_conjL [symmetric, rulify] \<comment>\<open>Used in normalization of type judgments.\<close>

named_theorems type_simp
named_theorems type_instance
named_theorems derivation_rules
named_theorems subtype_rules

ML_file "soft_type.ML"
ML_file "soft_type_context.ML"
ML_file "unification.ML"
ML_file "type_classes.ML"
ML_file "elaboration.ML"
ML_file \<open>derivation.ML\<close>

attribute_setup derive = \<open>Derivation.derivation_rule_parser\<close>


named_theorems squash

lemmas [squash] =
  has_type_iff
  Pi_type_iff
  Int_type_iff
  adjective_iff

method squash_types = (simp_all only: squash)

text \<open>@{method squash_types} converts all typing subformulas to their equivalent predicate forms.\<close>


subsection \<open>Basic declarations for HOL material\<close>

lemma eq_type [type]: "(=) : A \<Rightarrow> A \<Rightarrow> bool"
  by auto

lemma imp_type [type]: "(\<longrightarrow>) : bool \<Rightarrow> bool \<Rightarrow> bool"
  by auto

declare with_type_def [type_simp]


end
