section \<open>Soft types for HOL\<close>

theory Soft_Types_HOL
imports
  HOL.HOL
  Implicit_Arguments
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"

begin

text \<open>HOL version of the soft types library, using @{typ bool} instead of @{typ prop} for the judgments.\<close>

declare[[eta_contract=false]]


subsection \<open>Named theorems and automation\<close>

named_theorems intro_st
named_theorems elim_st
named_theorems dest_st
named_theorems iff_st
named_theorems simp_st

named_theorems subtype \<comment>\<open>For subtyping judgments\<close>
named_theorems typedef \<comment>\<open>For smart unfolding\<close>
  (* ^ To be implemented.. *)

method stauto declares intro_st elim_st dest_st iff_st simp_st =
  (auto intro: intro_st elim: elim_st simp: iff_st;
  solves\<open>stauto intro_st: intro_st elim_st: elim_st dest_st: dest_st
    iff_st: iff_st simp_st: simp_st\<close>)
| (elim elim_st;
  solves\<open>stauto intro_st: intro_st elim_st: elim_st dest_st: dest_st
    iff_st: iff_st simp_st: simp_st\<close>)
| (drule dest_st;
  solves\<open>stauto intro_st: intro_st elim_st: elim_st dest_st: dest_st
    iff_st: iff_st simp_st: simp_st\<close>)
| (intro intro_st;
  solves\<open>stauto intro_st: intro_st elim_st: elim_st dest_st: dest_st
    iff_st: iff_st simp_st: simp_st\<close>)
| (simp add: simp_st;
  solves\<open>stauto intro_st: intro_st elim_st: elim_st dest_st: dest_st
    iff_st: iff_st simp_st: simp_st\<close>)


subsection \<open>Basic definitions\<close>

typedecl 'a type

axiomatization 
  Type :: "('a \<Rightarrow> bool) \<Rightarrow> 'a type" and
  pred_of :: "'a type \<Rightarrow> 'a \<Rightarrow> bool"
where
  pred_of_type: "pred_of (Type t) \<equiv> t"

definition has_type :: "'a \<Rightarrow> 'a type \<Rightarrow> bool" (infix ":" 45)
  where "x : T \<equiv> pred_of T x"

lemma has_type_iff [iff_st]: "x : Type P \<longleftrightarrow> P x"
  unfolding has_type_def pred_of_type ..

lemma has_typeI [intro_st]: "P x \<Longrightarrow> x : Type P" by stauto
lemma has_typeE [elim_st]: "x : Type P \<Longrightarrow> P x" by stauto


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

definition Pi_type :: "'a type \<Rightarrow> ('a \<Rightarrow> 'b type) \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where Pi_typedef: "Pi_type \<sigma> \<tau> \<equiv> Type (\<lambda>f. \<forall>x : \<sigma>. f x : \<tau> x)"

abbreviation function_space :: "'a type \<Rightarrow> 'b type \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where "function_space A B \<equiv> Pi_type A (\<lambda>_. B)"

nonterminal tel_lhs

syntax
  "_telescope" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<Rightarrow>" 50)
translations
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>x. B)"
  "A \<Rightarrow> B" \<rightleftharpoons> "CONST function_space A B"

lemma Pi_type_iff [iff_st]: "f : (x : \<sigma>) \<Rightarrow> \<tau> x \<longleftrightarrow> (\<forall>x : \<sigma>. f x : \<tau> x)"
  unfolding Pi_typedef by stauto

lemma Pi_typeI [intro_st]:
  assumes "\<And>x. x : A \<Longrightarrow> f x : B x"
  shows "f : (x : A) \<Rightarrow> B x"
  using assms by stauto

lemma Pi_typeE [elim_st]:
  assumes "f : (x : A) \<Rightarrow> B x" and "x : A"
  shows "f x : B x"
  using assms by stauto


subsection \<open>Intersections\<close>

definition Int_type :: "'a type \<Rightarrow> 'a type \<Rightarrow> 'a type" (infixl "\<bar>" 55)
  where Int_typedef: "A \<bar> B \<equiv> Type (\<lambda>x. x : A \<and> x : B)"

lemma Int_type_iff [iff_st]: "x : A \<bar> B \<longleftrightarrow> x : A \<and> x : B"
  unfolding Int_typedef by stauto

lemma Int_typeI [intro_st]: "x : A \<Longrightarrow> x : B \<Longrightarrow> x : A \<bar> B" by stauto

lemma Int_typeD1 [dest_st]: "x : A \<bar> B \<Longrightarrow> x : A" by stauto
lemma Int_typeD2 [dest_st]: "x : A \<bar> B \<Longrightarrow> x : B" by stauto


subsection \<open>Subtypes\<close>

definition subtype :: "'a type \<Rightarrow> 'a type \<Rightarrow> bool" (infix "\<prec>" 50)
  where subtype_iff [iff]: "A \<prec> B \<longleftrightarrow> (\<forall>x : A. x : B)"

lemma subtypeI [intro_st]: "(\<And>x. x : A \<Longrightarrow> x : B) \<Longrightarrow> A \<prec> B" by auto

lemma subtypeE [elim]: "\<lbrakk>A \<prec> B; \<And>x. (x : B \<Longrightarrow> P); x : A\<rbrakk> \<Longrightarrow> P"
  by (drule Soft_BallI) auto

lemma subtypeD [elim_st]: "\<lbrakk>A \<prec> B; x : A\<rbrakk> \<Longrightarrow> x : B"
  by auto

subsection \<open>The ``any'' type\<close>

text \<open>Used to reflect rigid types back into the soft type system.\<close>
  (* Josh -- ^ Not yet sure if this is even useful. *)

definition any :: "'a type"
  where any_typedef: "any = Type (\<lambda>_. True)"

lemma any_typeI: "x : any"
  unfolding any_typedef by stauto


subsection \<open>Tooling\<close>

named_theorems type_simp

ML_file "soft_type.ML"
ML_file "soft_type_context.ML"
ML_file "unification.ML"
ML_file "soft_type_inference.ML"


end
