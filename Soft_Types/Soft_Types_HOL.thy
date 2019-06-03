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

named_theorems stintro
named_theorems stelim
named_theorems stdest
named_theorems stiff
named_theorems stsimp

named_theorems stsub \<comment>\<open>For subtyping judgments\<close>
named_theorems typedef \<comment>\<open>For smart unfolding\<close>
  (* ^ To be implemented.. *)

method stauto declares stintro stelim stdest stiff stsimp =
  (auto intro: stintro elim: stelim simp: stiff;
  solves\<open>stauto stintro: stintro stelim: stelim stdest: stdest stiff: stiff stsimp: stsimp\<close>)
| (elim stelim;
  solves\<open>stauto stintro: stintro stelim: stelim stdest: stdest stiff: stiff stsimp: stsimp\<close>)
| (drule stdest;
  solves\<open>stauto stintro: stintro stelim: stelim stdest: stdest stiff: stiff stsimp: stsimp\<close>)
| (intro stintro;
  solves\<open>stauto stintro: stintro stelim: stelim stdest: stdest stiff: stiff stsimp: stsimp\<close>)
| (simp add: stsimp;
  solves\<open>stauto stintro: stintro stelim: stelim stdest: stdest stiff: stiff stsimp: stsimp\<close>)


subsection \<open>Basic definitions\<close>

typedecl 'a type

axiomatization 
  Type :: "('a \<Rightarrow> bool) \<Rightarrow> 'a type" and
  pred_of :: "'a type \<Rightarrow> 'a \<Rightarrow> bool"
where
  pred_of_type: "pred_of (Type t) \<equiv> t"

definition has_type :: "'a \<Rightarrow> 'a type \<Rightarrow> bool" (infix ":" 45)
  where "x : T \<equiv> pred_of T x"

lemma has_type_iff [stiff]: "x : Type P \<longleftrightarrow> P x"
  unfolding has_type_def pred_of_type ..

lemma has_typeI [stintro]: "P x \<Longrightarrow> x : Type P" by stauto
lemma has_typeE [stelim]: "x : Type P \<Longrightarrow> P x" by stauto


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

lemma Pi_type_iff [stiff]: "f : (x : \<sigma>) \<Rightarrow> \<tau> x \<longleftrightarrow> (\<forall>x : \<sigma>. f x : \<tau> x)"
  unfolding Pi_typedef by stauto

lemma Pi_typeI [stintro]:
  assumes "\<And>x. x : A \<Longrightarrow> f x : B x"
  shows "f : (x : A) \<Rightarrow> B x"
  using assms by stauto

lemma Pi_typeE [stelim]:
  assumes "f : (x : A) \<Rightarrow> B x" and "x : A"
  shows "f x : B x"
  using assms by stauto


subsection \<open>Intersections\<close>

definition Int_type :: "'a type \<Rightarrow> 'a type \<Rightarrow> 'a type" (infixl "\<bar>" 55)
  where Int_typedef: "A \<bar> B \<equiv> Type (\<lambda>x. x : A \<and> x : B)"

lemma Int_type_iff [stiff]: "x : A \<bar> B \<longleftrightarrow> x : A \<and> x : B"
  unfolding Int_typedef by stauto

lemma Int_typeI [stintro]: "x : A \<Longrightarrow> x : B \<Longrightarrow> x : A \<bar> B" by stauto

lemma Int_typeD1 [stdest]: "x : A \<bar> B \<Longrightarrow> x : A" by stauto
lemma Int_typeD2 [stdest]: "x : A \<bar> B \<Longrightarrow> x : B" by stauto


subsection \<open>Subtypes\<close>

definition subtype :: "'a type \<Rightarrow> 'a type \<Rightarrow> bool" (infix "\<prec>" 50)
  where subtype_iff [iff]: "A \<prec> B \<longleftrightarrow> (\<forall>x : A. x : B)"

lemma subtypeI [stintro]: "(\<And>x. x : A \<Longrightarrow> x : B) \<Longrightarrow> A \<prec> B" by auto

lemma subtypeE [elim]: "\<lbrakk>A \<prec> B; \<And>x. (x : B \<Longrightarrow> P); x : A\<rbrakk> \<Longrightarrow> P"
  by (drule Soft_BallI) auto

lemma subtypeD [stdest]: "\<lbrakk>A \<prec> B; x : A\<rbrakk> \<Longrightarrow> x : B" by auto


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
