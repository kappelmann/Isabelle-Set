section \<open>Soft types for HOL\<close>

theory Soft_Types_HOL
imports HOL.HOL

begin

text \<open>HOL version of the soft types library, using @{typ bool} instead of @{typ prop} for the judgments.\<close>

declare[[eta_contract=false]]

typedecl 'a type

axiomatization 
  Type :: "('a \<Rightarrow> bool) \<Rightarrow> 'a type" and
  pred_of :: "'a type \<Rightarrow> 'a \<Rightarrow> bool"
where
  pred_of_Type: "pred_of (Type t) \<equiv> t"

definition has_type :: "'a \<Rightarrow> 'a type \<Rightarrow> bool" (infix ":" 45)
  where "x : T \<equiv> pred_of T x"

lemma has_type_Type [simp]: "x : Type P \<equiv> P x"
  unfolding has_type_def pred_of_Type .

lemma has_typeI [intro]: "P x \<Longrightarrow> x : Type P"
  by auto


subsection \<open>Bounded quantifiers\<close>

definition Soft_Ball :: "'a type \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Soft_Ball A P \<equiv> (\<forall>x. x : A \<longrightarrow> P x)"

definition Soft_Bex :: "'a type \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "Soft_Bex A P \<equiv> (\<exists>x. x : A \<and> P x)"

syntax
  "_Set_Ball" :: "[pttrn, 'a type, bool] \<Rightarrow> bool"  ("(3\<forall>_ : _./ _)" 10)
  "_Set_Bex"  :: "[pttrn, 'a type, bool] \<Rightarrow> bool"  ("(3\<exists>_ : _./ _)" 10)
translations
  "\<forall>x : A. P" \<rightleftharpoons> "CONST Soft_Ball A (\<lambda>x. P)"
  "\<exists>x : A. P" \<rightleftharpoons> "CONST Soft_Bex A (\<lambda>x. P)"


lemma Soft_BallI [intro]: "(\<And>x. x : A \<Longrightarrow> P x) \<Longrightarrow> \<forall>x : A. P x"
  unfolding Soft_Ball_def by auto

lemma Soft_BexI [intro]: "\<lbrakk>x : A; P x\<rbrakk> \<Longrightarrow> \<exists>x : A. P x"
  unfolding Soft_Bex_def by auto

(* elim rules etc.? *)


subsection \<open>Pi types\<close>

definition Pi_type :: "'a type \<Rightarrow> ('a \<Rightarrow> 'b type) \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where Pi_typedef: "Pi_type \<sigma> \<tau> \<equiv> Type (\<lambda>f. \<forall>x : \<sigma>. f x : \<tau> x)"

abbreviation function_space :: "'a type \<Rightarrow> 'b type \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where "function_space A B \<equiv> Pi_type A (\<lambda>_. B)"

nonterminal tel_lhs

syntax
  "_tel_simple" :: "logic \<Rightarrow> tel_lhs" ("_" [51] 52)
  "_telescopelhs" :: "pttrn \<Rightarrow> logic \<Rightarrow> tel_lhs" ("[_ : _]" [51, 50] 52)
  "_telescope" :: "tel_lhs \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<Rightarrow>" 50)
translations
  "A \<Rightarrow> B" \<rightleftharpoons> "CONST function_space A B"
  "[x : A] \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>x. B)"


lemma Pi_typeI:
  assumes "\<And>x. x : A \<Longrightarrow> f x : B x"
  shows "f : [x : A] \<Rightarrow> B x"
  unfolding Pi_typedef has_type_Type
  using assms by auto

lemma Pi_typeE:
  assumes 1: "f : [x : A] \<Rightarrow> B x"
  assumes 2: "x : A"
  shows "f x : B x"
proof -
  from 2
  show "?thesis"
  by (rule 1[unfolded Pi_typedef has_type_Type Soft_Ball_def, rule_format])
qed


subsection \<open>Intersections\<close>

definition Int_type :: "'a type \<Rightarrow> 'a type \<Rightarrow> 'a type" (infixl "\<bar>" 55)
where Int_typedef: "A \<bar> B \<equiv> Type (\<lambda>x. x : A \<and> x : B)"

lemma Int_TypeI [intro?]:
  "x : A \<Longrightarrow> x : B \<Longrightarrow> x : A \<bar> B"
  unfolding Int_typedef has_type_Type
  by auto

lemma Int_TypeD1:
  "x : A \<bar> B \<Longrightarrow> x : A"
  unfolding Int_typedef has_type_Type
  by auto

lemma Int_TypeD2:
  "x : A \<bar> B \<Longrightarrow> x : B"
  unfolding Int_typedef has_type_Type
  by auto


subsection \<open>Subtypes\<close>

definition is_subtype :: "'a type \<Rightarrow> 'a type \<Rightarrow> bool" ("(_ \<prec> _)")
  where "A \<prec> B \<equiv> \<forall>x : A. pred_of A x \<longrightarrow> pred_of B x"


subsection \<open>Some tooling\<close>

named_theorems type_simp

ML_file "soft_type.ML"
ML_file "soft_type_context.ML"
ML_file "unification.ML"
ML_file "soft_type_inference.ML"


(* See Old_ZF_Examples/ZF_Typing_Examples.thy for an example with type inference *)


end
