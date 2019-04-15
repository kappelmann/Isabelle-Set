theory Soft_Types_HOL
  imports HOL.HOL
begin

text \<open>
  HOL version of the soft types library.
\<close>

typedecl 'a type

axiomatization 
  Type :: "('a \<Rightarrow> bool) \<Rightarrow> 'a type" and
  pred_of :: "'a type \<Rightarrow> 'a \<Rightarrow> bool"
  where
  pred_of_Type: "pred_of (Type t) \<equiv> t"

definition has_type :: "'a \<Rightarrow> 'a type \<Rightarrow> bool" (infix ":::" 40)
  where "x ::: T \<equiv> pred_of T x"

lemma has_type_Type[simp]: "x ::: Type P \<equiv> P x"
  unfolding has_type_def pred_of_Type .


subsection \<open> Pi-Types \<close>

definition Pi_type :: "'a type \<Rightarrow> ('a \<Rightarrow> 'b type) \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where
  "Pi_type \<sigma> \<tau> \<equiv> Type (\<lambda>f. (\<forall>x. x ::: \<sigma> \<longrightarrow> f x ::: \<tau> x))"

syntax
  "_telescope" :: "[pttrn, 'a type, 'b type] \<Rightarrow> 'c type"  ("'(_ : _') \<Rightarrow> _" 50)
translations
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>x. B)"


lemma Pi_typeI:
  assumes "\<forall>x. x ::: A \<longrightarrow> f x ::: B x"
  shows "f ::: (x:A) \<Rightarrow> B x"
  unfolding Pi_type_def has_type_Type
  by fact

lemma Pi_typeE:
  assumes 1: "f ::: (x: A) \<Rightarrow> B x"
  assumes 2: "x ::: A"
  shows "f x ::: B x"
proof -
  from 2
  show "?thesis"
  by (rule 1[unfolded Pi_type_def has_type_Type, rule_format])
qed


subsection \<open> Intersections \<close>

definition Int_Type :: "'a type \<Rightarrow> 'a type \<Rightarrow> 'a type" (infixl "\<bar>" 100) 
where "A \<bar> B \<equiv> Type (\<lambda>x. (x ::: A \<and> x ::: B))"

lemma Int_TypeI [intro]:
  "x ::: A \<Longrightarrow> x ::: B \<Longrightarrow> x ::: A \<bar> B"
  unfolding Int_Type_def has_type_Type
  by auto

lemma Int_TypeD1 [intro]:
  "x ::: A \<bar> B \<Longrightarrow> x ::: A"
  unfolding Int_Type_def has_type_Type
  by auto

lemma Int_TypeD2 [intro]:
  "x ::: A \<bar> B \<Longrightarrow> x ::: B"
  unfolding Int_Type_def has_type_Type
  by auto


subsection \<open> Some Tooling \<close>

named_theorems type_simp

ML_file "soft_type.ML"
ML_file "soft_type_context.ML"
ML_file "soft_type_inference.ML"


(* See Old_ZF_Examples/ZF_Typing_Examples.thy for an example with type inference *)


end
