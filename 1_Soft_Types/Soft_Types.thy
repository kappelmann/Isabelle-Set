theory Soft_Types
  imports Pure
begin


text \<open>
  We define a meta-type of types, which is isomorphic to Pure predicates, that is
  @{typ "'a => prop"}. Pi-types and intersections can then be introduced as definitions.
  
  We define some syntax translations to introduce a telescope-like syntax.
\<close>

subsection \<open> Notion of soft type \<close>

(* Just an embedding of Pure predicates into a new type, for more explicit handling.
Note the type argument: We can assign a soft type to any object in Pure, including
meta-level functions. *)
typedecl 'a type

axiomatization 
  Type :: "('a \<Rightarrow> prop) \<Rightarrow> 'a type"
  and pred_of :: "'a type \<Rightarrow> 'a \<Rightarrow> prop"
  where pred_of_Type: "pred_of (Type t) \<equiv> t"

definition has_type :: "'a \<Rightarrow> 'a type \<Rightarrow> prop" (infix ":::" 5)
  where "x ::: T \<equiv> pred_of T x"

lemma has_type_Type[simp]: "x ::: Type P \<equiv> P x"
  unfolding has_type_def pred_of_Type .



subsection \<open> Pi-Types \<close>


definition Pi_type :: "'a type \<Rightarrow> ('a \<Rightarrow> 'b type) \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where
  "Pi_type \<sigma> \<tau> \<equiv> Type (\<lambda>f. (\<And>x. x ::: \<sigma> \<Longrightarrow> f x ::: \<tau> x))"


abbreviation 
  function_space :: "'a type \<Rightarrow> 'b type \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where "function_space A B \<equiv> Pi_type A (\<lambda>_. B)"

nonterminal tel_lhs

syntax
  "_tel_simple" :: "logic \<Rightarrow> tel_lhs" ("_" [11] 12)
  "_telescopelhs" :: "pttrn \<Rightarrow> logic \<Rightarrow> tel_lhs" ("'(_ : _')" [11, 10] 12)
  "_telescope" :: "tel_lhs \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<Rightarrow>" 10)
translations
  "A \<Rightarrow> B" \<rightleftharpoons> "CONST function_space A B"
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>x. B)"


term "(x : A) \<Rightarrow> (y : B) \<Rightarrow> C y"
term "(x : A) \<Rightarrow> B"
term "A \<Rightarrow> B \<Rightarrow> (x : C) \<Rightarrow> D x"
term "A \<Rightarrow> B \<Rightarrow> C"
term "(f: (x:A) \<Rightarrow> B x) \<Rightarrow> C f"


lemma Pi_typeI:
  assumes a: "\<And>x. x ::: A \<Longrightarrow> f x ::: B x"
  shows "f ::: (x : A) \<Rightarrow> B x"
  unfolding Pi_type_def has_type_Type
  by (rule a)
  
lemma Pi_typeE:
  assumes 1: "f ::: (x: A) \<Rightarrow> B x"
  assumes 2: "x ::: A"
  shows "f x ::: B x"
proof -
  from 2
  show "PROP ?thesis"
    by (rule 1[unfolded Pi_type_def has_type_Type, rule_format])
qed


subsection \<open> Intersections \<close>

definition Int_Type :: "'a type \<Rightarrow> 'a type \<Rightarrow> 'a type" (infixl "\<bar>" 100) 
where "A \<bar> B \<equiv> Type (\<lambda>x. (x ::: A &&& x ::: B))"

lemma Int_TypeI:
  "x ::: A \<Longrightarrow> x ::: B \<Longrightarrow> x ::: A \<bar> B"
  unfolding Int_Type_def has_type_Type
  by (rule conjunctionI)

lemma Int_TypeD1:
  "x ::: A \<bar> B \<Longrightarrow> x ::: A"
  unfolding Int_Type_def has_type_Type
  by (rule conjunctionD1)

lemma Int_TypeD2:
  "x ::: A \<bar> B \<Longrightarrow> x ::: B"
  unfolding Int_Type_def has_type_Type
  by (rule conjunctionD2)



subsection \<open> Some Tooling \<close>




named_theorems type_simp

ML_file "soft_type.ML"
ML_file "soft_type_context.ML"
ML_file "unification.ML"
ML_file "soft_type_inference.ML"



(* See Old_ZF_Examples/ZF_Typing_Examples.thy for an example with type inference *)



end
