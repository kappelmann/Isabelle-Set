theory Typing
  imports Nat_ZF
begin



text \<open>
  We define a meta-type of types, which is isomorphic to predicates. Pi-types
  and the type of sets can then be introduced as definitions.
  
  We define some syntax translations to introduce a telescope-like syntax.
\<close>


(* Just an embedding of Pure predicates into a new type, for more explicit handling *)
typedecl 'a type

axiomatization 
  Type :: "('a::{} \<Rightarrow> prop) \<Rightarrow> 'a type"
  and pred_of :: "'a type \<Rightarrow> 'a \<Rightarrow> prop"
  where pred_of_Type: "pred_of (Type t) \<equiv> t"

definition has_type :: "'a::{} \<Rightarrow> 'a type \<Rightarrow> prop" (infix ":::" 40)
  where "x ::: T \<equiv> pred_of T x"

lemma has_type_Type[simp]: "x ::: Type P \<equiv> P x"
  unfolding has_type_def pred_of_Type .



subsection \<open> Pi-Types \<close>


definition Pi_type :: "'a::{} type \<Rightarrow> ('a \<Rightarrow> 'b::{} type) \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where
  "Pi_type \<sigma> \<tau> \<equiv> Type (\<lambda>f. (\<And>x. x ::: \<sigma> \<Longrightarrow> f x ::: \<tau> x))"

syntax
  "_telescope" :: "[pttrn, 'a type, 'b type] \<Rightarrow> 'c type"  ("'(_ : _') \<Rightarrow> _" 50)
translations
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>x. B)"

term "(x : A) \<Rightarrow> (y : B) \<Rightarrow> C y"
term "t ::: (x : set A) \<Rightarrow> (set (A + B))"


lemma Pi_typeI:
  assumes a: "\<And>(x::'a::{}). x ::: A \<Longrightarrow> f x ::: B x"
  shows "f ::: (x:A) \<Rightarrow> B x"
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

(* Implicit version. Currently unused

axiomatization 
  Implicit_Pi_type :: "'a type \<Rightarrow> ('a::{} \<Rightarrow> 'b::{} type) \<Rightarrow> ('a \<Rightarrow> 'b) type"

syntax
  "_telescope_implicit" :: "[pttrn, 'a type, 'b type] \<Rightarrow> 'c type"  ("'{_ : _'} \<Rightarrow> _" 50)
translations
  "{x : A} \<Rightarrow> B" \<rightleftharpoons> "CONST Implicit_Pi_type A (\<lambda>x. B)"

*)


subsection \<open> Type of sets \<close>
definition Set :: "i type"
  where "Set \<equiv> Type (\<lambda>x::i. (x == x))"

lemma Set_TypeI: "(x::i) ::: Set"
  unfolding Set_def has_type_Type .


subsection \<open> Type of elements of a given set \<close>

definition set :: "i \<Rightarrow> i type"
  where "set A == Type (%x. Trueprop (x \<in> A))"

lemma set_typeI: "x \<in> A \<Longrightarrow> x ::: set A"
  unfolding set_def has_type_Type .

lemma set_typeE: "x ::: set A \<Longrightarrow> x \<in> A"
  unfolding set_def has_type_Type .


subsection \<open> Type of object-level propositions \<close>

definition o :: "o type"
  where "o \<equiv> Type (\<lambda>x::o. (x == x))"

lemma o_TypeI: "(P::o) ::: o"
  unfolding o_def has_type_Type .



ML_file "soft_type.ML"
ML_file "zf_logic.ML"
ML_file "soft_type_context.ML"
ML_file "soft_type_inference.ML"


lemma eq[type]: "((=)::(i \<Rightarrow> i \<Rightarrow> o)) ::: (x: A) \<Rightarrow> (y: A) \<Rightarrow> o"
  by (intro Pi_typeI o_TypeI)



text \<open> Example: Inferring types for list append \<close>

context
  fixes List :: "i \<Rightarrow> i"
    and Nil :: "i \<Rightarrow> i"
    and Cons :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
    and append :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
  assumes [type]: "Nil ::: (A: Set) \<Rightarrow> set (List A)"
    and [type]: "Cons ::: (A: Set) \<Rightarrow> (x: set A) \<Rightarrow> (xs : set (List A)) \<Rightarrow> set (List A)" 
    and [type]: "append ::: (A: Set) \<Rightarrow> (xs: set (List A)) \<Rightarrow> (ys : set (List A)) \<Rightarrow> set (List A)"
begin



ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "Nil A = B"}
]\<close>

ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "%A. Nil A"}
]\<close>

ML \<open>Soft_Type_Inference.print_inferred_types @{context} [
  @{term "%A x xs. Cons A x xs"}
]\<close>

ML \<open>

Soft_Type_Inference.print_inferred_types @{context} [
  @{term "append A (Cons A x xs) ys = Cons A x (append A xs ys)"},
  @{term "append A (Nil A) ys = ys"} 
]
\<close>

(*
ML \<open>

Soft_Type_Inference.print_inferred_types @{context} [
  @{term "\<And>A x xs ys. append A (Cons A x xs) ys = Cons A x (append A xs ys)"},
  @{term "\<And>A ys. append A (Nil A) ys = ys"} 
]
\<close>
*)


end






text \<open> Example: Inferring types for vectors of given length \<close>

context
  fixes Vec :: "i \<Rightarrow> i \<Rightarrow> i"
    and VNil :: "i \<Rightarrow> i"
    and VCons :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
    and add :: "i \<Rightarrow> i \<Rightarrow> i"
    and vappend :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
  assumes [type]: "Vec ::: (A: Set) \<Rightarrow> (n: set nat) \<Rightarrow> Set"
    and [type]: "VNil ::: (A: Set) \<Rightarrow> set (Vec A 0)"
    and [type]: "VCons ::: (A: Set) \<Rightarrow> (n: set nat) \<Rightarrow> (x: set A) \<Rightarrow> (xs : set (Vec A n)) \<Rightarrow> set (Vec A (succ n))"
    and [type]: "add ::: (n : set nat) \<Rightarrow> (m : set nat) \<Rightarrow> set nat"
    and [type]: "succ ::: (n : set nat) \<Rightarrow> set nat"
    and [type]: "0 ::: set nat"
    and [type]: "vappend ::: (A: Set) \<Rightarrow> (n: set nat) \<Rightarrow> (m: set nat) \<Rightarrow> (xs: set (Vec A n)) 
\<Rightarrow> (ys: set (Vec A m)) \<Rightarrow> set (Vec A (add n m))"
begin





(*

ML \<open> Soft_Type_Inference.print_inferred_types @{context} [
  @{term "vappend A (succ n) m (VCons A n x xs) ys
   = VCons A (add n m) x (vappend A n m xs ys)"}
]\<close>
*)


end




(*

axiomatization
  bijective :: "i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> o"
and compose :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i \<Rightarrow> i"
lemma "bijective ::: (A: Type) \<Rightarrow> (B: Type) \<Rightarrow> (f:(x:A)\<Rightarrow>B) \<Rightarrow> Type"]]


lemma "f \<in> bij A B \<Longrightarrow> g \<in> bij B C \<Longrightarrow> g O f \<in> bij A C"


*)






end
