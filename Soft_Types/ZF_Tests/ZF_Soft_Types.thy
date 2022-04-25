theory ZF_Soft_Types
  imports ZF
begin

no_notation (ASCII)
  cart_prod       (infixr \<open>*\<close> 80) and
  Int             (infixl \<open>Int\<close> 70) and
  Un              (infixl \<open>Un\<close> 65) and
  function_space  (infixr \<open>->\<close> 60) and
  Subset          (infixl \<open><=\<close> 50) and
  mem             (infixl \<open>:\<close> 50) and
  not_mem         (infixl \<open>~:\<close> 50) and
  not_equal  (infixl \<open>~=\<close> 50) and
  Not  (\<open>~ _\<close> [40] 40) and
  conj  (infixr \<open>&\<close> 35) and
  disj  (infixr \<open>|\<close> 30) and
  imp  (infixr \<open>-->\<close> 25) and
  iff  (infixr \<open><->\<close> 25)

declare [[eta_contract=false]]
declare[[show_sorts]]

text \<open>Remove conflicting HOL-specific syntax.\<close>

section \<open>Basic type judgments\<close>

text \<open>Soft types are "just" predicates wrapped up in a constructor.\<close>

typedecl 'a type

axiomatization
  type :: \<open>(('a :: {}) \<Rightarrow> o) \<Rightarrow> 'a type\<close> and
  has_type :: \<open>'a \<Rightarrow> 'a type \<Rightarrow> o\<close>
where
  meaning_of_type: "has_type(x, type(P)) \<equiv> P(x)"

bundle soft_type_base_syntax
begin notation has_type (infix ":" 45) end
bundle no_soft_type_base_syntax
begin no_notation has_type (infix ":" 45) end

unbundle soft_type_base_syntax

lemma has_typeI: "P(x) \<Longrightarrow> x : type(P)"
  unfolding meaning_of_type by assumption

lemma has_typeD: "x : type(P) \<Longrightarrow> P(x)"
  unfolding meaning_of_type by assumption

lemma has_typeE:
  assumes "x : type(P)"
  obtains "P(x)"
  using assms unfolding meaning_of_type by auto


section \<open>Type-Bounded quantifiers\<close>

definition tball :: "'a type \<Rightarrow> ('a \<Rightarrow> o) \<Rightarrow> o"
  where "tball(A, P) \<equiv> (\<forall>x. x : A \<longrightarrow> P(x))"

definition tbex :: "'a type \<Rightarrow> ('a \<Rightarrow> o) \<Rightarrow> o"
  where "tbex(A, P) \<equiv> (\<exists>x. x : A \<and> P(x))"

(*TODO: localise*)
syntax
  "_tball"  :: \<open>[idts, 'a type, o] \<Rightarrow> o\<close> ("(2\<forall>_ : _./ _)" 10)
  "_tball2" :: \<open>[idts, 'a type, o] \<Rightarrow> o\<close>
  "_tbex"   :: \<open>[idts, 'a type, o] \<Rightarrow> o\<close> ("(2\<exists>_ : _./ _)" 10)
  "_tbex2"  :: \<open>[idts, 'a type, o] \<Rightarrow> o\<close>
translations
  "\<forall>x xs : A. P" \<rightharpoonup> "CONST tball(A, (\<lambda>x. _tball2(xs, A, P)))"
  "_tball2(x, A, P)" \<rightharpoonup> "\<forall>x : A. P"
  "\<forall>x : A. P" \<rightleftharpoons> "CONST tball(A, (\<lambda>x. P))"

  "\<exists>x xs : A. P" \<rightharpoonup> "CONST tbex(A, (\<lambda>x. _tbex2(xs, A, P)))"
  "_tbex2(x, A, P)" \<rightharpoonup> "\<exists>x : A. P"
  "\<exists>x : A. P" \<rightleftharpoons> "CONST tbex(A, (\<lambda>x. P))"

text\<open>Setup of one point rules.\<close>

simproc_setup defined_bex ("\<exists>x : A. P(x) \<and> Q(x)") =
  \<open>fn _ => Quantifier1.rearrange_Bex
    (fn ctxt => unfold_tac ctxt @{thms tbex_def})\<close>

simproc_setup defined_ball ("\<forall>x : A. P(x) \<longrightarrow> Q(x)") =
  \<open>fn _ => Quantifier1.rearrange_Ball
    (fn ctxt => unfold_tac ctxt @{thms tball_def})\<close>

lemma tballI [intro!]: "(\<And>x. x : A \<Longrightarrow> P(x)) \<Longrightarrow> \<forall>x : A. P(x)"
  unfolding tball_def by auto

lemma tballE [elim!]:
  assumes "\<forall>x : A. P(x)"
  obtains "\<And>x. (x : A \<Longrightarrow> P(x))"
  using assms unfolding tball_def by auto

lemma tballD [elim]: "\<lbrakk>\<forall>x : A. P(x); x : A\<rbrakk> \<Longrightarrow> P(x)"
  unfolding tball_def by auto

lemma tball_iff_ex_has_type [simp]: "(\<forall>x : A. P) \<longleftrightarrow> ((\<exists>x. x : A) \<longrightarrow> P)"
  by (simp add: tball_def)


(* instance "fun" :: (\<open>term\<close>, \<open>term\<close>) \<open>term\<close> .. *)
(* instance "type" :: (\<open>term\<close>) \<open>term\<close> .. *)

lemma tball_cong [cong]:
  "\<lbrakk>A \<equiv> A'; \<And>x. x : A' \<Longrightarrow> P(x) \<longleftrightarrow> P'(x)\<rbrakk> \<Longrightarrow> (\<forall>x : A. P(x)) \<longleftrightarrow> (\<forall>x : A'. P'(x))"
  by (simp add: tball_def)

lemma tball_or_iff_tball_or [simp]: "(\<forall>x : A. P(x) \<or> Q) \<longleftrightarrow> ((\<forall>x : A. P(x)) \<or> Q)"
  by auto

lemma tball_or_iff_or_tball [simp]: "(\<forall>x : A. P \<or> Q(x)) \<longleftrightarrow> (P \<or> (\<forall>x : A. Q(x)))"
  by auto

lemma tball_imp_iff_imp_tball [simp]: "(\<forall>x : A. P \<longrightarrow> Q(x)) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x : A. Q(x)))"
  by auto

lemma atomize_tball: "(\<And>x. x : A \<Longrightarrow> P(x)) \<equiv> Trueprop (\<forall>x : A. P(x))"
  by (simp only: tball_def atomize_all atomize_imp)

declare atomize_tball[symmetric, rulify]
declare atomize_tball[symmetric, defn]

lemma tbexI [intro]: "\<lbrakk>x : A; P(x)\<rbrakk> \<Longrightarrow> \<exists>x : A. P(x)"
  unfolding tbex_def by auto

lemma tbexE [elim!]:
  assumes "\<exists>x : A. P(x)"
  obtains x where "x : A" and "P(x)"
  using assms unfolding tbex_def by auto

lemma tbex_iff_ex_and [simp]: "(\<exists>x : A. P) \<longleftrightarrow> ((\<exists>x. x : A) \<and> P)"
  unfolding tbex_def by simp

lemma tbex_cong [cong]:
  "\<lbrakk>A \<equiv> A'; \<And>x. x : A' \<Longrightarrow> P(x) \<longleftrightarrow> P'(x)\<rbrakk> \<Longrightarrow> (\<exists>x : A. P(x)) \<longleftrightarrow> (\<exists>x : A'. P'(x))"
  unfolding tbex_def by (simp cong: conj_cong)

lemma tbex_and_iff_tbex_and [simp]: "(\<exists>x : A. P(x) \<and> Q) \<longleftrightarrow> ((\<exists>x : A. P(x)) \<and> Q)"
  by auto

lemma tbex_and_iff_or_tbex [simp]: "(\<exists>x : A. P \<and> Q(x)) \<longleftrightarrow> (P \<and> (\<exists>x : A. Q(x)))"
  by auto

lemma tball_imp_iff_tbex_imp [simp]: "(\<forall>x : A. P(x) \<longrightarrow> Q) \<longleftrightarrow> ((\<exists>x : A. P(x)) \<longrightarrow> Q)"
  by auto

lemma not_tball_iff_tbex_not [simp]: "(\<not>(\<forall>x : A. P(x))) \<longleftrightarrow> (\<exists>x : A. \<not>P(x))"
  by auto

lemma not_tbex_iff_tball_not [simp]: "(\<not>(\<exists>x : A. P(x))) \<longleftrightarrow> (\<forall>x : A. \<not>P(x))"
  by auto


named_theorems typedef \<comment>\<open>soft type definitions\<close>
named_theorems type_intro \<comment>\<open>soft type introduction rules\<close>


section \<open>Dependent Function/Pi-Types (\<Pi>-Types)\<close>

text \<open>Dependent function soft type for HOL lambda terms.\<close>

definition Dep_fun_type :: "'a type \<Rightarrow> ('a \<Rightarrow> ('b :: {}) type) \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where [typedef]: "Dep_fun_type(A, B) \<equiv> type(\<lambda>f. \<forall>x : A. f(x) : B(x))"

abbreviation "Fun_type(A, B) \<equiv> Dep_fun_type(A, \<lambda>_. B)"

(*TODO: bundle/localise notation*)
syntax
  "_functions_telescope" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<Rightarrow>" 50)
translations
  (* "(x y : A) \<Rightarrow> B" \<rightharpoonup> "(x : A)(y : A) \<Rightarrow> B"
  "(x : A) args \<Rightarrow> B" \<rightleftharpoons> "(x : A) \<Rightarrow> args \<Rightarrow> B" *)
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Dep_fun_type(A, \<lambda>x. B)"
  "A \<Rightarrow> B" \<rightleftharpoons> "CONST Fun_type(A, B)"

lemma Dep_fun_typeI [type_intro]:
  "(\<And>x. x : A \<Longrightarrow> f(x) : B(x)) \<Longrightarrow> f : (x : A) \<Rightarrow> B(x)"
  unfolding Dep_fun_type_def meaning_of_type by auto

lemma Dep_fun_typeE:
  "\<lbrakk>f : (x : A) \<Rightarrow> B(x); x : A\<rbrakk> \<Longrightarrow> f(x) : B(x)"
  unfolding Dep_fun_type_def meaning_of_type by auto

lemma Dep_fun_contravariant_dom:
  "\<lbrakk>f : (x : A) \<Rightarrow> B(x); \<And>x. x : A' \<Longrightarrow> x : A\<rbrakk> \<Longrightarrow> f : (x : A') \<Rightarrow> B(x)"
  unfolding Dep_fun_type_def meaning_of_type by auto

lemma Dep_fun_covariant_codom:
  assumes "f : (x : A) \<Rightarrow> B(x)"
  and "\<And>x. x : A \<Longrightarrow> f(x) : B(x) \<Longrightarrow> f(x) : B'(x)"
  shows "f : (x : A) \<Rightarrow>  B'(x)"
  using assms unfolding Dep_fun_type_def meaning_of_type by auto


section \<open>Intersection and Union Types\<close>

definition [typedef]: "Int_type(A, B) \<equiv> type (\<lambda>x. x : A \<and> x : B)"

bundle soft_type_Int_type_syntax
begin notation Int_type (infixl "&" 55) end
bundle no_soft_type_Int_type_syntax
begin no_notation Int_type (infixl "&" 55) end

unbundle soft_type_Int_type_syntax

lemma
  Int_typeI [type_intro]: "x : A \<Longrightarrow> x : B \<Longrightarrow> x : A & B" and
  Int_typeD1: "x : A & B \<Longrightarrow> x : A" and
  Int_typeD2: "x : A & B \<Longrightarrow> x : B" and
  Int_type_covariant_left: "x : A & B \<Longrightarrow> (x : A \<Longrightarrow> x : A') \<Longrightarrow> x : A' & B" and
  Int_type_covariant_right: "x : A & B \<Longrightarrow> (x : B \<Longrightarrow> x : B') \<Longrightarrow> x : A & B'"
  by (rule type_intro
    | simp_all only: typedef meaning_of_type tball_def tbex_def)+

lemma Int_typeE:
  assumes "x : A & B"
  obtains "x : A" "x : B"
  using assms unfolding Int_type_def
  by (rule type_intro
    | simp_all only: typedef meaning_of_type tball_def tbex_def)+


definition [typedef]: "Union_type(A, B) \<equiv> type (\<lambda>x. x : A \<or> x : B)"

bundle soft_type_Union_type_syntax
begin notation Union_type (infixl "\<bar>" 55) end
bundle no_soft_type_Union_type_syntax
begin no_notation Union_type (infixl "\<bar>" 55) end

unbundle soft_type_Union_type_syntax

lemma
  Union_type_leftI: "x : A \<Longrightarrow> x : A \<bar> B" and
  Union_type_rightI: "x : B \<Longrightarrow> x : A \<bar> B" and
  Union_typeD: "x : A \<bar> B \<Longrightarrow> x : A \<or> x : B" and
  Union_type_covariant_left: "x : A \<bar> B \<Longrightarrow> (x : A \<Longrightarrow> x : A') \<Longrightarrow> x : A' \<bar> B" and
  Union_type_covariant_right: "x : A \<bar> B \<Longrightarrow> (x : B \<Longrightarrow> x : B') \<Longrightarrow> x : A \<bar> B'"
  by (rule type_intro
    | simp_all only: typedef meaning_of_type tball_def tbex_def)+ auto

lemma Union_typeE:
  assumes "x : A \<bar> B"
  obtains (left) "x : A" | (right) "x : B"
  using assms by (auto dest: Union_typeD)

section \<open>The Any type\<close>

text \<open>Used, for example, to reflect rigid types back into the soft type system.\<close>

definition Any_type :: "('a :: {}) type" ("Any")
  where [typedef]: "Any \<equiv> type (\<lambda>_. True)"

lemma Any_typeI [type_intro]: "x : Any"
  by (rule type_intro
    | simp_all only: typedef meaning_of_type tball_def tbex_def)+

abbreviation Bool_type :: "o type" ("Bool")
  where "Bool \<equiv> Any"

lemma tball_Any_iff_ball [simp]: "(\<forall>x : Any. P(x)) \<longleftrightarrow> (\<forall>x. P(x))"
  by (auto intro: Any_typeI)

lemma tbex_Any_iff_ex [simp]: "(\<exists>x : Any. P(x)) \<longleftrightarrow> (\<exists>x. P(x))"
  by (auto intro: Any_typeI)


section \<open>Type annotations\<close>

definition with_type :: "('a :: {}) \<Rightarrow> 'a type \<Rightarrow> 'a"
  where "with_type(x, A) \<equiv> x"

bundle soft_type_with_type_syntax
begin notation with_type (infixl ":>" 50) end
bundle no_soft_type_with_type_syntax
begin no_notation with_type (infixl ":>" 50) end

unbundle soft_type_with_type_syntax

definition "Element(x) \<equiv> type(\<lambda>y. y \<in> x)"

abbreviation "Nat \<equiv> Element(nat)"

(* lemma "[| n : Nat;  a : C(0);  \<And>m. m : Nat \<Longrightarrow> b(m) : C(succ(m)) |]
     ==> nat_case(a,b,n) : C(n)" *)
(* lemma "l : C(0) \<Rightarrow> (Nat \<Rightarrow> Nat) \<Rightarrow> (n : Nat) \<Rightarrow> C(n)" *)

(* lemma map_type [TC]:
  "map : (A \<Rightarrow> B) \<Rightarrow> Element(list(A)) \<Rightarrow> Element(list(B))" *)

(* lemma map_type [TC]:
  "[| l \<in> list(A);  \<And>x. x \<in> A \<Longrightarrow> h(x) \<in> B |] ==> map(h,l) \<in> list(B)"
apply (simp add: map_list_def)
apply (typecheck add: list.intros list_rec_type, blast)
done *)




end