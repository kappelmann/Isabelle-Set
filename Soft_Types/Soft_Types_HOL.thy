\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Soft types for HOL\<close>
theory Soft_Types_HOL
  imports
    HOL.HOL
    Implicit_Arguments
    "HOL-Eisbach.Eisbach"
  keywords
    "opaque" :: thy_decl and
    "soft_type_translation" :: thy_goal_stmt and
    "print_opaque_terms" "print_types" :: diag
begin

text \<open>This theory introduces a generic notion of soft types based on HOL
predicates. It contains the basic definitions and technical tool setup.\<close>


declare [[eta_contract=false]]

text \<open>Remove conflicting HOL-specific syntax.\<close>

bundle HOL_ascii_syntax
begin
notation (ASCII)
  Not ("~ _" [40] 40) and
  conj (infixr "&" 35) and
  disj (infixr "|" 30) and
  implies (infixr "-->" 25) and
  not_equal (infixl "~=" 50)
syntax "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let (_)/ in (_))" 10)
end
bundle no_HOL_ascii_syntax
begin
no_notation (ASCII)
  Not ("~ _" [40] 40) and
  conj (infixr "&" 35) and
  disj (infixr "|" 30) and
  implies (infixr "-->" 25) and
  not_equal (infixl "~=" 50)
no_syntax "_Let" :: "[letbinds, 'a] \<Rightarrow> 'a" ("(let (_)/ in (_))" 10)
end

unbundle no_HOL_ascii_syntax


subsection \<open>Basic type judgments\<close>

text \<open>Soft types are "just" predicates wrapped up in a constructor.\<close>

typedecl 'a type

axiomatization
  type :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a type\<close> and
  adj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a type \<Rightarrow> 'a type\<close>  and
  has_type :: \<open>'a \<Rightarrow> 'a type \<Rightarrow> bool\<close>
where
  meaning_of_adj: "has_type x (adj P T) \<equiv> P x \<and> has_type x T" and
  meaning_of_type: "has_type x (type P) \<equiv> P x"

bundle soft_type_base_syntax
begin notation adj (infixr "\<sqdot>" \<comment>\<open>\<sqdot>\<close> 56) and has_type (infix ":" 45) end
bundle no_soft_type_base_syntax
begin no_notation adj (infixr "\<sqdot>" \<comment>\<open>\<sqdot>\<close> 56) and has_type (infix ":" 45) end

unbundle soft_type_base_syntax

abbreviation (input) "type_pred T x \<equiv> x : T"

lemma has_typeI: "P x \<Longrightarrow> x : type P"
  unfolding meaning_of_type by assumption

lemma has_typeD: "x : type P \<Longrightarrow> P x"
  unfolding meaning_of_type by assumption

lemma has_typeE:
  assumes "x : type P"
  obtains "P x"
  using assms unfolding meaning_of_type by auto

lemma has_adjI: "\<lbrakk>P x; x : T\<rbrakk> \<Longrightarrow> x : P \<sqdot> T"
  unfolding meaning_of_adj by auto

lemma
  has_adjD1: "x : P \<sqdot> T \<Longrightarrow> P x" and
  has_adjD2: "x : P \<sqdot> T \<Longrightarrow> x : T"
  unfolding meaning_of_adj by auto

lemma has_adjE:
  "\<lbrakk>x: P \<sqdot> T; \<lbrakk>P x; x : T\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  unfolding meaning_of_adj by auto


subsection \<open>Type-Bounded quantifiers\<close>

definition tball :: "'a type \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "tball A P \<equiv> (\<forall>x. x : A \<longrightarrow> P x)"

definition tbex :: "'a type \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "tbex A P \<equiv> (\<exists>x. x : A \<and> P x)"

(*TODO: localise*)
syntax
  "_tball"  :: \<open>[idts, 'a type, bool] \<Rightarrow> bool\<close> ("(2\<forall>_ : _./ _)" 10)
  "_tball2" :: \<open>[idts, 'a type, bool] \<Rightarrow> bool\<close>
  "_tbex"   :: \<open>[idts, 'a type, bool] \<Rightarrow> bool\<close> ("(2\<exists>_ : _./ _)" 10)
  "_tbex2"  :: \<open>[idts, 'a type, bool] \<Rightarrow> bool\<close>
translations
  "\<forall>x xs : A. P" \<rightharpoonup> "CONST tball A (\<lambda>x. _tball2 xs A P)"
  "_tball2 x A P" \<rightharpoonup> "\<forall>x : A. P"
  "\<forall>x : A. P" \<rightleftharpoons> "CONST tball A (\<lambda>x. P)"

  "\<exists>x xs : A. P" \<rightharpoonup> "CONST tbex A (\<lambda>x. _tbex2 xs A P)"
  "_tbex2 x A P" \<rightharpoonup> "\<exists>x : A. P"
  "\<exists>x : A. P" \<rightleftharpoons> "CONST tbex A (\<lambda>x. P)"


text\<open>Setup of one point rules.\<close>

simproc_setup defined_bex ("\<exists>x : A. P x \<and> Q x") =
  \<open>fn _ => Quantifier1.rearrange_Bex
    (fn ctxt => unfold_tac ctxt @{thms tbex_def})\<close>

simproc_setup defined_ball ("\<forall>x : A. P x \<longrightarrow> Q x") =
  \<open>fn _ => Quantifier1.rearrange_Ball
    (fn ctxt => unfold_tac ctxt @{thms tball_def})\<close>

lemma tballI [intro!]: "(\<And>x. x : A \<Longrightarrow> P x) \<Longrightarrow> \<forall>x : A. P x"
  unfolding tball_def by auto

lemma tballE [elim!]:
  assumes "\<forall>x : A. P x"
  obtains "\<And>x. x : A \<Longrightarrow> P x"
  using assms unfolding tball_def by auto

lemma tballD [elim]: "\<lbrakk>\<forall>x : A. P x; x : A\<rbrakk> \<Longrightarrow> P x"
  unfolding tball_def by auto

lemma tball_iff_ex_has_type [simp]: "(\<forall>x : A. P) \<longleftrightarrow> ((\<exists>x. x : A) \<longrightarrow> P)"
  by (simp add: tball_def)

lemma tball_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x : A' \<Longrightarrow> P x \<longleftrightarrow> P' x\<rbrakk> \<Longrightarrow> (\<forall>x : A. P x) \<longleftrightarrow> (\<forall>x : A'. P' x)"
  by (simp add: tball_def)

lemma tball_or_iff_tball_or [simp]: "(\<forall>x : A. P x \<or> Q) \<longleftrightarrow> ((\<forall>x : A. P x) \<or> Q)"
  by auto

lemma tball_or_iff_or_tball [simp]: "(\<forall>x : A. P \<or> Q x) \<longleftrightarrow> (P \<or> (\<forall>x : A. Q x))"
  by auto

lemma tball_imp_iff_imp_tball [simp]: "(\<forall>x : A. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x : A. Q x))"
  by auto

lemma atomize_tball: "(\<And>x. x : A \<Longrightarrow> P x) \<equiv> Trueprop (\<forall>x : A. P x)"
  by (simp only: tball_def atomize_all atomize_imp)

declare atomize_tball[symmetric, rulify]
declare atomize_tball[symmetric, defn]

lemma tbexI [intro]: "\<lbrakk>x : A; P x\<rbrakk> \<Longrightarrow> \<exists>x : A. P x"
  unfolding tbex_def by auto

lemma tbexE [elim!]:
  assumes "\<exists>x : A. P x"
  obtains x where "x : A" and "P x"
  using assms unfolding tbex_def by auto

lemma tbex_iff_ex_and [simp]: "(\<exists>x : A. P) \<longleftrightarrow> ((\<exists>x. x : A) \<and> P)"
  unfolding tbex_def by simp

lemma tbex_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. x : A' \<Longrightarrow> P x \<longleftrightarrow> P' x\<rbrakk> \<Longrightarrow> (\<exists>x : A. P x) \<longleftrightarrow> (\<exists>x : A'. P' x)"
  unfolding tbex_def by (simp cong: conj_cong)

lemma tbex_and_iff_tbex_and [simp]: "(\<exists>x : A. P x \<and> Q) \<longleftrightarrow> ((\<exists>x : A. P x) \<and> Q)"
  by auto

lemma tbex_and_iff_or_tbex [simp]: "(\<exists>x : A. P \<and> Q x) \<longleftrightarrow> (P \<and> (\<exists>x : A. Q x))"
  by auto

lemma tball_imp_iff_tbex_imp [simp]: "(\<forall>x : A. P x \<longrightarrow> Q) \<longleftrightarrow> ((\<exists>x : A. P x) \<longrightarrow> Q)"
  by auto

lemma not_tball_iff_tbex_not [simp]: "(\<not>(\<forall>x : A. P x)) \<longleftrightarrow> (\<exists>x : A. \<not>P x)"
  by auto

lemma not_tbex_iff_tball_not [simp]: "(\<not>(\<exists>x : A. P x)) \<longleftrightarrow> (\<forall>x : A. \<not>P x)"
  by auto


subsection \<open>Low-level soft type methods\<close>

(*FUTURE: Dedicated keyword setup for soft type declarations should go here*)

text \<open>Unfold all type information to work only in the underlying theory:\<close>

named_theorems typedef \<comment>\<open>soft type definitions\<close>
named_theorems type_intro \<comment>\<open>soft type introduction rules\<close>
  (*FUTURE: This should be kept for typechecking, so only introduction rules
    whose premises and conclusion are type judgments should be declared*)

method unfold_types =
  (rule type_intro
  |simp_all only: typedef meaning_of_type meaning_of_adj tball_def tbex_def)+


subsection \<open>Dependent Function/Pi-Types (\<Pi>-Types)\<close>

text \<open>Dependent function soft type for HOL lambda terms.\<close>

definition Dep_fun_type :: "'a type \<Rightarrow> ('a \<Rightarrow> 'b type) \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where [typedef]: "Dep_fun_type A B \<equiv> type (\<lambda>f. \<forall>x : A. f x : B x)"

abbreviation "Fun_type A B \<equiv> Dep_fun_type A (\<lambda>_. B)"

(*TODO: bundle/localise notation*)
syntax
  "_functions_telescope" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<Rightarrow>" 50)
translations
  "(x y : A) \<Rightarrow> B" \<rightharpoonup> "(x : A)(y : A) \<Rightarrow> B"
  "(x : A) args \<Rightarrow> B" \<rightleftharpoons> "(x : A) \<Rightarrow> args \<Rightarrow> B"
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Dep_fun_type A (\<lambda>x. B)"
  "A \<Rightarrow> B" \<rightleftharpoons> "CONST Fun_type A B"

lemma Dep_fun_typeI [type_intro]:
  "(\<And>x. x : A \<Longrightarrow> f x : B x) \<Longrightarrow> f : (x : A) \<Rightarrow> B x"
  unfolding Dep_fun_type_def meaning_of_type by auto

lemma Dep_fun_typeE:
  "\<lbrakk>f : (x : A) \<Rightarrow> B x; x : A\<rbrakk> \<Longrightarrow> f x : B x"
  unfolding Dep_fun_type_def meaning_of_type by auto

lemma Dep_fun_contravariant_dom:
  "\<lbrakk>f : (x : A) \<Rightarrow> B x; \<And>x. x : A' \<Longrightarrow> x : A\<rbrakk> \<Longrightarrow> f : (x : A') \<Rightarrow> B x"
  unfolding Dep_fun_type_def meaning_of_type by auto

lemma Dep_fun_covariant_codom:
  assumes "f : (x : A) \<Rightarrow> B x"
  and "\<And>x. x : A \<Longrightarrow> f x : B x \<Longrightarrow> f x : B' x"
  shows "f : (x : A) \<Rightarrow> B' x"
  using assms unfolding Dep_fun_type_def meaning_of_type by auto


subsection \<open>Intersection and Union Types\<close>

definition [typedef]: "Int_type A B \<equiv> type (\<lambda>x. x : A \<and> x : B)"

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
  by unfold_types

lemma Int_typeE:
  assumes "x : A & B"
  obtains "x : A" "x : B"
  using assms unfolding Int_type_def by unfold_types

definition [typedef]: "Union_type A B \<equiv> type (\<lambda>x. x : A \<or> x : B)"

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
  by unfold_types auto

lemma Union_typeE:
  assumes "x : A \<bar> B"
  obtains (left) "x : A" | (right) "x : B"
  using assms by (auto dest: Union_typeD)

subsection \<open>The Any type\<close>

text \<open>Used, for example, to reflect rigid types back into the soft type system.\<close>

definition Any_type :: "'a type" ("Any")
  where [typedef]: "Any \<equiv> type (\<lambda>_. True)"

lemma Any_typeI [type_intro]: "x : Any"
  by unfold_types

abbreviation Bool_type :: "bool type" ("Bool")
  where "Bool \<equiv> Any"

lemma tball_Any_iff_ball [simp]: "(\<forall>x : Any. P x) \<longleftrightarrow> (\<forall>x. P x)"
  by (auto intro: Any_typeI)

lemma tbex_Any_iff_ex [simp]: "(\<exists>x : Any. P x) \<longleftrightarrow> (\<exists>x. P x)"
  by (auto intro: Any_typeI)


subsection \<open>Type annotations\<close>

definition with_type :: "'a \<Rightarrow> 'a type \<Rightarrow> 'a"
  where "with_type x A \<equiv> x"

bundle soft_type_with_type_syntax
begin notation with_type (infixl ":>" 50) end
bundle no_soft_type_with_type_syntax
begin no_notation with_type (infixl ":>" 50) end

unbundle soft_type_with_type_syntax

text \<open>
\<^term>\<open>x :> A\<close> annotates \<^term>\<open>x\<close> with type \<^term>\<open>A\<close>, and is used by automated
tools to represent additional typing information in a term.
\<close>


subsection \<open>Tooling and automation\<close>

declare atomize_conjL [symmetric, rulify]
  \<comment>\<open>Used in normalization of type judgments.\<close>

named_theorems type_simp \<comment>\<open>For type elaboration\<close>
named_theorems type_instance \<comment>\<open>For type class reasoning\<close>


named_theorems derivation_rules
named_theorems backderivation_rules
(* named_theorems subtype_rules *) \<comment>\<open>Unused, for now\<close>

text \<open>
@{thm derivation_rules}, @{thm backderivation_rules} \<open>(*and @{thm subtype_rules}*)\<close>
should only be inspected and not assigned to directly; use the \<open>derive\<close>,
\<open>backward_derive\<close> \<open>(*and \<open>subtype\<close>*)\<close> attributes instead.
\<close>

(* Enable this when debugging exceptions:
declare [[ML_debugger, ML_exception_debugger]]
*)

ML_file \<open>soft_type.ML\<close>
ML_file \<open>soft_type_context.ML\<close>
ML_file \<open>derivation.ML\<close>

subsubsection \<open>Type derivation\<close>

method_setup raw_discharge_type =
  \<open>Scan.optional (Scan.lift (Args.add -- Args.colon) |-- Scan.repeat Args.term) []
    >> (fn add_tms => fn ctxt => SIMPLE_METHOD (
      HEADGOAL (Derivation.raw_discharge_type_tac [] add_tms ctxt)))\<close>

method_setup discharge_types =
  \<open>Scan.optional (Scan.lift (Args.add -- Args.colon) |-- Scan.repeat Args.term) []
    >> (fn add_tms => fn ctxt => SIMPLE_METHOD (
      REPEAT1 (CHANGED (ALLGOALS (TRY o (
        Derivation.full_discharge_types_tac [] add_tms ctxt))))))\<close>

ML \<open>
val soft_type_simp_solver =
  let
    fun solver ctxt i =
      (if Config.get ctxt Derivation.debug
      then print_tac ctxt ("type derivation called on subgoal " ^ string_of_int i)
      else all_tac)
      THEN
      (SUBGOAL (fn (_, j) =>
        Derivation.full_discharge_types_tac (Simplifier.prems_of ctxt) [] ctxt j)) i
  in
    map_theory_simpset (fn ctxt => ctxt
      addSolver (mk_solver "discharge_types" solver))
  end
\<close>

setup \<open>soft_type_simp_solver\<close>

ML_file \<open>unification.ML\<close>
ML_file \<open>type_classes.ML\<close>
ML_file \<open>elaboration.ML\<close>
ML_file \<open>isar_integration.ML\<close>

setup \<open>Isar_Integration.setup\<close>

declare with_type_def [type_simp]


subsection \<open>Basic declarations\<close>

declare Any_typeI [type]
declare Dep_fun_typeI [backward_derive]
declare Dep_fun_typeE [derive]

lemma eq_type [type]: "(=) : A \<Rightarrow> A \<Rightarrow> Bool"
  by discharge_types

lemma imp_type [type]: "(\<longrightarrow>) : Bool \<Rightarrow> Bool \<Rightarrow> Bool"
  by discharge_types

lemma const_fun_type [derive]: "c : C \<Longrightarrow> (\<lambda>a. c) : A \<Rightarrow> C"
  by discharge_types

lemma id_type [type]: "(\<lambda>x. x) : A \<Rightarrow> A"
  by discharge_types

lemma if_type [type]: "If : Bool \<Rightarrow> A \<Rightarrow> A \<Rightarrow> A"
  by unfold_types auto


end
