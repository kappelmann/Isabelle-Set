chapter \<open>Soft types for HOL\<close>

text \<open>
This theory introduces a generic notion of soft types based on HOL predicates.
It contains the basic definitions and technical tool setup.
\<close>

theory Soft_Types_HOL
  imports
    HOL.HOL
    Implicit_Arguments
    "HOL-Eisbach.Eisbach"
    "HOL-Eisbach.Eisbach_Tools"
  keywords
    "opaque" :: thy_decl and
    "soft_type_translation" :: thy_goal_stmt and
    "print_opaque_terms" "print_types" :: diag
begin

declare [[eta_contract=false]]


section \<open>Basic type judgments\<close>

text \<open>
Soft types are "just" predicates wrapped up in a constructor. Adjectives are
predicates that modify soft types.
\<close>

typedecl 'a type

axiomatization
  type     :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a type\<close> and
  adj      :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a type \<Rightarrow> 'a type\<close> (infixr "\<sqdot>" \<comment>\<open>\<sqdot>\<close> 56) and
  has_type :: \<open>'a \<Rightarrow> 'a type \<Rightarrow> bool\<close> (infix ":" 45)
where
  meaning_of_type: "x : type P \<equiv> P x" and
  meaning_of_adj: "x : P \<sqdot> T \<equiv> P x \<and> x : T"

lemma has_typeI: "P x \<Longrightarrow> x : type P"
  unfolding meaning_of_type by auto

lemma has_typeD: "x : type P \<Longrightarrow> P x"
  unfolding meaning_of_type by auto

lemma has_typeE:
  "\<lbrakk>x: type P; P x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  unfolding meaning_of_type by auto

lemma has_adjI: "\<lbrakk>P x; x : T\<rbrakk> \<Longrightarrow> x : P \<sqdot> T"
  unfolding meaning_of_adj by auto

lemma
  has_adjD1: "x : P \<sqdot> T \<Longrightarrow> P x" and
  has_adjD2: "x : P \<sqdot> T \<Longrightarrow> x : T"
  unfolding meaning_of_adj by auto

lemma has_adjE:
  "\<lbrakk>x: P \<sqdot> T; \<lbrakk>P x; x : T\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  unfolding meaning_of_adj by auto


section \<open>Bounded quantifiers\<close>

definition sball :: "'a type \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "sball A P \<equiv> (\<forall>x. x : A \<longrightarrow> P x)"

definition sbex :: "'a type \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "sbex A P \<equiv> (\<exists>x. x : A \<and> P x)"

syntax
  "_sball" :: "[pttrn, 'a type, bool] \<Rightarrow> bool"  ("(3\<forall>_ : _./ _)" 10)
  "_sbex"  :: "[pttrn, 'a type, bool] \<Rightarrow> bool"  ("(3\<exists>_ : _./ _)" 10)
translations
  "\<forall>x : A. P" \<rightleftharpoons> "CONST sball A (\<lambda>x. P)"
  "\<exists>x : A. P" \<rightleftharpoons> "CONST sbex A (\<lambda>x. P)"

lemma sballI [intro]: "(\<And>x. x : A \<Longrightarrow> P x) \<Longrightarrow> \<forall>x : A. P x"
  unfolding sball_def by auto

lemma sballE [elim]: "\<lbrakk>\<forall>x : A. P x; \<And>x. (x : A \<Longrightarrow> P x) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding sball_def by auto

lemma sballE' [elim]: "\<lbrakk>\<forall>x : A. P x; x : A\<rbrakk> \<Longrightarrow> P x"
  unfolding sball_def by auto

lemma sbexI [intro]: "\<lbrakk>x : A; P x\<rbrakk> \<Longrightarrow> \<exists>x : A. P x"
  unfolding sbex_def by auto

lemma sbexE [elim]: "\<lbrakk>\<exists>x : A. P x; \<And>x. \<lbrakk>x : A; P x\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding sbex_def by auto


section \<open>Low-level soft type methods\<close>

(*FUTURE: Dedicated keyword setup for soft type declarations should go here*)

text \<open>Unfold all type information to work only in the underlying theory:\<close>

named_theorems typedef \<comment>\<open>soft type definitions\<close>
named_theorems type_intro \<comment>\<open>soft type introduction rules\<close>
  (*FUTURE: This should be kept for typechecking, so only introduction rules
    whose premises and conclusion are type judgments should be declared*)

method unfold_types =
  (rule type_intro
  |simp_all only: typedef meaning_of_type meaning_of_adj sball_def sbex_def)+


section \<open>Pi types\<close>

text \<open>Dependent function soft type for HOL lambda terms.\<close>

definition Pi_type :: "'a type \<Rightarrow> ('a \<Rightarrow> 'b type) \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where [typedef]: "Pi_type A B \<equiv> type (\<lambda>f. \<forall>x : A. f x : B x)"

abbreviation "Nondep_Pi_type A B \<equiv> Pi_type A (\<lambda>_. B)"

syntax
  "_telescope" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<Rightarrow>" 50)
translations
  "(x y : A) \<Rightarrow> B" \<rightharpoonup> "(x : A)(y: A) \<Rightarrow> B"
  "(x: A) args \<Rightarrow> B" \<rightleftharpoons> "(x : A) \<Rightarrow> args \<Rightarrow> B"
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>x. B)"
  "A \<Rightarrow> B" \<rightleftharpoons> "CONST Nondep_Pi_type A B"

lemma Pi_typeI [type_intro]:
  "(\<And>x. x : A \<Longrightarrow> f x : B x) \<Longrightarrow> f : (x : A) \<Rightarrow> B x"
  unfolding Pi_type_def meaning_of_type by auto

lemma Pi_typeE:
  "\<lbrakk>f : (x : A) \<Rightarrow> B x; x : A\<rbrakk> \<Longrightarrow> f x : B x"
  unfolding Pi_type_def meaning_of_type by auto


section \<open>Intersection types\<close>

definition Int_type :: "'a type \<Rightarrow> 'a type \<Rightarrow> 'a type" (infixl "\<bar>" 55)
  where [typedef]: "A \<bar> B \<equiv> type (\<lambda>x. x : A \<and> x : B)"

lemma
  Int_typeI [type_intro]: "x : A \<Longrightarrow> x : B \<Longrightarrow> x : A \<bar> B" and
  Int_typeD1: "x : A \<bar> B \<Longrightarrow> x : A" and
  Int_typeD2: "x : A \<bar> B \<Longrightarrow> x : B" and
  Int_typeE: "\<lbrakk>x: A \<bar> B; \<lbrakk>x: A; x : B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding Int_type_def by unfold_types


section \<open>The Any type\<close>

text \<open>Used, for example, to reflect rigid types back into the soft type system.\<close>

definition Any_type :: "'a type" ("Any")
  where [typedef]: "Any \<equiv> type (\<lambda>_. True)"

lemma Any_typeI [type_intro]: "x : Any"
  by unfold_types

abbreviation Bool_type :: "bool type" ("Bool")
  where "Bool \<equiv> Any"


section \<open>Type annotations\<close>

definition with_type :: "'a \<Rightarrow> 'a type \<Rightarrow> 'a" (infixl ":>" 50)
  where "with_type x A \<equiv> x"

text \<open>
\<^term>\<open>x :> A\<close> annotates \<^term>\<open>x\<close> with type \<^term>\<open>A\<close>, and is used by automated
tools to represent additional typing information in a term.
\<close>


section \<open>Tooling and automation\<close>

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
ML_file \<open>unification.ML\<close>
ML_file \<open>type_classes.ML\<close>
ML_file \<open>elaboration.ML\<close>
ML_file \<open>isar_integration.ML\<close>

setup \<open>Isar_Integration.setup\<close>

declare with_type_def [type_simp]

\<comment> \<open>Declarations for the derivator; currently slightly ad hoc.\<close>
declare Any_typeI [type]
declare Pi_typeI [backward_derive]
declare Pi_typeE [derive]

subsection \<open>Type derivation\<close>

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


section \<open>Basic declarations\<close>

lemma eq_type [type]: "(=) : A \<Rightarrow> A \<Rightarrow> Bool"
  by unfold_types

lemma imp_type [type]: "(\<longrightarrow>) : Bool \<Rightarrow> Bool \<Rightarrow> Bool"
  by unfold_types

text \<open>The "non-" modifier gives the negation of a predicate.\<close>

definition non :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("non-_" [1000])
  where "non-P \<equiv> \<lambda>x. \<not> P x"


end
