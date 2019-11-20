section \<open>Soft types for HOL\<close>

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
  "opaque" "soft_type_translation" :: thy_decl and
  "print_opaque_terms" "print_types" :: diag

begin

declare [[eta_contract=false]]


subsection \<open>Fundamental type setup\<close>

text \<open>
  Soft types are "just" predicates wrapped up in a constructor.
  Adjectives are predicates that modify soft types.
\<close>

(*
  Josh: I think adjectives should really have their own constructor, and
  be registered similarly to types, so that we can treat them in a more
  structured way, e.g. in the derivator. FUTURE WORK!
*)

typedecl 'a type

axiomatization
  type     :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a type\<close> and
  adj      :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a type \<Rightarrow> 'a type\<close> (infixr "\<sqdot>" 56) and
  has_type :: \<open>'a \<Rightarrow> 'a type \<Rightarrow> bool\<close> (infix ":" 45)
where
  has_type_type: "x : type P \<equiv> P x" and
  has_type_adj: "x : P \<sqdot> T \<equiv> P x \<and> x : T"

lemma has_type_typeI: "P x \<Longrightarrow> x : type P"
  unfolding has_type_type by auto

lemma has_type_typeE: "x : type P \<Longrightarrow> P x"
  unfolding has_type_type by auto

lemma has_type_adjI: "\<lbrakk>P x; x : T\<rbrakk> \<Longrightarrow> x : P \<sqdot> T"
  unfolding has_type_adj by auto

lemma
  adj_spec: "x : P \<sqdot> T \<Longrightarrow> P x" and
  type_spec: "x : P \<sqdot> T \<Longrightarrow> x : T"
  unfolding has_type_adj by auto

text \<open>The "non-" modifier gives the negation of a predicate.\<close>

definition non :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("non-_" [1000])
  where "non-P \<equiv> \<lambda>x. \<not> P x"

text \<open>For soft type definitions.\<close>

named_theorems typedef


subsection \<open>Bounded quantifiers\<close>

definition SBall :: "'a type \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "SBall A P \<equiv> (\<forall>x. x : A \<longrightarrow> P x)"

definition SBex :: "'a type \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where "SBex A P \<equiv> (\<exists>x. x : A \<and> P x)"

syntax
  "_SBall" :: "[pttrn, 'a type, bool] \<Rightarrow> bool"  ("(3\<forall>_ : _./ _)" 10)
  "_SBex"  :: "[pttrn, 'a type, bool] \<Rightarrow> bool"  ("(3\<exists>_ : _./ _)" 10)
translations
  "\<forall>x : A. P" \<rightleftharpoons> "CONST SBall A (\<lambda>x. P)"
  "\<exists>x : A. P" \<rightleftharpoons> "CONST SBex A (\<lambda>x. P)"

lemma SBallI [intro]: "(\<And>x. x : A \<Longrightarrow> P x) \<Longrightarrow> \<forall>x : A. P x"
  unfolding SBall_def by auto

lemma SBallE [elim]: "\<lbrakk>\<forall>x : A. P x; \<And>x. (x : A \<Longrightarrow> P x) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding SBall_def by auto

lemma SBallE' [elim]: "\<lbrakk>\<forall>x : A. P x; x : A\<rbrakk> \<Longrightarrow> P x"
  unfolding SBall_def by auto

lemma SBexI [intro]: "\<lbrakk>x : A; P x\<rbrakk> \<Longrightarrow> \<exists>x : A. P x"
  unfolding SBex_def by auto

lemma SBexE [elim]: "\<lbrakk>\<exists>x : A. P x; \<And>x. \<lbrakk>x : A; P x\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding SBex_def by auto


subsection \<open>Low-level type methods\<close>

text \<open>
  These are the canonical low-level methods for using the defining predicates of
  a type.
\<close>
method prove_type for x =
  (rule has_type_typeI[where ?x=x] | rule has_type_adjI[where ?x=x])

(* Not complete; this doesn't handle adjectives yet *)
method use_type for x =
  (drule has_type_typeE[where ?x=x])

text \<open>Unfold all type information to work only in the underlying theory:\<close>

method unfold_types =
  (simp_all only: typedef has_type_type has_type_adj SBall_def SBex_def)


subsection \<open>Intersection types\<close>

definition Int_type :: "'a type \<Rightarrow> 'a type \<Rightarrow> 'a type" (infixl "\<bar>" 55)
  where [typedef]: "A \<bar> B \<equiv> type (\<lambda>x. x : A \<and> x : B)"

lemma
  Int_typeI: "x : A \<Longrightarrow> x : B \<Longrightarrow> x : A \<bar> B" and
  Int_typeE1: "x : A \<bar> B \<Longrightarrow> x : A" and
  Int_typeE2: "x : A \<bar> B \<Longrightarrow> x : B"
  by unfold_types


subsection \<open>The ``any'' type\<close>

text \<open>Used, for example, to reflect rigid types back into the soft type system.\<close>

definition any :: "'a type"
  where [typedef]: "any \<equiv> type (\<lambda>_. True)"

lemma any_typeI: "x : any"
  by unfold_types

abbreviation bool :: "bool type"
  where "bool \<equiv> any"


subsection \<open>\<Pi> types\<close>

text \<open>Dependent function soft type for HOL lambda terms.\<close>

definition Pi_type :: "'a type \<Rightarrow> ('a \<Rightarrow> 'b type) \<Rightarrow> ('a \<Rightarrow> 'b) type"
  where [typedef]: "Pi_type A B \<equiv> type (\<lambda>f. \<forall>x : A. f x : B x)"

syntax
  "_telescope" :: "logic \<Rightarrow> logic \<Rightarrow> logic"  (infixr "\<Rightarrow>" 50)
translations
  "(x : A) \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>x. B)"
  "A \<Rightarrow> B" \<rightleftharpoons> "CONST Pi_type A (\<lambda>_. B)"

lemma Pi_typeI:
  "(\<And>x. x : A \<Longrightarrow> f x : B x) \<Longrightarrow> f : (x : A) \<Rightarrow> B x"
  unfolding Pi_type_def by (prove_type f) auto

lemma Pi_typeE:
  "\<lbrakk>f : (x : A) \<Rightarrow> B x; x : A\<rbrakk> \<Longrightarrow> f x : B x"
  unfolding Pi_type_def by (use_type f) auto


subsection \<open>Type annotations\<close>

definition with_type :: "'a \<Rightarrow> 'a type \<Rightarrow> 'a" (infixl ":>" 50)
  where "with_type x A \<equiv> x"

text \<open>
  \<^term>\<open>x :> A\<close> annotates \<open>x\<close> with type \<open>A\<close>, and is used by automated tools to
  represent additional typing information in a term.
\<close>


subsection \<open>Tooling and automation\<close>

declare atomize_conjL [symmetric, rulify]
  \<comment>\<open>Used in normalization of type judgments.\<close>

named_theorems type_simp \<comment>\<open>For type elaboration\<close>
named_theorems type_instance \<comment>\<open>For type class reasoning\<close>

named_theorems derivation_rules
named_theorems backderivation_rules
(* named_theorems subtype_rules *) \<comment>\<open>Unused, for now\<close>
  \<comment>\<open>
    \<open>derivation_rules\<close>, \<open>backderivation_rule\<close> and \<open>subtype_rules\<close> should only be
    inspected and not assigned to directly; use the \<open>derive\<close>, \<open>backward_derive\<close>
    and \<open>subtype\<close> attributes instead.
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
declare any_typeI [type]
declare Pi_typeI [backward_derive]


subsection \<open>Methods\<close>

method_setup raw_discharge_type =
  \<open>Scan.optional (Scan.lift (Args.add -- Args.colon) |-- Scan.repeat Args.term) [] >>
    (fn add_tms => fn ctxt => SIMPLE_METHOD (
      HEADGOAL (Derivation.raw_discharge_type_tac [] add_tms ctxt)))\<close>

method_setup discharge_types =
  \<open>Scan.optional (Scan.lift (Args.add -- Args.colon) |-- Scan.repeat Args.term) [] >>
    (fn add_tms => fn ctxt => SIMPLE_METHOD (
      REPEAT1 (CHANGED (ALLGOALS (TRY o (
        Derivation.full_discharge_types_tac [] add_tms ctxt))))))\<close>


subsection \<open>Simplifier integration\<close>

ML \<open> 
val soft_type_simp_solver =
  let
    fun solver ctxt i =
      (if Config.get ctxt Derivation.debug
      then print_tac ctxt ("type derivation called on subgoal " ^ string_of_int i)
      else all_tac)
      THEN
      SOLVED' (SUBGOAL (fn (_, j) =>
        Derivation.full_discharge_types_tac (Simplifier.prems_of ctxt) [] ctxt j)) i
  in
    map_theory_simpset (fn ctxt => ctxt
      addSolver (mk_solver "discharge_types" solver))
  end
\<close>

setup \<open>soft_type_simp_solver\<close>


subsection \<open>Basic declarations for HOL material\<close>

lemma eq_type [type]: "(=) : A \<Rightarrow> A \<Rightarrow> bool"
  by unfold_types auto

lemma imp_type [type]: "(\<longrightarrow>) : bool \<Rightarrow> bool \<Rightarrow> bool"
  by unfold_types auto


end
