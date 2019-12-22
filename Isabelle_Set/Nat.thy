chapter \<open>Natural numbers\<close>

theory Nat
imports Ordinal Recursion

begin

text \<open>The basic definitions have already been shown for \<nat> = \<omega>.\<close>

definition nat ("\<nat>") where "\<nat> = \<omega>"

lemmas
  nat_unfold = omega_unfold[folded nat_def] and
  zero_nat [simp] = empty_in_omega[folded nat_def] and
  succ_nat [simp] = succ_omega[folded nat_def] and
  nat_cases = omega_cases[folded nat_def] and
  nat_induct [case_names 0 succ, induct set: nat] = omega_induct[folded nat_def] and
  nat_pred_exists = omega_pred_exists[folded nat_def] and
  pred_nat [simp] = pred_omega[folded nat_def] and
  pred_0 = pred_empty and
  pred_succ [simp] = Ordinal.pred_succ[folded nat_def] and
  succ_pred [simp] = Ordinal.succ_pred[folded nat_def]


section \<open>\<nat> as a type\<close>

abbreviation "Nat \<equiv> element \<nat>"

lemmas Nat_induct = nat_induct
  [ simplified element_iff,
    case_names 0 succ,
    induct set: nat ]

lemma Nat_Ord [derive]: "x : Nat \<Longrightarrow> x : Ord"
  by (induct x rule: Nat_induct) (auto intro: succ_Ord)

lemma
  zero_type: "{} : Nat" and
  succ_type [type]: "succ : Nat \<Rightarrow> Nat" and
  pred_type [type]: "pred : Nat \<Rightarrow> Nat"
  by unfold_types auto
(*
  Declaring zero_type [type] causes a funny error when importing Nat and Sum or
  Set_Extension together: investigate!
*)


section \<open>Primitive recursion\<close>

definition "nat_case \<equiv> \<lambda>n\<^sub>0\<in> \<nat>. \<lambda>f\<in> \<nat> \<rightarrow> \<nat>. \<lambda>n\<in> \<nat>.
  if n = {} then n\<^sub>0 else f `(pred n)"

text \<open>
  Lift set-theoretic notion to HOL by reflecting the argument HOL function f to
  the set theory.

  Maybe this can be automated with syntax phase translations in the future?
\<close>

definition "natcase n\<^sub>0 f n = nat_case `n\<^sub>0 `(\<lambda>n\<in> \<nat>. f n) `n"

lemma natcase_type [type]:
  "natcase: Nat \<Rightarrow> (Nat \<Rightarrow> Nat) \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding natcase_def nat_case_def
  apply unfold_types
  text \<open>Reasoning with set-theoretic function is still quite manual\<close>
  apply (rule FunctionE)+
  apply (rule FunctionI)+
  by auto

lemma natcase_0 [simp]:
  assumes "n\<^sub>0 : Nat"
      and "f : Nat \<Rightarrow> Nat"
  shows "natcase n\<^sub>0 f {} = n\<^sub>0"
  unfolding natcase_def nat_case_def
  using assms by unfold_types fastforce

lemma natcase_succ [simp]:
  assumes "n\<^sub>0 : Nat"
      and "f : Nat \<Rightarrow> Nat"
      and "n : Nat"
  shows "natcase n\<^sub>0 f (succ n) = f n"
  unfolding natcase_def nat_case_def
  using assms by unfold_types fastforce

(*THIS DEFINITION IS WRONG: it needs the well-founded recursion operator*)
definition "natrec n\<^sub>0 f n = natcase n\<^sub>0 (\<lambda>x. f (natcase n\<^sub>0 f x)) n"

text \<open>
  The next proof is a nontrivial *EXAMPLE* of where type derivation is doing
  some nontrivial simplification of a proof! :) :) :)
  (The derivation depth needs to be increased in order to derive the required
  type of the inner function \<open>\<lambda>x. f (natcase n\<^sub>0 f (pred x))\<close>.
\<close>

lemma natrec_0 [simp]:
  assumes "n\<^sub>0 : Nat"
      and "f : Nat \<Rightarrow> Nat"
  shows "natrec n\<^sub>0 f {} = n\<^sub>0"
  unfolding natrec_def
  using assms [[derivation_depth=3]] by auto

lemma natrec_succ:
  assumes "n\<^sub>0 : Nat"
      and "f : Nat \<Rightarrow> Nat"
      and "n : Nat"
  shows "natrec n\<^sub>0 f (succ n) = f (natrec n\<^sub>0 f n)"
oops


section \<open>Addition\<close>

(*
  We might consider implementing set-theoretic lambdas for set-sized soft types
  if we want to conform to usual type-theoretic notation. (Do we?)
  This ventures a little into Mizar-like "sethood" territory...
*)

text \<open>This definition is rather low-level for now:\<close>

(* definition "natural_add = \<lambda>m n\<in> \<nat>. if m = {} then n else succ *)


section \<open>Monoid properties\<close>




end
