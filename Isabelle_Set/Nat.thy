chapter \<open>Natural numbers\<close>

theory Nat
imports Ordinal Function

begin

text \<open>The basic definitions have already been shown for \<nat> = \<omega>.\<close>

definition nat ("\<nat>") where "\<nat> = \<omega>"

lemmas
  nat_unfold = omega_unfold[folded nat_def] and
  zero_nat [simp] = empty_in_omega[folded nat_def] and
  succ_nat [simp] = succ_omega[folded nat_def] and
  nat_induct [case_names 0 succ, induct set: nat] = omega_induct[folded nat_def] and
  nat_pred_exists = omega_pred_exists[folded nat_def] and
  pred_nat [simp] = pred_omega[folded nat_def] and
  pred_of_succ [simp] = Ordinal.pred_of_succ[folded nat_def] and
  succ_of_pred [simp] = Ordinal.succ_of_pred[folded nat_def]


section \<open>\<nat> as a type\<close>

definition [typedef]: "Nat = element \<nat>"

lemmas Nat_induct = nat_induct
  [ simplified element_iff, folded Nat_def,
    case_names 0 succ,
    induct set: nat ]

lemma Nat_Ord [derive]: "x : Nat \<Longrightarrow> x : Ord"
  by (induct x rule: Nat_induct) (auto intro: succ_Ord)

lemma
  zero_type (*[type]*): "{} : Nat" and
  succ_type [type]: "succ : Nat \<Rightarrow> Nat" and
  pred_type [type]: "pred : Nat \<Rightarrow> Nat"
  by unfold_types auto
(*
  Declaring zero_type [type] causes a funny error when importing Nat and Sum or
  Set_Extension together: investigate!
*)


section \<open>Primitive recursion\<close>

definition "nat_primrec \<equiv> \<lambda>n\<^sub>0\<in> \<nat>. \<lambda>f\<in> \<nat> \<rightarrow> \<nat>. \<lambda>n\<in> \<nat>.
  if n = {} then n\<^sub>0 else f `(pred n)"

text \<open>
  Lift set-theoretic notion to HOL, by reflecting the argument HOL function f to
  the set theory.
\<close>

definition "natrec n\<^sub>0 f n = nat_primrec `n\<^sub>0 `(\<lambda>n\<in> \<nat>. f n) `n"

lemma natrec_type [type]:
  "natrec: Nat \<Rightarrow> (Nat \<Rightarrow> Nat) \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding natrec_def nat_primrec_def
  apply unfold_types
  (*Observe that reasoning with set-theoretic function is still quite manual*)
  apply (rule FunctionE)+
  apply (rule FunctionI)+
  by auto

lemma nat_rec_0:
  "\<lbrakk>n\<^sub>0 : Nat; f : Nat \<Rightarrow> Nat\<rbrakk> \<Longrightarrow> natrec n\<^sub>0 f {} = n\<^sub>0"
  unfolding natrec_def nat_primrec_def
  apply unfold_types
  apply simp (*Need more results on reflected functions*)
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
