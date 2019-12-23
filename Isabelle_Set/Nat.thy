chapter \<open>Natural numbers\<close>

theory Nat
imports Ordinal Function

begin

text \<open>The basic results have already been shown for \<nat> = \<omega>.\<close>

definition nat ("\<nat>") where "\<nat> = \<omega>"

lemmas
  nat_unfold = omega_unfold[folded nat_def] and
  zero_nat [simp] = empty_in_omega[folded nat_def] and
  succ_nat [simp] = succ_omega[folded nat_def] and
  nat_cases = omega_cases[folded nat_def] and
  nat_induct [case_names 0 induct, induct set: nat] = omega_induct[folded nat_def] and
  nat_elems = omega_elems[folded nat_def] and
  pred_nat [simp] = pred_omega[folded nat_def] and
  pred_0 = pred_empty and
  pred_succ [simp] = Ordinal.pred_succ[folded nat_def] and
  succ_pred [simp] = Ordinal.succ_pred[folded nat_def]


section \<open>\<nat> as a type\<close>

abbreviation "Nat \<equiv> element \<nat>"

lemmas Nat_induct = nat_induct
  [ simplified element_type_iff,
    case_names base induct,
    induct pred: Nat ]

lemma Nat_Ord [derive]: "x : Nat \<Longrightarrow> x : Ord"
  by (induct x rule: Nat_induct) (auto intro: succ_Ord)

lemma
  zero_type [type]: "{} : Nat" and
  succ_type [type]: "succ : Nat \<Rightarrow> Nat" and
  pred_type [type]: "pred : Nat \<Rightarrow> Nat"
  by unfold_types auto


section \<open>The \<open><\<close> order on Nat\<close>

definition "nat_lt m n = (m \<in> n)"

lemma nat_lt_0 [simp]: "n : Nat \<Longrightarrow> nat_lt {} (succ n)"
  unfolding nat_lt_def nat_def
  by unfold_types (fact omega_empty_in_succ)

lemma nat_lt_monotone [intro]:
  "\<lbrakk>n: Nat; m: Nat; nat_lt m n\<rbrakk> \<Longrightarrow> nat_lt (succ m) (succ n)"
  unfolding nat_lt_def
  by (induction n rule: Nat_induct) (auto simp: succ_def)

lemma nat_lt_total:
  "\<lbrakk>m: Nat; n: Nat\<rbrakk> \<Longrightarrow> nat_lt m n \<or> m = n \<or> nat_lt n m"
  unfolding nat_lt_def
  using Ord_trichotomy by auto
  \<comment>\<open>Good *EXAMPLE* of type derivation helpfulness!\<close>


section \<open>Recursion\<close>

text \<open>A specialization of well-founded recursion to \<open><\<close>>\<close>

lemma Nat_recursion:
  assumes "f : element X \<Rightarrow> element X"
      and "x\<^sub>0 : element X"
  obtains F where
    "F : Nat \<Rightarrow> element X"
    "F {} = x\<^sub>0"
    "\<And>n. n: Nat \<Longrightarrow> F (succ n) = f (F n)"
proof -

fix n
have "n: Nat \<Longrightarrow> \<exists>F. dom F = succ (succ n) \<and> F `{} = x\<^sub>0 \<and> F `(succ n) = f (F `n)"
proof (induction n rule: Nat_induct)
  case base
  show "\<exists>F. dom F = succ (succ {}) \<and> F `{} = x\<^sub>0 \<and> F `(succ {}) = f (F `{})"
  proof
    let ?F = "{\<langle>{}, x\<^sub>0\<rangle>, \<langle>succ {}, f x\<^sub>0\<rangle>}"
    show "dom ?F = succ (succ {}) \<and> ?F `{} = x\<^sub>0 \<and> ?F `(succ {}) = f (?F `{})"
      by (auto intro: equalityI simp: succ_def)
  qed

  case (induct n)
  then obtain F where IH:
    "dom F = succ (succ n)"
    "F `{} = x\<^sub>0"
    "F `(succ n) = f (F `n)"
    by auto
  show "\<exists>F.
    dom F = succ (succ (succ n)) \<and> F `{} = x\<^sub>0 \<and>
    F `(succ (succ n)) = f (F `(succ n))"
  proof
    let ?F = "F \<union> {\<langle>succ (succ n), f (F `(succ n))\<rangle>}"
    have "dom ?F = succ (succ (succ n))"
      by (auto intro: equalityI simp: IH(1) bin_union_dom succ_def)
    moreover have "?F `{} = x\<^sub>0"
      by (auto intro: equalityI simp: IH(2) bin_union_dom)
    moreover have "?F `(succ (succ n)) = f (?F `(succ n))"
      by(auto intro: equalityI simp: IH bin_union_dom mem_irrefl succ_neq)
    ultimately show
      "dom ?F = succ (succ (succ n)) \<and>
      ?F `{} = x\<^sub>0 \<and> ?F `(succ (succ n)) = f (?F `(succ n))"
      by fast
  qed
qed

have "n: Nat \<Longrightarrow>
  F \<in> succ (succ n) \<rightarrow> X \<and> F `{} = x\<^sub>0 \<and> F `(succ n) = f (F `n) \<Longrightarrow>
  G \<in> succ (succ n) \<rightarrow> X \<and> G `{} = x\<^sub>0 \<and> G `(succ n) = f (G `n) \<Longrightarrow>
  F = G"
proof (induction n arbitrary: F G rule: Nat_induct)
  case base
  show "F = G"
  proof (rule funext)
    show "F \<in> succ (succ {}) \<rightarrow> X" and "G \<in> succ (succ {}) \<rightarrow> X"
      using base by auto
    have "succ (succ {}) = {{}, succ {}}"
      by (auto intro: equalityI simp: succ_def)
    thus "\<And>x. x \<in> succ (succ {}) \<Longrightarrow> F `x = G `x"
      using base by force
  qed
next
  case (induct n)
  show "F = G"
  proof (rule funext)
    show "F \<in> succ (succ (succ n)) \<rightarrow> X" and "G \<in> succ (succ (succ n)) \<rightarrow> X"
      using induct.prems by auto

    let ?F = "\<lambda>m\<in> succ (succ n). F `(succ m)"
    and ?G = "\<lambda>m\<in> succ (succ n). G `(succ m)"
thm induct
oops

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
