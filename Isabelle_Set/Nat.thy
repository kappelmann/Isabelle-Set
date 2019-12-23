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


section \<open>The \<open><\<close> and \<open>\<le>\<close> orders on Nat\<close>

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

definition "nat_le m n = (nat_lt m n \<or> m = n)"

(* lemma nat_le_subset: "nat_le m n \<longleftrightarrow> m \<subseteq> n" *)


section \<open>Finite induction\<close>

lemma finite_induct:
  assumes "n: Nat"
      and "nat_le m n"
      and "P {}"
      and "\<And>m. nat_lt m n \<Longrightarrow> P m \<Longrightarrow> P (succ m)"
  shows "P m"
oops


section \<open>Recursion\<close>

text \<open>A specialization of well-founded recursion to \<open><\<close>\<close>

lemma Nat_recursion:
  assumes "f : element X \<Rightarrow> element X"
      and "x\<^sub>0 : element X"
  obtains F where
    "F : Nat \<Rightarrow> element X"
    "F {} = x\<^sub>0"
    "\<And>n. n: Nat \<Longrightarrow> F (succ n) = f (F n)"

proof

fix n

have "n: Nat \<Longrightarrow> \<exists>F.
  dom F = succ (succ n) \<and> F `{} = x\<^sub>0 \<and>
  (\<forall>m \<in> n. F `(succ m) = f (F `m)) \<and> F `(succ n) = f (F `n)"
proof (induction n rule: Nat_induct)
  case base
  let ?F = "{\<langle>{}, x\<^sub>0\<rangle>, \<langle>succ {}, f x\<^sub>0\<rangle>}"
  have
    "dom ?F = succ (succ {}) \<and> ?F `{} = x\<^sub>0 \<and>
    (\<forall>m \<in> {}. ?F `(succ m) = f (?F `m)) \<and> ?F `(succ {}) = f (?F `{})"
    by (auto intro: equalityI simp: succ_def)
  thus
    "\<exists>F. dom F = succ (succ {}) \<and> F `{} = x\<^sub>0 \<and>
    (\<forall>m \<in> {}. F `(succ m) = f (F `m)) \<and> F `(succ {}) = f (F `{})"
    by fast

  case (induct n)
  obtain F where IH:
    "dom F = succ (succ n)"
    "F `{} = x\<^sub>0"
    "\<forall>m \<in> n. F `(succ m) = f (F `m)"
    "F `(succ n) = f (F `n)"
    using induct.IH by auto
  let ?F = "F \<union> {\<langle>succ (succ n), f (F `(succ n))\<rangle>}"

  have 1: "dom ?F = succ (succ (succ n))"
    using IH(1) by (auto intro: equalityI simp: bin_union_dom succ_def)

  have 2: "?F `{} = x\<^sub>0"
    using IH(2) by auto

  have 3: "\<forall>m \<in> succ n. ?F `(succ m) = f (?F `m)"
  proof (simp, clarify)
    fix m show "m \<in> succ n \<Longrightarrow> F `(succ m) = f (F `m)"
    using IH by (elim succ_cases) auto
  qed

  have 4: "?F `(succ (succ n)) = f (?F `(succ n))"
    by (simp add: IH(1) mem_irrefl)

  thus "\<exists>F.
    dom F = succ (succ (succ n)) \<and>
    F `{} = x\<^sub>0 \<and>
    (\<forall>m \<in> succ n. F `(succ m) = f (F `m)) \<and>
    F `(succ (succ n)) = f (F `(succ n))"
    using 1 2 3 4 by fast
qed

have "n: Nat \<Longrightarrow> \<exists>F.
  F \<in> succ (succ n) \<rightarrow> X \<and> F `{} = x\<^sub>0 \<and>
  (\<forall>m \<in> n. F `(succ m) = f (F `m)) \<and> F `(succ n) = f (F `n)"
proof (induction n rule: Nat_induct)
  case base
  let ?F = "{\<langle>{}, x\<^sub>0\<rangle>, \<langle>succ {}, f x\<^sub>0\<rangle>}"
  have "succ (succ {}) = {succ {}} \<union> {{}}"
    by (auto intro: equalityI simp: succ_def)
  hence "?F \<in> succ (succ {}) \<rightarrow> X"
    by (force intro: cons_FunctionI' assms)
  hence
    "?F \<in> succ (succ {}) \<rightarrow> X \<and> ?F `{} = x\<^sub>0 \<and>
    (\<forall>m \<in> {}. ?F `(succ m) = f (?F `m)) \<and> ?F `(succ {}) = f (?F `{})"
    by (auto intro: equalityI simp: succ_def)
  thus
    "\<exists>F. F \<in> succ (succ {}) \<rightarrow> X \<and> F `{} = x\<^sub>0 \<and>
    (\<forall>m \<in> {}. F `(succ m) = f (F `m)) \<and> F `(succ {}) = f (F `{})"
    by blast

  case (induct n)
  obtain F where IH:
    "F \<in> succ (succ n) \<rightarrow> X"
    "F `{} = x\<^sub>0"
    "\<forall>m \<in> n. F `(succ m) = f (F `m)"
    "F `(succ n) = f (F `n)"
    using induct.IH by auto
  let ?F = "cons \<langle>succ (succ n), f (F `(succ n))\<rangle> F"

  have "?F \<in> succ (succ n) \<union> {succ (succ n)} \<rightarrow> X"
   by
    (rule cons_FunctionI')
    (auto intro: IH simp: [[type_derivation_depth=3]] mem_irrefl) \<comment>\<open>*EXAMPLE*\<close>

  hence 1: "?F \<in> succ (succ (succ n)) \<rightarrow> X"
    by (simp add: succ_def)

  have 2: "?F `{} = x\<^sub>0"
    using IH(2) by auto

  have 3: "\<forall>m \<in> succ n. ?F `(succ m) = f (?F `m)"
  proof (simp, clarify)
    fix m show "m \<in> succ n \<Longrightarrow> F `(succ m) = f (F `m)"
    using IH by (elim succ_cases) auto
  qed

  have 4: "?F `(succ (succ n)) = f (?F `(succ n))"
    by (simp add: IH(1) mem_irrefl)

  show "\<exists>F.
    F \<in> succ (succ (succ n)) \<rightarrow> X \<and>
    F `{} = x\<^sub>0 \<and>
    (\<forall>m \<in> succ n. F `(succ m) = f (F `m)) \<and>
    F `(succ (succ n)) = f (F `(succ n))"
    using 1 2 3 4 by blast
qed

let ?P = "\<lambda>F.
  F \<in> succ (succ n) \<rightarrow> X \<and>
  F `{} = x\<^sub>0 \<and>
  (\<forall>m \<in> n. F `(succ m) = f (F `m)) \<and>
  F `(succ n) = f (F `n)"

fix F G
assume n: "n: Nat" and F: "?P F" and G: "?P G"
have "F = G"
proof (rule funext)
  show "F \<in> succ (succ n) \<rightarrow> X" "G \<in> succ (succ n) \<rightarrow> X"
    using F G by auto

  fix m show "m \<in> succ (succ n) \<Longrightarrow> F `m = G `m"
  
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
  using assms [[type_derivation_depth=3]] by auto

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
