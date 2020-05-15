chapter \<open>Natural numbers\<close>

theory Nat
imports Ordinal Function Monoid

begin

text \<open>The basic results have already been shown for \<nat> = \<omega>.\<close>

definition nat ("\<nat>") where "\<nat> = \<omega>"

definition "nat_zero \<equiv> {}"
definition "nat_one \<equiv> succ nat_zero"

bundle notation_nat_zero begin notation nat_zero ("0") end
bundle no_notation_nat_zero begin no_notation nat_zero ("0") end

bundle notation_nat_one begin notation nat_one ("1") end
bundle no_notation_nat_one begin no_notation nat_one ("1") end

unbundle
  no_notation_zero_implicit
  no_notation_one_implicit

  notation_nat_zero
  notation_nat_one

lemmas
  nat_unfold = omega_unfold[folded nat_def nat_zero_def] and
  nat_zero_nat [simp] = empty_in_omega[folded nat_def nat_zero_def] and
  succ_nat [intro] = succ_omega[folded nat_def] and
  nat_cases = omega_cases[folded nat_def nat_zero_def] and
  nat_induct [case_names 0 induct, induct set: nat] =
    omega_induct[folded nat_def nat_zero_def] and
  nat_elems = omega_elems[folded nat_def nat_zero_def] and
  succ_not_empty [simp] = Ordinal.succ_not_empty[folded nat_zero_def] and
  empty_not_succ [simp] = Ordinal.empty_not_succ[folded nat_zero_def]

lemma nat_one_in_nat [simp]: "1 \<in> \<nat>"
  unfolding nat_one_def by auto

lemma nat_zero_ne_one [simp]: "0 \<noteq> 1"
  unfolding nat_one_def by simp

lemmas nat_one_ne_zero [simp] = nat_zero_ne_one[symmetric]

section \<open>\<nat> as a type\<close>

abbreviation "Nat \<equiv> Element \<nat>"

lemmas Nat_induct = nat_induct[
  simplified Element_iff,
  case_names base induct,
  induct pred: Nat]

lemmas Nat_cases = nat_cases[
  simplified Element_iff,
  case_names typecheck zero succ]

lemma Nat_Ord [derive]: "x: Nat \<Longrightarrow> x: Ord"
  by (induct x rule: Nat_induct) (auto intro: succ_Ord simp: nat_zero_def)

lemma
  zero_type [type]: "0: Nat" and
  succ_type [type]: "succ: Nat \<Rightarrow> Nat"
  by unfold_types auto

lemma one_type [type]: "1: Nat"
  unfolding nat_one_def by auto

section \<open>Truncated predecessor function\<close>

definition "pred n = (if n = 0 then 0 else (THE m \<in> \<nat>. n = succ m))"

lemma pred_type [type]: "pred: Nat \<Rightarrow> Nat"
  unfolding pred_def by unfold_types (auto intro: btheI1 nat_elems)

lemma pred_nonzero: "\<lbrakk>n: Nat; n \<noteq> 0\<rbrakk> \<Longrightarrow> pred n = (THE m \<in> \<nat>. n = succ m)"
  unfolding pred_def by auto

lemma pred_zero [simp]: "pred 0 = 0"
  unfolding pred_def by auto

lemma pred_succ [simp]: "n: Nat \<Longrightarrow> pred (succ n) = n"
  unfolding pred_def by auto

lemma succ_pred [simp]: "\<lbrakk>n: Nat; n \<noteq> 0\<rbrakk> \<Longrightarrow> succ (pred n) = n"
  unfolding pred_def
  by (simp, rule sym, rule btheI2) (auto intro: nat_elems)


section \<open>The \<open><\<close> and \<open>\<le>\<close> orders on Nat\<close>

definition lt (infix "<" 60) where "m < n = (m \<in> n)"

lemmas
  lt_succ [simp] = succ_mem[folded lt_def] and
  lt_succ_cases = succ_cases[folded lt_def]

lemma succ_lt_monotone [intro]:
  "n: Nat \<Longrightarrow> m < n \<Longrightarrow> succ m < succ n"
  unfolding lt_def nat_def by auto

lemma succ_lt_monotoneE:
  "\<lbrakk>n: Nat; succ m < succ n\<rbrakk> \<Longrightarrow> m < n"
  unfolding lt_def nat_def by (auto intro: omega_succ_mem_monotoneE)

lemma lt_succ_if_lt: "n : Nat \<Longrightarrow> m < n \<Longrightarrow> m < succ n"
  unfolding lt_def by simp

lemma lt_trichotomy:
  "\<lbrakk>m: Nat; n: Nat\<rbrakk> \<Longrightarrow> m < n \<or> m = n \<or> n < m"
  unfolding lt_def using Ord_trichotomy by auto
  \<comment>\<open>Good *EXAMPLE* of type derivation helpfulness!\<close>

lemma lt_trichotomyE:
  assumes major: "m: Nat" "n: Nat"
      and case1: "m < n \<Longrightarrow> P"
      and case2: "m = n \<Longrightarrow> P"
      and case3: "n < m \<Longrightarrow> P"
  shows P
  using assms lt_trichotomy unfolding lt_def by auto

definition le (infix "\<le>" 60) where "m \<le> n = (m < n \<or> m = n)"

lemma le_self [simp]: "n \<le> n"
  unfolding le_def by simp

lemma nat_lt_imp_le: "m < n \<Longrightarrow> m \<le> n"
  unfolding le_def ..

lemma le_succ [simp]: "n \<le> succ n"
  unfolding le_def by auto

lemma not_le_zero [simp]: "\<not> succ n \<le> 0"
  unfolding succ_def le_def nat_zero_def lt_def by auto

lemma succ_le_monotone:
  "\<lbrakk>n: Nat; m \<le> n\<rbrakk> \<Longrightarrow> succ m \<le> succ n"
  unfolding le_def using succ_lt_monotone by auto

lemma succ_le_monotoneE: "\<lbrakk>n: Nat; succ m \<le> succ n\<rbrakk> \<Longrightarrow> m \<le> n"
  unfolding le_def using succ_lt_monotoneE by auto

lemma succ_lt_le_monotone: "\<lbrakk>n: Nat; m < n\<rbrakk> \<Longrightarrow> succ m \<le> succ n"
  unfolding le_def using succ_lt_monotone by auto

lemma lt_succ_if_le: "n : Nat \<Longrightarrow> m \<le> n \<Longrightarrow> m < succ n"
  unfolding lt_def le_def succ_def by simp

lemma nat_zero_lt_succ [simp]: "n : Nat \<Longrightarrow> 0 < succ n"
  unfolding lt_def nat_def nat_zero_def
  by unfold_types (fact omega_empty_in_succ)

lemma lt_zerotE [elim]: "n < 0 \<Longrightarrow> P"
  unfolding lt_def nat_zero_def by auto

corollary [simp]: "\<not> n < 0" by auto

lemma ne_zero_if_zero_lt: "0 < n \<Longrightarrow> n \<noteq> 0"
  by auto

lemma zero_lt_if_ne_zero: assumes "n : Nat" and "n \<noteq> 0" shows "0 < n"
  by (rule lt_trichotomyE[of 0 n]) (auto simp: assms)

corollary nat_gt_zero_iff_ne_zero [iff]:
  "n: Nat \<Longrightarrow> 0 < n \<longleftrightarrow> n \<noteq> 0"
  using zero_lt_if_ne_zero by auto

lemma nat_zero_le [simp]: "n: Nat \<Longrightarrow> 0 \<le> n"
  by (induction rule: Nat_induct) (auto intro: nat_lt_imp_le)

lemma
  not_succ_lt [simp]: "\<not> succ n < n" and
  not_lt_self [simp]: "\<not> n < n"
  unfolding lt_def by auto

lemma le_0 [simp]: "n \<le> 0 \<Longrightarrow> n = 0"
  unfolding le_def by auto

lemma nat_lt_imp_Nat [elim]: "n: Nat \<Longrightarrow> m < n \<Longrightarrow> m: Nat"
  unfolding nat_def lt_def by unfold_types (fact omega_mem_transitive)

(*Case splits*)
lemma le_cases [case_names eq lt]:
  assumes "m \<le> n" and "n: Nat"
  obtains "m = n" | "m < n"
  using assms unfolding le_def by auto

lemma lt_asym: "\<lbrakk>m < n; n < m\<rbrakk> \<Longrightarrow> P"
  unfolding lt_def using mem_asym by blast

lemma le_iff_not_lt:
  assumes "m: Nat" "n: Nat"
  shows "m \<le> n \<longleftrightarrow> \<not> n < m"
  unfolding le_def using assms lt_trichotomy lt_asym by auto

corollary not_lt_imp_le:
  assumes "\<not> n < m"
      and "m: Nat" "n: Nat"
  shows "m \<le> n"
  using le_iff_not_lt by auto

lemma lt_trans:
  "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m < n \<Longrightarrow> k < n"
  unfolding lt_def nat_def
  by unfold_types (auto intro: omega_elem_mem_transitive')

lemma
  le_trans: "n: Nat \<Longrightarrow> k \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> k \<le> n" and
  le_lt_lt: "n: Nat \<Longrightarrow> k \<le> m \<Longrightarrow> m < n \<Longrightarrow> k < n" and
  lt_le_lt: "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m \<le> n \<Longrightarrow> k < n" and
  lt_le_le: "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m \<le> n \<Longrightarrow> k \<le> n" and
  le_lt_le: "n: Nat \<Longrightarrow> k \<le> m \<Longrightarrow> m < n \<Longrightarrow> k \<le> n" and
  lt_lt_le: "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m < n \<Longrightarrow> k \<le> n"
  unfolding le_def by (auto intro: lt_trans)

lemma le_induct:
  assumes "m: Nat"
      and "n: Nat"
      and "m \<le> n"
      and "P 0"
      and "\<And>m. m < n \<Longrightarrow> P m \<Longrightarrow> P (succ m)"
  shows "P m"
proof (cases n rule: Nat_cases, fact)
  assume "n = 0"
  hence "m = 0" using \<open>m \<le> n\<close> by auto
  thus "P m" using assms by simp

  next {
  fix m
  have "m: Nat \<Longrightarrow> (\<And>k. \<lbrakk>k: Nat; n = succ k; m \<le> n\<rbrakk> \<Longrightarrow> P m)"
  proof (induction m rule: Nat_induct)
    show "P 0" by fact
    next
    fix k l assume
      "succ l \<le> n" and
      hyp: "\<And>k. k : Nat \<Longrightarrow> n = succ k \<Longrightarrow> l \<le> n \<Longrightarrow> P l" and
      conds: "k: Nat" "n = succ k"
    then have "l < n" by (auto intro: lt_succ lt_le_lt)
    then moreover have "l \<le> n" by (rule nat_lt_imp_le)
    ultimately show "P (succ l)" using conds hyp assms(5) by auto
  qed
  }
  thus "\<And>k. k : Nat \<Longrightarrow> n = succ k \<Longrightarrow> P m" using assms by blast
qed

lemma zero_le [simp]: assumes "n : Nat" shows "0 \<le> n"
  by (induction rule: Nat_induct[OF assms(1)]) (auto intro: le_trans)


lemma ne_zero_if_gt: assumes "m : Nat" "n : Nat" "m < n" shows "n \<noteq> 0"
  by (rule ne_zero_if_zero_lt, intro le_lt_lt[of n 0 m]) auto

lemma succ_lt: "\<lbrakk>n: Nat; succ m < n\<rbrakk> \<Longrightarrow> m < n"
  unfolding succ_def lt_def nat_def
  by unfold_types (auto dest: omega_elem_Ord Ord_mem_transitive')

lemma succ_le:
  assumes "n: Nat" shows "succ m \<le> n \<Longrightarrow> m < n"
  using assms by (elim le_cases) (assumption, auto intro: succ_lt)

lemma succ_zero_lt:
  "\<lbrakk>m: Nat; n: Nat\<rbrakk> \<Longrightarrow> succ m < n \<Longrightarrow> 0 < n"
  by (rule lt_trans) auto

lemma pred_lt_monotone [intro]:
  assumes "m: Nat" "n: Nat"
      and "0 < m" "m < n"
  shows "pred m < pred n"
proof -
  have "m \<in> \<nat>" "n \<in> \<nat>" "m \<noteq> 0" "n \<noteq> 0"
    using assms by auto
  then obtain k k' where "k \<in> \<nat>" "k'\<in> \<nat>" and
    *: "m = succ k" "n = succ k'"
  using nat_elems[of m] nat_elems[of n] by blast
  then have "succ k < succ k'"
    using assms by simp
  thus ?thesis
    using succ_lt_monotoneE by (auto simp only: * pred_succ)
qed

lemma pred_lt_monotoneE:
  assumes "m: Nat" "n: Nat"
  shows "pred m < pred n \<Longrightarrow> m < n"
  using \<open>m: Nat\<close> apply (induction, clarsimp)
  using \<open>n: Nat\<close> by induction auto

lemma lt_pred_if_succ_lt:
  assumes "m: Nat" "n: Nat" "succ n < m"
  shows "n < pred m"
proof (rule succ_lt_monotoneE)
  have "m \<noteq> 0" using assms by auto
  with succ_pred show "succ n < succ (pred m)" by auto
qed discharge_types

lemma succ_lt_if_lt_pred:
  "\<lbrakk>m: Nat; n: Nat; n < pred m\<rbrakk> \<Longrightarrow> succ n < m"
  by (auto intro: pred_lt_monotoneE)
  
lemma pred_le_mono [intro!]:
  assumes "m: Nat" "n: Nat" "m \<le> n"
  shows "pred m \<le> pred n"
using assms
proof (induction m rule: Nat_induct)
  case (induct m)
  then show ?case unfolding le_def by (auto intro: lt_pred_if_succ_lt)
qed simp

lemma le_if_lt_succ: "\<lbrakk>m: Nat; n: Nat; m < succ n\<rbrakk> \<Longrightarrow> m \<le> n"
  unfolding succ_def lt_def le_def by simp

lemma le_pred_if_succ_le [intro!]:
  assumes "m : Nat" "n : Nat" "succ m \<le> n"
  shows "m \<le> pred n"
  by (subst pred_succ[OF \<open>m : Nat\<close>, symmetric], rule pred_le_mono)
  discharge_types

lemma le_succ_if_le: "n : Nat \<Longrightarrow> m \<le> n \<Longrightarrow> m \<le> succ n"
proof (rule le_induct[of m n])
  assume "n : Nat" "m \<le> n"
  then show "m : Nat" unfolding le_def using nat_lt_imp_Nat by auto
next
  fix l
  assume "n : Nat" "m \<le> n" "l < n" "l \<le> succ n"
  with nat_lt_imp_le have "l \<le> n" by simp
  then show "succ l \<le> succ n" using succ_le_monotone by auto
qed auto

lemma succ_le_if_lt:
  assumes "m: Nat" "n: Nat" "m < n"
  shows "succ m \<le> n"
proof -
  have "succ m < succ n" using assms by auto
  then show ?thesis using le_if_lt_succ assms by auto
qed

lemma le_pred_if_lt:
  assumes "m: Nat" "n: Nat" "m < n"
  shows "m \<le> pred n"
proof -
  have "succ m \<le> n" using succ_le_if_lt assms by auto
  then show ?thesis using le_pred_if_succ_le assms by auto
qed

lemma pred_lt_if_le_if_ne_zero:
  assumes "m : Nat" "n : Nat"
  and "m \<noteq> 0" "m \<le> n"
  shows "pred m < n"
  using assms succ_pred succ_lt_monotoneE[where ?m="pred m"]
  by (cases n rule: Nat_cases) (auto dest: lt_succ_if_le)

lemma pred_lt_if_le_if_zero_lt:
  assumes "m : Nat" "n : Nat"
  and "0 < m" "m \<le> n"
  shows "pred m < n"
  using assms by (auto intro: pred_lt_if_le_if_ne_zero)


section \<open>Ranges\<close>

definition range ("{_.._}") where "{l..u} = {i \<in> \<nat> | l \<le> i \<and> i \<le> u}"

lemma in_rangeI [intro]:
  assumes "n : Nat" "l \<le> n" "n \<le> u"
  shows "n \<in> {l..u}"
  unfolding range_def by auto

lemma succ_eq_range_zero: assumes "n : Nat" shows "succ n = {0..n}"
proof -
  have "{0..n} = {i \<in> \<nat> | i \<le> n}" unfolding range_def by simp
  then show ?thesis using assms
    unfolding succ_def range_def le_def lt_def nat_def Element_def meaning_of_type
    by (intro equalityI) (auto intro: omega_mem_transitive)
qed

lemmas range_zero_eq_succ = succ_eq_range_zero[symmetric]

lemma range_zeroI: "n: Nat \<Longrightarrow> m \<le> n \<Longrightarrow> m \<in> {0..n}"
  by unfold_types (auto simp: range_zero_eq_succ le_def lt_def)

lemma range_zeroE1: "m \<in> {0..n} \<Longrightarrow> m : Nat"
  unfolding range_def by auto

lemmas [derive] = range_zeroE1[simplified Element_iff]

lemma range_zeroE2: "m \<in> {0..n} \<Longrightarrow> m \<le> n"
  unfolding range_def by auto

lemma le_iff_in_range_zero: "n : Nat \<Longrightarrow> m \<le> n \<longleftrightarrow> (m \<in> {0..n})"
  by (auto intro: range_zeroI elim: range_zeroE2)

lemmas in_range_zero_iff_le = le_iff_in_range_zero[symmetric]

lemma zero_in_range_zero [derive]: "n : Nat \<Longrightarrow> 0 : Element {0..n}"
  by unfold_types auto

lemma
  [derive]: "n : Nat \<Longrightarrow> n : Element {0..n}" and
  [derive]: "n : Nat \<Longrightarrow> m : Element n \<Longrightarrow> m : Element {0..n}"
  by unfold_types (auto simp: range_zero_eq_succ)

lemma le_imp_range_zero_subset_ [intro!]:
  "n : Nat \<Longrightarrow> m \<le> n \<Longrightarrow> {0..m} \<subseteq> {0..n}"
  unfolding range_def le_def by (auto intro: lt_trans)

lemma cons_range_zero_FunctionI [intro]:
  assumes "n: Nat"
      and "f : {0..n} \<rightarrow> X"
      and "x \<in> X"
  shows "cons \<langle>succ n, x\<rangle> f : {0..succ n} \<rightarrow> X"
  by
    (simp only: range_zero_eq_succ, subst (2) succ_def)
    (auto intro: assms cons_FunctionI' simp: succ_eq_range_zero)


section \<open>Recursion\<close>

text \<open>Recursion on Nat. Axiomatized, for now.\<close>

\<comment> \<open>Note Kevin: TODO: the natural number to recurse on should come first.\<close>
axiomatization natrec :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set\<close> where
  natrec_0 [simp]: "natrec x\<^sub>0 f 0 = x\<^sub>0" and
  natrec_succ [simp]: "n: Nat \<Longrightarrow> natrec x\<^sub>0 f (succ n) = f (natrec x\<^sub>0 f n)"

lemma natrec_type [type]:
  "natrec: X \<Rightarrow> (X \<Rightarrow> X) \<Rightarrow> Nat \<Rightarrow> X"
proof discharge_types
  fix x f n
  show "n: Nat \<Longrightarrow> x: X \<Longrightarrow> f: X \<Rightarrow> X \<Longrightarrow> natrec x f n: X"
  by (induct n rule: Nat_induct) auto
qed

text \<open>Recursion on Nat with index\<close>
definition "natrec' n x\<^sub>0 f \<equiv> snd (natrec
  \<langle>0, x\<^sub>0\<rangle>
  (\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>)
  n
)"

(*Note Kevin: TODO: type derivator is not able to handle this automatically yet.*)
(*Note Kevin: dependent type can be found in Matrix.thy at the moment as it relies
on things I do not want to put in the Nat library yet.*)
lemma natrec'_type [type]:
  "natrec' : Nat \<Rightarrow> Element A \<Rightarrow> (Nat \<Rightarrow> Element A \<Rightarrow> Element A) \<Rightarrow> Element A"
proof (rule type_intro)+
  fix x\<^sub>0 f n
  assume "x\<^sub>0 : Element A" "f : Nat \<Rightarrow> Element A \<Rightarrow> Element A" "n : Nat"
  have "(\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>)
    : Element (\<nat> \<times> A) \<Rightarrow> Element (\<nat> \<times> A)" using [[type_derivation_depth=4]]
    by discharge_types
  then show "natrec' n x\<^sub>0 f : Element A" unfolding natrec'_def using [[type_derivation_depth=4]]
    by discharge_types
qed

lemma natrec'_zero [simp]: "natrec' 0 x\<^sub>0 f = x\<^sub>0"
  unfolding natrec'_def by simp

lemma natrec'_succ [simp]:
  assumes "n : Nat"
  shows "natrec' (succ n) x\<^sub>0 f = f (succ n) (natrec' n x\<^sub>0 f)"
proof -
  have "\<And> m. m : Nat \<Longrightarrow>
    fst (natrec \<langle>0, x\<^sub>0\<rangle> (\<lambda>p. \<langle>succ (fst p), f (succ (fst p)) (snd p)\<rangle>) m) = m"
    by (rule Nat_induct) auto
  then show ?thesis unfolding natrec'_def by auto
qed


section \<open>Arithmetic\<close>

subsection \<open>Addition\<close>

definition "nat_add m n = natrec n succ m"

lemma nat_add_type [type]: "nat_add: Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_add_def by auto

bundle notation_nat_add begin notation nat_add (infixl "+" 65) end
bundle no_notation_nat_add begin no_notation nat_add (infixl "+" 65) end

unbundle
  no_notation_add_implicit
  notation_nat_add

lemma nat_add_zero [simp]: "m: Nat \<Longrightarrow> m + 0 = m"
  unfolding nat_add_def by (induction m rule: Nat_induct) auto

lemma nat_zero_add [simp]: "0 + m = m"
  unfolding nat_add_def by simp

(*Next three rules declared [simp] to reduce sums to some kind of normal form*)
lemma nat_add_assoc [simp]:
  "\<lbrakk>m: Nat; n: Nat; k: Nat\<rbrakk> \<Longrightarrow> m + (n + k) = m + n + k"
  unfolding nat_add_def by (induction m rule: Nat_induct) auto

lemma nat_succ_add [simp]: "m: Nat \<Longrightarrow> succ m + n = succ (m + n)"
  unfolding nat_add_def by simp

lemma nat_add_succ [simp]: "m: Nat \<Longrightarrow> m + succ n = succ (m + n)"
  by (induction m rule: Nat_induct) auto

corollary nat_succ_add_eq_add_succ: "m: Nat \<Longrightarrow> succ m + n = m + succ n"
  using nat_succ_add nat_add_succ by simp

lemma nat_add_comm: "m: Nat \<Longrightarrow> n: Nat \<Longrightarrow> m + n = n + m"
  by (induction m rule: Nat_induct) auto

lemma nat_one_add_eq_succ: "1 + n = succ n"
  unfolding nat_one_def by (simp add: nat_add_def)

lemma nat_add_one_eq_succ: "n: Nat \<Longrightarrow> n + 1 = succ n"
  using nat_add_comm nat_one_add_eq_succ by simp

lemma nat_add_nonzero_left [simp]:
  assumes "m: Nat" "m \<noteq> 0"
  shows "m + n \<noteq> 0"
  unfolding nat_add_def using assms by induction auto

lemma nat_add_nonzero_right [simp]:
  assumes "m: Nat" "n \<noteq> 0"
  shows "m + n \<noteq> 0"
  unfolding nat_add_def using assms by induction auto

lemma nat_lt_add:
  assumes "m: Nat" "n: Nat" "l: Nat"
      and "m < n"
  shows "m < n + l"
using \<open>l: Nat\<close>
proof (induction l rule: Nat_induct)
  case (induct l)
  then have "m < n + l" by simp
  then have "m < succ (n + l)" using lt_trans by simp
  then show "m < n + succ l" using nat_add_succ by simp
\<comment> \<open>TODO: Transitivity rules have typing assumptions. Proof should more
  look like this:
  then have "n < m + l" by simp
  also have "... < succ (m + l)" by simp
  also have "... = m + succ l" using nat_add_succ_eq_succ_add by auto
  finally show ?case by auto\<close>
qed simp

(*Next two rules declared [simp] to simplify to normal form*)
lemma nat_pred_add [simp]: "\<lbrakk>m: Nat; n: Nat; 0 < m\<rbrakk> \<Longrightarrow> pred m + n = pred (m + n)"
  by (induction m rule: Nat_induct) auto

lemma nat_add_pred [simp]: "\<lbrakk>m: Nat; n: Nat; 0 < n\<rbrakk> \<Longrightarrow> m + pred n = pred (m + n)"
  using nat_pred_add by (simp add: nat_add_comm)

lemma nat_succ_add_pred [simp]:
  "\<lbrakk>m: Nat; n: Nat; 0 < n\<rbrakk> \<Longrightarrow> succ m + pred n = m + n"
  by (induction m rule: Nat_induct) auto

lemma nat_pred_add_succ [simp]:
  "\<lbrakk>m: Nat; n: Nat; 0 < m\<rbrakk> \<Longrightarrow> pred m + succ n = m + n"
  using nat_succ_add_pred by (simp add: nat_add_comm)

lemma nat_succ_add_succ:
  assumes "m: Nat" "n: Nat"
  shows "succ m + succ n = succ (succ (m + n))"
  by simp

subsection \<open>Subtraction (truncated)\<close>

definition "nat_sub m n = natrec m pred n"

lemma nat_sub_type [type]: "nat_sub: Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_sub_def by auto

bundle notation_nat_sub begin notation nat_sub (infixl "-" 65) end
bundle no_notation_nat_sub begin no_notation nat_sub (infixl "-" 65) end

unbundle notation_nat_sub

lemma nat_sub_zero [simp]: "m - 0 = m"
  unfolding nat_sub_def by auto

lemma nat_sub_succ: "n: Nat \<Longrightarrow> m - succ n = pred (m - n)"
  unfolding nat_sub_def by simp

lemma nat_zero_sub [simp]: "m: Nat \<Longrightarrow> 0 - m = 0"
  by (induction m rule: Nat_induct) (auto simp: nat_sub_succ)

lemma nat_pred_sub: "m: Nat \<Longrightarrow> pred n - m = pred (n - m)"
  by (induction m rule: Nat_induct) (auto simp: nat_sub_succ)

lemma nat_succ_sub_succ [simp]:
  "n: Nat \<Longrightarrow> m: Nat \<Longrightarrow> succ m - succ n = m - n"
  by (induction n rule: Nat_induct) (simp_all add: nat_sub_def)

lemma nat_lt_imp_zero_lt_sub [simp]:
  assumes "m: Nat" "n: Nat"
      and "m < n"
  shows "0 < n - m"
using assms
proof (induction m arbitrary: n rule: Nat_induct)
  case (induct m)
  with lt_pred_if_succ_lt have "m < pred n" by simp
  then have "0 < pred n - m" using induct.IH by simp
  then show ?case using nat_pred_sub nat_sub_succ by simp
qed simp

corollary nat_lt_imp_sub_ne_zero [simp]:
  assumes "m: Nat" "n: Nat"
      and "m < n"
  shows "n - m \<noteq> 0"
proof -
  from assms have "0 < n - m" by (rule nat_lt_imp_zero_lt_sub)
  thus ?thesis by auto
qed

lemma nat_succ_sub:
  assumes "m: Nat" "n: Nat" "n < m"
  shows "succ m - n = succ (m - n)"
using \<open>n: Nat\<close> \<open>n < m\<close> proof induction
  case (induct n)
  show "succ m - succ n = succ (m - succ n)"
    by simp (simp add: nat_sub_succ succ_lt)
qed simp

lemma nat_sub_pred:
  assumes "m: Nat" "n: Nat"
  shows "\<lbrakk>0 < n; n \<le> m\<rbrakk> \<Longrightarrow> m - pred n = succ (m - n)"
using assms(2) proof (induction, clarsimp)
  fix n assume n: "n: Nat" and "0 < succ n" and "succ n \<le> m"
  then have "n < m" by (simp add: succ_le)
  then have "0 < m - n" using n assms(1) by (intro nat_lt_imp_zero_lt_sub)
  with \<open>0 < succ n\<close> show "m - pred (succ n) = succ (m - succ n)"
    by (auto simp: nat_sub_succ)
qed

lemma nat_zero_lt_sub_imp_lt:
  assumes "m: Nat" "n: Nat"
      and "0 < m - n"
  shows "n < m"
using \<open>n: Nat\<close> \<open>0 < m - n\<close> \<open>m: Nat\<close> proof (induction arbitrary: m)
  case base thus "0 < m" by auto
  next case (induct n)
    from \<open>0 < m - succ n\<close>
    have "0 < pred m - n" and "0 < m"
      using nat_pred_sub nat_sub_succ by auto
    hence "n < pred m" by (auto intro: induct.IH)
    hence "succ n < succ (pred m)" by auto
    thus "succ n < m" using \<open>0 < m\<close> by auto
qed

corollary nat_lt_iff_zero_lt_sub:
  "\<lbrakk>m: Nat; n: Nat\<rbrakk> \<Longrightarrow> m < n \<longleftrightarrow> 0 < n - m"
  using nat_zero_lt_sub_imp_lt nat_lt_imp_zero_lt_sub by blast

lemma nat_sub_dist_add:
  assumes "m: Nat" "n: Nat" "k: Nat"
  shows "m - (n + k) = m - n - k"
using assms(3) apply (induction, clarsimp)
using assms(2) apply (induction, clarsimp)
using assms(1)
proof (induction, simp add: [[type_derivation_depth=3]])
  fix m n k assume asm: "m: Nat" "n: Nat" "k: Nat" and
    "succ m - (succ n + k) = succ m - succ n - k"
  then have "m - (n + k) = m - n -k"
    using nat_succ_add nat_succ_sub_succ by simp
  with asm show "succ m - (succ n + succ k) = succ m - succ n - succ k"
    using nat_succ_add_succ nat_succ_sub_succ nat_sub_succ by simp
qed

lemma nat_sub_twice_comm:
  assumes "m: Nat" "n: Nat" "k: Nat"
  shows "m - n - k = m - k - n"
  using assms by (simp add: nat_sub_dist_add[symmetric] nat_add_comm)

lemma nat_add_sub_assoc:
  "\<lbrakk>m: Nat; n: Nat; k: Nat; k \<le> n\<rbrakk> \<Longrightarrow> m + n - k = m + (n - k)"
proof (induction m rule: Nat_induct, clarsimp)
  case (induct m)
  show "\<lbrakk>n: Nat; k: Nat; k \<le> n\<rbrakk> \<Longrightarrow> succ m + n - k = succ m + (n - k)"
  proof (induction n arbitrary: k rule: Nat_induct, clarsimp)
    case base
    have *: "k = 0" by auto
    show "succ m - k = succ m" by (simp add: *)
  next
    case (induct n)
    note IHn = induct.IH
    show "\<lbrakk>k: Nat; k \<le> succ n\<rbrakk> \<Longrightarrow> succ m + succ n - k = succ m + (succ n - k)"
    proof (induction k rule: Nat_induct, clarsimp)
      case (induct k)
      from \<open>succ k \<le> succ n\<close> succ_le_monotoneE have "k \<le> n" by simp
      show "succ m + succ n - succ k = succ m + (succ n - succ k)"
        using IHn by (simp add: nat_succ_add_succ)
    qed
  qed
qed

subsection \<open>Multiplication\<close>

definition "nat_mul m n = natrec 0 (nat_add n) m"

lemma nat_mul_type [type]: "nat_mul: Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_mul_def by auto

bundle notation_nat_mul begin notation nat_mul (infixl "\<cdot>" 65) end
bundle no_notation_nat_mul begin no_notation nat_mul (infixl "\<cdot>" 65) end

unbundle no_notation_mul_implicit
unbundle notation_nat_mul

lemma nat_zero_mul [simp]: "0 \<cdot> n = 0"
  unfolding nat_mul_def by simp

lemma nat_mul_zero [simp]: "n: Nat \<Longrightarrow> n \<cdot> 0 = 0"
  by (induction n rule: Nat_induct) (auto simp: nat_mul_def)

lemma nat_one_mul [simp]: "n: Nat \<Longrightarrow> 1 \<cdot> n = n"
  unfolding nat_mul_def nat_one_def by auto

lemma nat_mul_one [simp]: "n: Nat \<Longrightarrow> n \<cdot> 1 = n"
  by (induction n rule: Nat_induct)
     (auto simp: nat_succ_add nat_mul_def nat_one_def)

lemma nat_succ_mul: "\<lbrakk>m: Nat; n: Nat\<rbrakk> \<Longrightarrow> succ m \<cdot> n = n + (m \<cdot> n)"
  by (induction m rule: Nat_induct)
     (simp add: nat_one_def[symmetric], simp add: nat_mul_def)

lemma nat_mul_dist_add_left:
  assumes "l: Nat" "m: Nat" "n: Nat"
  shows "l \<cdot> (m + n) = (l \<cdot> m) + (l \<cdot> n)"
using assms
proof (induction l arbitrary: n m rule: Nat_induct)
  case (induct l)
  from nat_succ_mul have "succ l \<cdot> (m + n) = (m + n) + (l \<cdot> (m + n))" by simp
  with induct.IH have "succ l \<cdot> (m + n) = (m + n) + ((l \<cdot> m) + (l \<cdot> n))" by simp
  then have "succ l \<cdot> (m + n) = m + (n + (l \<cdot> m) + (l \<cdot> n))"
    by (simp only: nat_add_assoc)
  then have "succ l \<cdot> (m + n) = m + ((l \<cdot> m) + n + (l \<cdot> n))"
    by (simp only: nat_add_comm)
  then have "succ l \<cdot> (m + n) = (m + (l \<cdot> m)) + (n + (l \<cdot> n))"
    by (simp only: nat_add_assoc)
  with nat_succ_mul show ?case by simp
qed simp

lemma nat_mul_comm: "m: Nat \<Longrightarrow> n: Nat \<Longrightarrow> m \<cdot> n = n \<cdot> m"
proof (induction m arbitrary: n rule: Nat_induct)
  case (induct m)
  with nat_succ_mul have "succ m \<cdot> n = n + (n \<cdot> m)" by simp
  then show ?case
    by (auto simp: nat_add_one_eq_succ[symmetric] nat_mul_dist_add_left nat_add_comm)
qed simp

lemma nat_mul_dist_add_right:
  assumes "l: Nat" "m: Nat" "n: Nat"
  shows "(l + m) \<cdot> n = (l \<cdot> n) + (m \<cdot> n)"
  by (simp only: nat_mul_comm nat_mul_dist_add_left)

lemma nat_mul_assoc:
  "l: Nat \<Longrightarrow> m: Nat \<Longrightarrow> n: Nat \<Longrightarrow> l \<cdot> m \<cdot> n = l \<cdot> (m \<cdot> n)"
  by (induction l arbitrary: n m rule: Nat_induct)
     (auto simp: nat_succ_mul nat_mul_dist_add_right)

lemma nat_zero_lt_mul [intro]:
  assumes "m: Nat" "n: Nat" and "0 < m" "0 < n"
  shows "0 < m \<cdot> n"
using assms
proof (induction m rule: Nat_induct)
  case (induct m)
  with nat_lt_add have "0 < n + (m \<cdot> n)" by simp
  with nat_succ_mul show ?case by simp
qed simp

lemma "nat_mul_eq_zero":
  assumes "m: Nat" "n: Nat" and "m \<cdot> n = 0"
  shows "m = 0 \<or> n = 0"
proof (rule ccontr)
  presume "m \<noteq> 0" and "n \<noteq> 0"
  with zero_lt_if_ne_zero have "0 < m" and "0 < n" using assms by simp_all
  with nat_zero_lt_mul have "0 < m \<cdot> n" using assms by blast
  with \<open>m \<cdot> n = 0\<close> have "0 < 0" by simp
  then show "False" by simp
qed auto

lemma nat_mul_eq_zeroE:
  assumes "m: Nat" "n: Nat" "m \<cdot> n = 0"
  obtains (left_zero) "m = 0" | (right_zero) "n = 0"
  using assms nat_mul_eq_zero by blast

lemma nat_mul_ne_zero:
  assumes "m: Nat" "n: Nat" and "m \<noteq> 0" "n \<noteq> 0"
  shows "m \<cdot> n \<noteq> 0"
  using zero_lt_if_ne_zero nat_mul_eq_zeroE[of m n] assms by simp

subsection \<open>More inequalities\<close>

lemma nat_lt_add_left [intro]:
  "\<lbrakk>a: Nat; b: Nat; 0 < b\<rbrakk> \<Longrightarrow> a < b + a"
  by (induction a rule: Nat_induct) auto

lemma nat_lt_add_right [intro]:
  "\<lbrakk>a: Nat; b: Nat; 0 < b\<rbrakk> \<Longrightarrow> a < a + b"
  by (induction a rule: Nat_induct) auto

lemma nat_le_add_left [intro]:
  "\<lbrakk>a: Nat; b: Nat\<rbrakk> \<Longrightarrow> a \<le> b + a"
  by (induction a rule: Nat_induct) (auto intro: succ_le_monotone)

lemma nat_le_add_right [intro]:
  "\<lbrakk>a: Nat; b: Nat\<rbrakk> \<Longrightarrow> a \<le> a + b"
  by (induction a rule: Nat_induct) (auto intro: succ_le_monotone)

lemma
  nat_succ_lt_succ_add_left:
    "\<lbrakk>a: Nat; b: Nat; 0 < b\<rbrakk> \<Longrightarrow> succ a < succ (b + a)"
and
  nat_succ_lt_succ_add_right:
    "\<lbrakk>a: Nat; b: Nat; 0 < b\<rbrakk> \<Longrightarrow> succ a < succ (a + b)"
and
  nat_succ_le_succ_add_left:
    "\<lbrakk>a: Nat; b: Nat\<rbrakk> \<Longrightarrow> succ a \<le> succ (b + a)"
and
  nat_succ_le_succ_add_right:
    "\<lbrakk>a: Nat; b: Nat\<rbrakk> \<Longrightarrow> succ a \<le> succ (a + b)"
by (auto simp add:
  succ_le_monotone nat_le_add_left nat_le_add_right
  nat_lt_add_left nat_lt_add_right)

lemma nat_add_lt_imp_left_lt:
  "\<lbrakk>a + b < c; a: Nat; b: Nat; c: Nat\<rbrakk> \<Longrightarrow> a < c"
proof (cases b rule: Nat_cases)
  case (succ b')
  assume "a + b < c" "a: Nat" "b: Nat" "c: Nat"
  moreover note \<open>b = succ b'\<close>
  ultimately have "a + succ b' < c" by simp
  moreover have "a < a + succ b'" by (rule nat_lt_add_right) auto
  ultimately show "a < c" using lt_trans by auto
qed simp_all

lemma nat_add_lt_imp_right_lt:
  "\<lbrakk>a + b < c; a: Nat; b: Nat; c: Nat\<rbrakk> \<Longrightarrow> b < c"
proof (cases a rule: Nat_cases)
  case (succ a')
  assume "a + b < c" "b: Nat" "c: Nat"
  moreover note \<open>a = succ a'\<close>
  ultimately have "succ a' + b < c" by simp
  moreover have "b < succ a' + b"
    using nat_lt_add_left[of b "succ a'"] by auto
  ultimately show "b < c" using lt_trans by auto
qed simp_all

lemma nat_add_le_imp_left_le:
  "\<lbrakk>a + b \<le> c; a: Nat; b: Nat; c: Nat\<rbrakk> \<Longrightarrow> a \<le> c"
proof (cases b rule: Nat_cases)
  case (succ b')
  assume "a + b \<le> c" "a: Nat" "b: Nat" "c: Nat"
  moreover note \<open>b = succ b'\<close>
  ultimately have "a + succ b' \<le> c" by simp
  moreover have "a \<le> a + succ b'" by (rule nat_le_add_right) auto
  ultimately show "a \<le> c" using le_trans by auto
qed simp_all

lemma nat_add_le_imp_right_le:
  "\<lbrakk>a + b \<le> c; a: Nat; b: Nat; c: Nat\<rbrakk> \<Longrightarrow> b \<le> c"
proof (cases a rule: Nat_cases)
  case (succ a')
  assume "a + b \<le> c" "b: Nat" "c: Nat"
  moreover note \<open>a = succ a'\<close>
  ultimately have "succ a' + b \<le> c" by simp
  moreover have "b \<le> succ a' + b"
    using nat_le_add_left[of b "succ a'"] by auto
  ultimately show "b \<le> c" using le_trans by simp
qed simp_all
    
lemma nat_add_lt_imp_lt_sub:
  assumes "a + b < c"
      and "a: Nat" "b: Nat" "c: Nat"
  shows "a < c - b"
using \<open>b: Nat\<close> \<open>c: Nat\<close> \<open>a + b < c\<close> proof (induction b arbitrary: c)
  case (induct b)
  from induct.prems have "a + b < pred c"
    by (auto intro: lt_pred_if_succ_lt)
  thus "a < c - succ b"
    using induct.IH by (simp add: nat_sub_succ nat_pred_sub[symmetric])
qed simp

lemma nat_lt_sub_imp_add_lt:
  assumes "a < c - b"
      and "a: Nat" "b: Nat" "c: Nat"
  shows "a + b < c"
using \<open>b: Nat\<close> \<open>c: Nat\<close> \<open>a < c - b\<close> proof (induction b arbitrary: c)
  case (induct b)
  then have "a + b < pred c" by (simp add: nat_sub_succ nat_pred_sub)
  thus "a + succ b < c" by (auto intro: succ_lt_if_lt_pred)
qed simp

corollary nat_add_lt_iff_lt_sub:
  assumes "a: Nat" "b: Nat" "c: Nat"
  shows "a + b < c \<longleftrightarrow> a < c - b"
  by (auto intro: nat_add_lt_imp_lt_sub nat_lt_sub_imp_add_lt)

lemma nat_lt_imp_lt_add_left:
  assumes "c < b"
      and "a: Nat" "b: Nat" "c: Nat"
  shows "c < a + b"
proof (cases a rule: Nat_cases)
  case (succ n)
  have "b \<le> n + b" by auto
  hence "b < succ n + b" using le_lt_lt by auto
  thus ?thesis using \<open>a = succ n\<close> \<open>c < b\<close> lt_trans by auto
qed auto

corollary nat_lt_imp_lt_add_right:
  "\<lbrakk>c < b; a: Nat; b: Nat; c: Nat\<rbrakk> \<Longrightarrow> c < b + a"
  by (subst nat_add_comm) (auto intro: nat_lt_imp_lt_add_left)

lemma nat_le_imp_le_add_left:
  assumes "c \<le> b"
      and "a: Nat" "b: Nat" "c: Nat"
  shows "c \<le> a + b"
proof (cases a rule: Nat_cases)
  case (succ n)
  have "b \<le> n + b" by auto
  hence "b \<le> succ n + b" using le_trans by auto
  thus ?thesis using \<open>a = succ n\<close> \<open>c \<le> b\<close> le_trans by auto
qed auto

corollary nat_le_imp_le_add_right:
  "\<lbrakk>c \<le> b; a: Nat; b: Nat; c: Nat\<rbrakk> \<Longrightarrow> c \<le> b + a"
  by (subst nat_add_comm) (auto intro: nat_le_imp_le_add_left)


section \<open>Algebraic structures\<close>

definition Nat_monoid ("'(\<nat>, +')")
  where "(\<nat>, +) \<equiv> object {\<langle>@zero, 0\<rangle>, \<langle>@add, \<lambda>m n\<in> \<nat>. nat_add m n\<rangle>}"

lemma "(\<nat>, +): Monoid \<nat>"
proof (rule MonoidI)
  show "(\<nat>, +): Zero \<nat>"
    by (rule Zero_typeI) (simp add: Nat_monoid_def)
  show "(\<nat>, +): Add \<nat>"
    by (rule Add_typeI) (unfold_types, auto simp: Nat_monoid_def)

  fix x assume "x \<in> \<nat>"
  show "add (\<nat>, +) (zero (\<nat>, +)) x = x"
   and "add (\<nat>, +) x (zero (\<nat>, +)) = x"
    \<comment> \<open>Very low-level; lots of unfolding.\<close>
    unfolding Nat_monoid_def add_def zero_def by auto

  fix y z assume "y \<in> \<nat>" "z \<in> \<nat>"
  show "add (\<nat>, +) (add (\<nat>, +) x y) z = add (\<nat>, +) x (add (\<nat>, +) y z)"
    unfolding Nat_monoid_def add_def zero_def
    using nat_add_assoc by auto
qed

definition Nat_mul_monoid ("'('\<nat>, \<cdot>')")
  where "(\<nat>, \<cdot>) \<equiv> object {\<langle>@one, 1\<rangle>, \<langle>@mul, \<lambda>m n\<in> \<nat>. nat_mul m n\<rangle>}"

lemma "(\<nat>, \<cdot>): Mul_Monoid \<nat>"
proof (rule Mul_MonoidI)
  show "(\<nat>, \<cdot>): One \<nat>"
    by (rule One_typeI) (simp add: Nat_mul_monoid_def)
  show "(\<nat>, \<cdot>): Mul \<nat>"
    by (rule Mul_typeI) (unfold_types, auto simp: Nat_mul_monoid_def)
next
  fix x assume "x \<in> \<nat>"
  show "mul (\<nat>, \<cdot>) (one (\<nat>, \<cdot>)) x = x"
   and "mul (\<nat>, \<cdot>) x (one (\<nat>, \<cdot>)) = x"
  unfolding Nat_mul_monoid_def mul_def one_def by auto
next
  fix x y z assume "x \<in> \<nat>" "y \<in> \<nat>" "z \<in> \<nat>"
  show "mul (\<nat>, \<cdot>) (mul (\<nat>, \<cdot>) x y) z = mul (\<nat>, \<cdot>) x (mul (\<nat>, \<cdot>) y z)"
    unfolding Nat_mul_monoid_def mul_def one_def
    using nat_mul_assoc by auto
qed


end
