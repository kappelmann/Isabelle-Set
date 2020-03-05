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
  zero_nat [simp] = empty_in_omega[folded nat_def nat_zero_def] and
  succ_nat [simp] = succ_omega[folded nat_def] and
  nat_cases = omega_cases[folded nat_def nat_zero_def] and
  nat_induct [case_names 0 induct, induct set: nat] =
    omega_induct[folded nat_def nat_zero_def] and
  nat_elems = omega_elems[folded nat_def nat_zero_def] and
  succ_not_empty [simp] = Ordinal.succ_not_empty[folded nat_zero_def] and
  empty_not_succ [simp] = Ordinal.empty_not_succ[folded nat_zero_def]


text \<open>Truncated predecessor function\<close>

definition "pred n = (if n = 0 then 0 else (THE m \<in> \<nat>. n = succ m))"

lemma pred_nonzero:
  "\<lbrakk>n \<in> \<nat>; n \<noteq> 0\<rbrakk> \<Longrightarrow> pred n = (THE m \<in> \<nat>. n = succ m)"
  unfolding pred_def by auto

lemma pred_nat [simp]: "n \<in> \<nat> \<Longrightarrow> pred n \<in> \<nat>"
  unfolding pred_def by (auto intro: btheI1 nat_elems)

lemma pred_zero [simp]: "pred 0 = 0"
  unfolding pred_def by auto

lemma pred_succ [simp]: "n \<in> \<nat> \<Longrightarrow> pred (succ n) = n"
  unfolding pred_def by auto

lemma succ_pred [simp]: "\<lbrakk>n \<in> \<nat>; n \<noteq> 0\<rbrakk> \<Longrightarrow> succ (pred n) = n"
  unfolding pred_def by (simp, rule sym, rule btheI2) (fact nat_elems)


section \<open>\<nat> as a type\<close>

abbreviation "Nat \<equiv> element \<nat>"

lemmas Nat_induct = nat_induct
  [ simplified element_type_iff,
    case_names base induct,
    induct pred: Nat ]

lemmas Nat_cases = nat_cases[simplified element_type_iff]

lemma Nat_Ord [derive]: "x : Nat \<Longrightarrow> x : Ord"
  by (induct x rule: Nat_induct) (auto intro: succ_Ord simp: nat_zero_def)

lemma
  zero_type [type]: "0 : Nat" and
  succ_type [type]: "succ : Nat \<Rightarrow> Nat" and
  pred_type [type]: "pred : Nat \<Rightarrow> Nat"
  by unfold_types auto

lemma one_type [type]: "1 : Nat"
  unfolding nat_one_def by auto


section \<open>The \<open><\<close> and \<open>\<le>\<close> orders on Nat\<close>

definition lt (infix "<" 60) where "m < n = (m \<in> n)"

lemmas
  lt_succ [simp] = succ_mem[folded lt_def] and
  lt_succ_cases = succ_cases[folded lt_def]

lemma succ_lt_monotone:
  "n : Nat \<Longrightarrow> m < n \<Longrightarrow> succ m < succ n"
  unfolding lt_def by unfold_types (auto simp: nat_def)

lemma succ_lt_monotoneE:
  "\<lbrakk>n: Nat; succ m < succ n\<rbrakk> \<Longrightarrow> m < n"
  unfolding lt_def
  by unfold_types (auto intro: omega_succ_mem_monotoneE simp: nat_def)

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

lemma lt_imp_le: "m < n \<Longrightarrow> m \<le> n"
  unfolding le_def ..

lemma succ_le_monotone:
  "\<lbrakk>n: Nat; m \<le> n\<rbrakk> \<Longrightarrow> succ m \<le> succ n"
  unfolding le_def using succ_lt_monotone by auto

lemma succ_lt_le_monotone:
  "\<lbrakk>n: Nat; m < n\<rbrakk> \<Longrightarrow> succ m \<le> succ n"
  unfolding le_def using succ_lt_monotone by auto

lemma lt_0 [simp]: "n : Nat \<Longrightarrow> 0 < succ n"
  unfolding lt_def nat_def nat_zero_def
  by unfold_types (fact omega_empty_in_succ)

lemma zero_ltE [elim]: "n < 0 \<Longrightarrow> P"
  unfolding lt_def nat_zero_def by auto

corollary [simp]: "\<not> n < 0" by auto

lemma zero_lt_imp_neq [simp]: "0 < n \<Longrightarrow> n \<noteq> 0"
  by auto

lemma
  not_succ_lt [simp]: "\<not> succ n < n" and
  not_succ_lt_succ [simp]: "\<not> succ n < succ n"
  unfolding lt_def by auto

lemma nat_neq_zero_imp_zero_lt:
  "n: Nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> 0 < n"
  using nat_elems by unfold_types force

lemma le_0 [simp]: "n \<le> 0 \<Longrightarrow> n = 0"
  unfolding le_def by auto

lemma lt_imp_Nat [elim]: "n: Nat \<Longrightarrow> m < n \<Longrightarrow> m: Nat"
  unfolding nat_def lt_def by unfold_types (fact omega_mem_transitive)

(*Case splits*)
lemma le_cases:
  assumes "n: Nat"
      and "m \<le> n"
      and "\<And>m. m < n \<Longrightarrow> P m"
      and "P n"
  shows "P m"
  using assms unfolding le_def by auto

lemma lt_asym: "\<lbrakk>m < n; n < m\<rbrakk> \<Longrightarrow> P"
  unfolding lt_def using mem_asym by blast

lemma lt_transitive:
  "n : Nat \<Longrightarrow> k < m \<Longrightarrow> m < n \<Longrightarrow> k < n"
  unfolding lt_def nat_def
  by unfold_types (auto intro: omega_elem_mem_transitive')

lemma
  le_transitive: "n: Nat \<Longrightarrow> k \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> k \<le> n" and
  le_lt_lt:      "n: Nat \<Longrightarrow> k \<le> m \<Longrightarrow> m < n \<Longrightarrow> k < n" and
  lt_le_lt:      "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m \<le> n \<Longrightarrow> k < n" and
  lt_le_le:      "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m \<le> n \<Longrightarrow> k \<le> n" and
  le_lt_le:      "n: Nat \<Longrightarrow> k \<le> m \<Longrightarrow> m < n \<Longrightarrow> k \<le> n" and
  lt_lt_le:      "n: Nat \<Longrightarrow> k < m \<Longrightarrow> m < n \<Longrightarrow> k \<le> n"
  unfolding le_def by (auto intro: lt_transitive)

lemma succ_lt: "\<lbrakk>m: Nat; n: Nat; succ m < n\<rbrakk> \<Longrightarrow> m < n"
  unfolding succ_def lt_def nat_def
  by unfold_types (auto dest: omega_elem_Ord Ord_mem_transitive')

lemma succ_zero_lt:
  "\<lbrakk>m: Nat; n: Nat\<rbrakk> \<Longrightarrow> succ m < n \<Longrightarrow> 0 < n"
  by (rule lt_transitive) auto

lemma pred_lt_monotone [intro]:
  assumes "m: Nat" "n: Nat"
      and "0 < m" "m < n"
  shows "pred m < pred n"
proof -
  have "m \<in> \<nat>" "n \<in> \<nat>" "m \<noteq> 0" "n \<noteq> 0"
    using assms by auto
  then obtain k k' where "k \<in> \<nat>" "k'\<in> \<nat>" and
    *: "m = succ k" "n = succ k'"
    using nat_elems by blast
  then have "succ k < succ k'"
    using assms by simp
  thus ?thesis
    using succ_lt_monotoneE by (auto simp only: * pred_succ)
qed

lemma succ_lt_imp_lt_pred:
  assumes "m: Nat" "n: Nat" "succ n < m"
  shows "n < pred m"
proof (rule succ_lt_monotoneE, discharge_types)
  have "m \<noteq> 0" using assms by auto
  thus "succ n < succ (pred m)" by auto
qed


section \<open>Ranges\<close>

definition upto ("{0, ..., _}") where "{0, ..., n} = {i \<in> \<nat> | i \<le> n}"

lemma succ_eq_upto: "n: Nat \<Longrightarrow> succ n = {0, ..., n}"
  unfolding succ_def upto_def le_def lt_def
  by unfold_types (auto intro: equalityI omega_mem_transitive simp: nat_def)

lemmas upto_eq_succ = succ_eq_upto[symmetric]

lemma uptoI: "n: Nat \<Longrightarrow> m \<le> n \<Longrightarrow> m \<in> {0, ..., n}"
  by unfold_types (auto simp: upto_eq_succ le_def lt_def)

lemma uptoE1: "m \<in> {0, ..., n} \<Longrightarrow> m: Nat"
  unfolding upto_def by auto

lemmas [derive] = uptoE1[simplified element_type_iff]

lemma uptoE2: "m \<in> {0, ..., n} \<Longrightarrow> m \<le> n"
  unfolding upto_def by auto

lemma le_iff_upto: "n: Nat \<Longrightarrow> m \<le> n = (m \<in> {0, ..., n})"
  by (auto intro: uptoI elim: uptoE2)

lemmas upto_iff_le = le_iff_upto[symmetric]

lemma [derive]: "n: Nat \<Longrightarrow> 0: element {0, ..., n}"
  by
    (simp add: upto_eq_succ nat_def nat_zero_def, unfold_types)
    (auto intro: omega_empty_in_succ)

lemma
  [derive]: "n: Nat \<Longrightarrow> n: element {0, ..., n}" and
  [derive]: "n: Nat \<Longrightarrow> m: element n \<Longrightarrow> m: element {0, ..., n}"
  by unfold_types (auto simp: upto_eq_succ)

lemma upto_subset_upto [intro!]: "n: Nat \<Longrightarrow> m < n \<Longrightarrow> {0, ..., m} \<subseteq> {0, ..., n}"
  unfolding upto_def le_def by (auto intro: lt_transitive)

lemma le_induct_raw:
  "n: Nat \<Longrightarrow> P 0 \<Longrightarrow> (\<forall>m. m < n \<longrightarrow> P m \<longrightarrow> P (succ m)) \<longrightarrow> (\<forall>m. m \<le> n \<longrightarrow> P m)"
text \<open>Proof sketch: case n = 0 is easy, case n > 0 is by induction.\<close>
proof (cases n rule: Nat_cases, assumption; rule impI)
  assume "P 0"
  then show "\<forall>m. m \<le> 0 \<longrightarrow> P m" by (auto dest: le_0)
next
  fix n assume assms:
    "n: Nat"
    "P 0"
    "(\<forall>m. m < succ n \<longrightarrow> P m \<longrightarrow> P (succ m))"
  show "\<forall>m. m \<le> succ n \<longrightarrow> P m"
  proof clarify
    have succ_n: "succ n: Nat" using assms by auto

    { fix m have "m: Nat \<Longrightarrow> m < succ n \<Longrightarrow> P m"
      proof (induction m rule: Nat_induct)
        show "P 0" by (fact assms)
      next
        fix k assume assms': "k: Nat" "k < succ n \<Longrightarrow> P k" "succ k < succ n"
        then have "k < succ n" by (auto intro: succ_lt)
        moreover have "P k" using assms' by auto
        ultimately show "P (succ k)" using assms(3) by auto
      qed
      hence "m < succ n \<Longrightarrow> P m" using lt_imp_Nat[OF succ_n] by auto
    }
    hence 1: "\<And>m. m < succ n \<Longrightarrow> P m" by auto
    hence 2: "P (succ n)" using assms(3) by auto

    fix m show "m \<le> succ n \<Longrightarrow> P m" using 1 2 by (auto elim: le_cases[OF succ_n])
  qed
qed

lemma le_induct:
  assumes "n: Nat"
      and "m \<le> n"
      and "P 0"
      and "\<And>m. m < n \<Longrightarrow> P m \<Longrightarrow> P (succ m)"
  shows "P m"
  using le_induct_raw assms by auto

lemma cons_upto_FunctionI [intro]:
  assumes "n: Nat"
      and "f \<in> {0, ..., n} \<rightarrow> X"
      and "x \<in> X"
  shows "cons \<langle>succ n, x\<rangle> f \<in> {0, ..., succ n} \<rightarrow> X"
  by
    (simp only: upto_eq_succ, subst (2) succ_def)
    (auto intro: assms cons_FunctionI' simp: succ_eq_upto mem_irrefl)


section \<open>Recursion\<close>

text \<open>Recursion on Nat. Axiomatized, for now.\<close>

axiomatization natrec :: \<open>set \<Rightarrow> (set \<Rightarrow> set) \<Rightarrow> set \<Rightarrow> set\<close> where
  natrec_0 [simp]: "natrec x\<^sub>0 f 0 = x\<^sub>0" and
  natrec_succ [simp]: "natrec x\<^sub>0 f (succ n) = f (natrec x\<^sub>0 f n)"

lemma natrec_type [type]:
  "natrec : X \<Rightarrow> (X \<Rightarrow> X) \<Rightarrow> Nat \<Rightarrow> X"
proof (intro typeI)
  fix x f n
  show "n: Nat \<Longrightarrow> x: X \<Longrightarrow> f: X \<Rightarrow> X \<Longrightarrow> natrec x f n: X"
  by (induct n rule: Nat_induct) auto
qed


section \<open>Arithmetic\<close>

named_theorems arith

subsection \<open>Addition\<close>

definition [arith]: "nat_add m n = natrec m succ n"

lemma nat_add_type [type]: "nat_add : Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_add_def by auto

bundle notation_nat_add begin notation nat_add (infixl "+" 65) end
bundle no_notation_nat_add begin no_notation nat_add (infixl "+" 65) end

unbundle
  no_notation_add_implicit
  notation_nat_add

lemma nat_add_zero_left [simp]:
  "m: Nat \<Longrightarrow> 0 + m = m"
  unfolding nat_add_def
  by (induction m rule: Nat_induct) auto

lemma nat_add_zero_right [simp]:
  "m: Nat \<Longrightarrow> m + 0 = m"
  unfolding nat_add_def
  by (induction m rule: Nat_induct) auto

lemma nat_add_assoc [simp]:
  "k: Nat \<Longrightarrow> n: Nat \<Longrightarrow> m: Nat \<Longrightarrow> m + n + k = m + (n + k)"
apply (induct k rule: Nat_induct)
  subgoal
    by simp
  subgoal
    unfolding nat_add_def
    by (rotate_tac, rotate_tac, induct n rule: Nat_induct) auto
done

lemma nat_add_nonzero [simp]:
  assumes
    "m: Nat" "n: Nat"
    "m \<noteq> 0" "n \<noteq> 0"
  shows "m + n \<noteq> 0"
proof (insert assms(2), induction n rule: Nat_induct)
  show "m + 0 \<noteq> 0"
    using assms by auto
  show "\<And>n. n : Nat \<Longrightarrow> m + n \<noteq> 0 \<Longrightarrow> m + succ n \<noteq> 0"
    unfolding nat_add_def by auto
qed

subsection \<open>Subtraction (truncated)\<close>

definition [arith]: "nat_sub m n = natrec m pred n"

lemma nat_sub_type [type]: "nat_sub : Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_sub_def by auto

bundle notation_nat_sub begin notation nat_sub (infixl "-" 65) end
bundle no_notation_nat_sub begin no_notation nat_sub (infixl "-" 65) end

unbundle notation_nat_sub

lemma nat_sub_zero [simp]: "m - 0 = m"
  unfolding nat_sub_def by auto

lemma nat_sub_succ [simp]:
  "n: Nat \<Longrightarrow> m: Nat \<Longrightarrow> succ m - succ n = m - n"
  by (induction n rule: Nat_induct) (simp_all add: arith)

lemma nat_sub_lt [simp]:
  "\<lbrakk>n: Nat; m: Nat; n < m\<rbrakk> \<Longrightarrow> 0 < m - n"
proof (induction n arbitrary: m rule: Nat_induct, clarsimp)
  fix m n assume "m: Nat" "n: Nat" and
    hyp: "\<And>m. m : Nat \<Longrightarrow> n < m \<Longrightarrow> 0 < m - n"
  have "succ n < m \<longrightarrow> 0 < m - succ n"
  proof (cases m rule: Nat_cases, simp, simp, clarsimp)
    show "\<And>k. k : Nat \<Longrightarrow> succ n < succ k \<Longrightarrow> 0 < k - n"
    using hyp by (auto intro: succ_lt_monotoneE)
  qed
  thus "succ n < m \<Longrightarrow> 0 < m - succ n" ..
qed

subsection \<open>Multiplication\<close>

definition [arith]: "nat_mul m n = natrec 0 (nat_add m) n"

lemma nat_mul_type [type]: "nat_mul : Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_mul_def by auto

bundle notation_nat_mul begin notation nat_mul (infixl "\<cdot>" 65) end
bundle no_notation_nat_mul begin no_notation nat_mul (infixl "\<cdot>" 65) end

unbundle no_notation_mul_implicit
unbundle notation_nat_mul

lemma nat_mul_nonzero [simp]:
  assumes
    "m: Nat" "n: Nat"
    "m \<noteq> 0" "n \<noteq> 0"
  shows "m \<cdot> n \<noteq> 0"
oops


section \<open>Monoid structure of (\<nat>, +)\<close>

definition Nat_monoid ("'(\<nat>, +')")
  where "(\<nat>, +) \<equiv> object {\<langle>@zero, 0\<rangle>, \<langle>@add, \<lambda>m n\<in> \<nat>. nat_add m n\<rangle>}"

lemma "(\<nat>, +): Monoid \<nat>"
proof unfold_types
  show "(\<nat>, +) @@ zero \<in> \<nat>"
   and "(\<nat>, +) @@ add \<in> \<nat> \<rightarrow> \<nat> \<rightarrow> \<nat>"
  unfolding Nat_monoid_def by auto

  fix x assume "x \<in> \<nat>"
  show "add (\<nat>, +) (zero (\<nat>, +)) x = x"
   and "add (\<nat>, +) x (zero (\<nat>, +)) = x"
  \<comment> \<open>Very low-level; lots of unfolding.\<close>
  unfolding Nat_monoid_def add_def zero_def
  using nat_add_zero_left nat_add_zero_right
  by auto

  fix y z assume "y \<in> \<nat>" "z \<in> \<nat>"
  show
    "add (\<nat>, +) (add (\<nat>, +) x y) z =
      add (\<nat>, +) x (add (\<nat>, +) y z)"
  unfolding Nat_monoid_def add_def zero_def
  using nat_add_assoc by auto
qed


end
