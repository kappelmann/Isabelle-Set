\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Multiplication\<close>
theory TSNat_Mul
  imports TSNat_Add
begin

definition "nat_mul m n = nat_rec m 0 (nat_add n)"

lemma nat_mul_type [type]: "nat_mul \<Ztypecolon> Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_mul_def by auto

open_bundle isa_set_nat_mul_syntax begin notation nat_mul (infixl "*" 70) end

lemma zero_nat_mul_eq [simp]: "0 * n = 0"
  unfolding nat_mul_def by simp

lemma Nat_succ_mul_eq: "m \<Ztypecolon> Nat \<Longrightarrow> succ m * n = n + (m * n)"
  unfolding nat_mul_def by simp

lemma Nat_mul_zero_eq [simp]: "n \<Ztypecolon> Nat \<Longrightarrow> n * 0 = 0"
  by (induction n rule: Nat_induct) (auto simp: nat_mul_def)

lemma Nat_one_mul_eq [simp]: "n \<Ztypecolon> Nat \<Longrightarrow> 1 * n = n"
  unfolding nat_mul_def by simp

lemma Nat_mul_one_eq [simp]: "n \<Ztypecolon> Nat \<Longrightarrow> n * 1 = n"
  by (induction n rule: Nat_induct) (auto simp: nat_mul_def)

lemma Nat_mul_add_eq_mul_add_mul:
  assumes "l \<Ztypecolon> Nat" "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  shows "l * (m + n) = (l * m) + (l * n)"
using assms
proof (induction l rule: Nat_induct)
  case (succ l)
  from Nat_succ_mul_eq have "succ l * (m + n) = m + n + l * (m + n)" by simp
  also with succ.IH have "... = m + n + (l * m + l * n)" by simp
  also have "... = m + l * m + (n + l * n)" by (simp only: Nat_add_AC_rules)
  also have "... = succ l * m + succ l * n" by (simp only: Nat_succ_mul_eq)
  finally show ?case .
qed simp

lemma Nat_mul_comm: "m \<Ztypecolon> Nat \<Longrightarrow> n \<Ztypecolon> Nat \<Longrightarrow> m * n = n * m"
proof (induction m arbitrary: n rule: Nat_induct)
  case (succ m)
  with Nat_succ_mul_eq have "succ m * n = n + (n * m)" by simp
  then show ?case
    by (simp only: nat_add_one_eq_succ[of m, symmetric] Nat_mul_one_eq
    Nat_mul_add_eq_mul_add_mul Nat_add_comm)
qed simp

lemma Nat_add_mul_eq_mul_add_mul:
  assumes "l \<Ztypecolon> Nat" "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  shows "(l + m) * n = l * n + m * n"
  by (simp only: Nat_mul_comm Nat_mul_add_eq_mul_add_mul)

lemma Nat_mul_assoc:
  "l \<Ztypecolon> Nat \<Longrightarrow> m \<Ztypecolon> Nat \<Longrightarrow> n \<Ztypecolon> Nat \<Longrightarrow> l * m * n = l * (m * n)"
  by (induction l rule: Nat_induct)
    (auto simp: Nat_succ_mul_eq Nat_add_mul_eq_mul_add_mul)

lemma Nat_mul_comm_left:
  "\<lbrakk>l \<Ztypecolon> Nat; m \<Ztypecolon> Nat; n \<Ztypecolon> Nat\<rbrakk> \<Longrightarrow> l * (m * n) = m * (l * n)"
  by (induction l rule: Nat_induct)
    (auto simp: Nat_succ_mul_eq Nat_mul_add_eq_mul_add_mul)

lemmas Nat_mul_AC_rules = Nat_mul_comm Nat_mul_assoc Nat_mul_comm_left

lemma Nat_mul_ne_zero_if_ne_zero_if_ne_zero:
  assumes "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  and "m \<noteq> 0" "n \<noteq> 0"
  shows "m * n \<noteq> 0"
using assms
proof (induction m rule: Nat_induct)
  case (succ m)
  from \<open>n \<noteq> 0\<close> have "0 < n" by simp
  moreover have "... \<le> n + m * n" by (simp only: Nat_le_add)
  moreover have "... = succ m * n" by (simp only: Nat_succ_mul_eq)
  ultimately have "0 < succ m * n" by (simp only: lt_if_le_if_lt)
  then show ?case by simp
qed simp

corollary Nat_mul_eq_zero_iff:
  "\<lbrakk>m \<Ztypecolon> Nat; n \<Ztypecolon> Nat\<rbrakk> \<Longrightarrow> m * n = 0 \<longleftrightarrow> m = 0 \<or> n = 0"
  using Nat_mul_ne_zero_if_ne_zero_if_ne_zero by auto

corollary "Nat_mul_eq_zeroE":
  assumes "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  and "m * n = 0"
  obtains (left_zero) "m = 0" | (right_zero) "n = 0"
  using assms Nat_mul_eq_zero_iff by auto


end
