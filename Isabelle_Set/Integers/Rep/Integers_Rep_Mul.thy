text \<open>Multiplication\<close>
theory Integers_Rep_Mul
imports Integers_Rep_Base
begin

definition "int_rep_mul x y \<equiv>
  if x = int_rep_zero \<or> y = int_rep_zero then int_rep_zero
  else int_rep_rec
    (\<lambda>m. int_rep_rec (\<lambda>n. int_rep_nonneg (m * n)) (\<lambda>n. int_rep_neg (m * n)) y)
    (\<lambda>m. int_rep_rec (\<lambda>n. int_rep_neg (m * n)) (\<lambda>n. int_rep_nonneg (m * n)) y)
    x"

lemma int_rep_zero_mul_eq [simp]:
  "int_rep_mul int_rep_zero x = int_rep_zero"
  unfolding int_rep_mul_def int_rep_zero_def by simp

lemma int_rep_nonneg_mul_nonneg_eq [simp]:
  assumes "n : Nat" "m : Nat"
  shows "int_rep_mul (int_rep_nonneg n) (int_rep_nonneg m) = int_rep_nonneg (n * m)"
  unfolding int_rep_mul_def int_rep_zero_def by simp

lemma int_rep_nonneg_mul_neg_eq [simp]:
  assumes "n : Nat" "m : Nat"
  and "n \<noteq> 0"
  shows "int_rep_mul (int_rep_nonneg n) (int_rep_neg m) = int_rep_neg (n * m)"
  using assms unfolding int_rep_mul_def int_rep_zero_def by simp

lemma int_rep_neg_mul_nonneg_eq [simp]:
  assumes "n : Nat" "m : Nat"
  and "m \<noteq> 0"
  shows "int_rep_mul (int_rep_neg n) (int_rep_nonneg m) = int_rep_neg (n * m)"
  using assms unfolding int_rep_mul_def int_rep_zero_def by simp

lemma int_rep_neg_mul_neg_eq [simp]:
  assumes "n : Nat" "m : Nat"
  shows "int_rep_mul (int_rep_neg n) (int_rep_neg m) = int_rep_nonneg (n * m)"
  using assms unfolding int_rep_mul_def int_rep_zero_def by simp

lemma int_rep_mul_zero_eq [simp]:
  "x \<in> int_rep \<Longrightarrow> int_rep_mul x int_rep_zero = int_rep_zero"
  unfolding int_rep_mul_def int_rep_zero_def by auto

lemma int_rep_mul_type [type]:
  "int_rep_mul : Element int_rep \<Rightarrow> Element int_rep \<Rightarrow> Element int_rep"
proof -
  {
    fix n m assume n_m_assms: "n \<in> \<nat>" "m \<in> \<nat>" "m \<noteq> 0"
    then have nonneg_neg:
      "int_rep_mul (int_rep_nonneg n) (int_rep_neg m) \<in> int_rep"
    proof (cases n rule: mem_natE)
      case (succ n)
      with n_m_assms have "succ n * m \<in> \<nat> \<setminus> {0}"
        using Nat_mul_ne_zero_if_ne_zero_if_ne_zero by auto
      with succ show ?thesis by auto
    qed (auto simp: int_rep_zero_def[symmetric])

    from n_m_assms have "m \<in> \<nat> \<setminus> {0}" by simp
    with \<open>m \<in> \<nat>\<close> \<open>m \<noteq> 0\<close> have
      "int_rep_mul (int_rep_neg m) (int_rep_nonneg n) \<in> int_rep"
    proof (cases n rule: mem_natE)
      case (succ n)
      with n_m_assms have "m * succ n \<in> \<nat> \<setminus> {0}"
        using Nat_mul_ne_zero_if_ne_zero_if_ne_zero by auto
      with succ show ?thesis by auto
    qed (auto simp: int_rep_zero_def[symmetric])
    note this nonneg_neg
  }
  note this[intro!]
  show ?thesis by (unfold_types, erule mem_int_repE; erule mem_int_repE)
    (auto simp: int_rep_zero_def)
qed

lemma int_rep_one_mul_eq [simp]: "x \<in> int_rep \<Longrightarrow> int_rep_mul int_rep_one x = x"
  unfolding int_rep_one_def
  by (elim mem_int_repE) (auto simp: nat_zero_ne_one[symmetric])

lemma int_rep_mul_one_eq [simp]: "x \<in> int_rep \<Longrightarrow> int_rep_mul x int_rep_one = x"
  unfolding int_rep_one_def
  by (elim mem_int_repE) (auto simp: nat_zero_ne_one[symmetric])

lemma int_rep_mul_assoc:
  assumes "x \<in> int_rep" "y \<in> int_rep" "z \<in> int_rep"
  shows "int_rep_mul (int_rep_mul x y) z = int_rep_mul x (int_rep_mul y z)"
  (*TODO: ugly proof*)
  unfolding int_rep_mul_def
  by (rule mem_int_repE[OF \<open>x \<in> _\<close>];
    rule mem_int_repE[OF \<open>y \<in> _\<close>];
    rule mem_int_repE[OF \<open>z \<in> _\<close>])
    (auto simp: Nat_mul_assoc int_rep_zero_def Nat_mul_eq_zero_iff)


end