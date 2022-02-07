text \<open>Multiplication\<close>
theory Integers_Rep_Mul
imports Integers_Rep_Base
begin

definition "Int_Rep_mul x y \<equiv>
  if x = Int_Rep_zero \<or> y = Int_Rep_zero then Int_Rep_zero
  else Int_Rep_rec
    (\<lambda>m. Int_Rep_rec (\<lambda>n. Int_Rep_nonneg (m * n)) (\<lambda>n. Int_Rep_neg (m * n)) y)
    (\<lambda>m. Int_Rep_rec (\<lambda>n. Int_Rep_neg (m * n)) (\<lambda>n. Int_Rep_nonneg (m * n)) y)
    x"

lemma Int_Rep_zero_mul_eq [simp]:
  "Int_Rep_mul Int_Rep_zero x = Int_Rep_zero"
  unfolding Int_Rep_mul_def Int_Rep_zero_def by simp

lemma Int_Rep_nonneg_mul_nonneg_eq [simp]:
  assumes "n : Nat" "m : Nat"
  shows "Int_Rep_mul (Int_Rep_nonneg n) (Int_Rep_nonneg m) = Int_Rep_nonneg (n * m)"
  unfolding Int_Rep_mul_def Int_Rep_zero_def by simp

lemma Int_Rep_nonneg_mul_neg_eq [simp]:
  assumes "n : Nat" "m : Nat"
  and "n \<noteq> 0"
  shows "Int_Rep_mul (Int_Rep_nonneg n) (Int_Rep_neg m) = Int_Rep_neg (n * m)"
  using assms unfolding Int_Rep_mul_def Int_Rep_zero_def by simp

lemma Int_Rep_neg_mul_nonneg_eq [simp]:
  assumes "n : Nat" "m : Nat"
  and "m \<noteq> 0"
  shows "Int_Rep_mul (Int_Rep_neg n) (Int_Rep_nonneg m) = Int_Rep_neg (n * m)"
  using assms unfolding Int_Rep_mul_def Int_Rep_zero_def by simp

lemma Int_Rep_neg_mul_neg_eq [simp]:
  assumes "n : Nat" "m : Nat"
  shows "Int_Rep_mul (Int_Rep_neg n) (Int_Rep_neg m) = Int_Rep_nonneg (n * m)"
  using assms unfolding Int_Rep_mul_def Int_Rep_zero_def by simp

lemma Int_Rep_mul_zero_eq [simp]:
  "x : Int_Rep \<Longrightarrow> Int_Rep_mul x Int_Rep_zero = Int_Rep_zero"
  unfolding Int_Rep_mul_def Int_Rep_zero_def by auto

lemma Int_Rep_mul_type [type]:
  "Int_Rep_mul : Int_Rep \<Rightarrow> Int_Rep \<Rightarrow> Int_Rep"
proof -
  {
    fix n m assume n_m_assms: "n \<in> \<nat>" "m \<in> \<nat>" "m \<noteq> 0"
    then have nonneg_neg:
      "Int_Rep_mul (Int_Rep_nonneg n) (Int_Rep_neg m) : Int_Rep"
    proof (cases n rule: mem_natE)
      case (succ n)
      with n_m_assms have "succ n * m \<in> \<nat> \<setminus> {0}"
        using Nat_mul_ne_zero_if_ne_zero_if_ne_zero by auto
      with succ show ?thesis by auto
    qed (auto simp: Int_Rep_zero_def[symmetric])

    from n_m_assms have "m \<in> \<nat> \<setminus> {0}" by simp
    with \<open>m \<in> \<nat>\<close> \<open>m \<noteq> 0\<close> have
      "Int_Rep_mul (Int_Rep_neg m) (Int_Rep_nonneg n) : Int_Rep"
    proof (cases n rule: mem_natE)
      case (succ n)
      with n_m_assms have "m * succ n \<in> \<nat> \<setminus> {0}"
        using Nat_mul_ne_zero_if_ne_zero_if_ne_zero by auto
      with succ show ?thesis by auto
    qed (auto simp: Int_Rep_zero_def[symmetric])
    note this nonneg_neg
  }
  note this[intro!]
  show ?thesis by (intro Dep_fun_typeI, erule mem_Int_RepE; erule mem_Int_RepE)
    (auto simp: Int_Rep_zero_def)
qed

lemma Int_Rep_one_mul_eq [simp]: "x : Int_Rep \<Longrightarrow> Int_Rep_mul Int_Rep_one x = x"
  unfolding Int_Rep_one_def
  by (elim mem_Int_RepE) (auto simp: nat_zero_ne_one[symmetric])

lemma Int_Rep_mul_one_eq [simp]: "x : Int_Rep \<Longrightarrow> Int_Rep_mul x Int_Rep_one = x"
  unfolding Int_Rep_one_def
  by (elim mem_Int_RepE) (auto simp: nat_zero_ne_one[symmetric])

lemma Int_Rep_mul_assoc:
  assumes "x : Int_Rep" "y : Int_Rep" "z : Int_Rep"
  shows "Int_Rep_mul (Int_Rep_mul x y) z = Int_Rep_mul x (Int_Rep_mul y z)"
  (*TODO: ugly proof*)
  unfolding Int_Rep_mul_def
  by (rule mem_Int_RepE[OF \<open>x : _\<close>];
    rule mem_Int_RepE[OF \<open>y : _\<close>];
    rule mem_Int_RepE[OF \<open>z : _\<close>])
    (auto simp: Nat_mul_assoc Int_Rep_zero_def Nat_mul_eq_zero_iff)


end