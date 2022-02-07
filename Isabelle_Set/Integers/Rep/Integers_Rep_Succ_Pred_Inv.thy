text \<open>Successor, Predecessor, and Inverse\<close>
theory Integers_Rep_Succ_Pred_Inv
  imports Integers_Rep_Base
begin

definition "Int_Rep_succ \<equiv> Int_Rep_rec (\<lambda>n. Int_Rep_nonneg (succ n))
  (\<lambda>n. (if n = 1 then Int_Rep_nonneg else Int_Rep_neg) (pred n))"

lemma Int_Rep_succ_nonneg_eq [simp]:
  "Int_Rep_succ (Int_Rep_nonneg n) = Int_Rep_nonneg (succ n)"
  unfolding Int_Rep_succ_def by simp

lemma Int_Rep_succ_neg_one_eq [simp]:
  "Int_Rep_succ (Int_Rep_neg 1) = Int_Rep_zero"
  unfolding Int_Rep_succ_def nat_one_def Int_Rep_zero_def by simp

lemma Int_Rep_succ_neg_eq [simp]:
  "n \<noteq> 1 \<Longrightarrow> Int_Rep_succ (Int_Rep_neg n) = Int_Rep_neg (pred n)"
  unfolding Int_Rep_succ_def by simp

lemma Int_Rep_succ_type [type]: "Int_Rep_succ : Int_Rep \<Rightarrow> Int_Rep"
proof -
  {
    fix n assume "n \<in> \<nat>" "n \<noteq> 0" "n \<noteq> 1"
    then have "pred n \<in> \<nat> \<setminus> {0}" using Nat_pred_eq_zero_iff by auto
    then have "Int_Rep_neg (pred n) : Int_Rep" by discharge_types
  }
  note this[intro]
  show ?thesis
    unfolding Int_Rep_succ_def by (intro Dep_fun_typeI, elim mem_Int_RepE) auto
qed

definition "Int_Rep_pred \<equiv> Int_Rep_rec
  (\<lambda>n. if n = 0 then Int_Rep_neg 1 else Int_Rep_nonneg (pred n))
  (\<lambda>n. Int_Rep_neg (succ n))"

lemma Int_Rep_pred_neg_eq [simp]:
  "Int_Rep_pred (Int_Rep_neg n) = Int_Rep_neg (succ n)"
  unfolding Int_Rep_pred_def by simp

lemma Int_Rep_pred_zero_eq_neg_one [simp]:
  "Int_Rep_pred Int_Rep_zero = Int_Rep_neg 1"
  unfolding Int_Rep_pred_def Int_Rep_zero_def by simp

lemma Int_Rep_pred_nonneg_eq [simp]:
  "n \<noteq> 0 \<Longrightarrow> Int_Rep_pred (Int_Rep_nonneg n) = Int_Rep_nonneg (pred n)"
  unfolding Int_Rep_pred_def by simp

lemma Int_Rep_pred_type [type]:
  "Int_Rep_pred : Int_Rep \<Rightarrow> Int_Rep"
  unfolding Int_Rep_pred_def nat_one_def
  by (intro Dep_fun_typeI, elim mem_Int_RepE) auto

lemma Int_Rep_pred_succ_eq [simp]:
  assumes "x : Int_Rep"
  shows "Int_Rep_pred (Int_Rep_succ x) = x"
using assms
proof (cases x rule: mem_Int_RepE)
  case (neg n)
  then show ?thesis by (cases "n = 1") auto
qed simp

lemma Int_Rep_succ_pred_eq [simp]:
  assumes "x : Int_Rep"
  shows "Int_Rep_succ (Int_Rep_pred x) = x"
using assms
proof (cases x rule: mem_Int_RepE)
  case (nonneg n)
  then show ?thesis by (cases "n = 0") (auto simp: Int_Rep_zero_def[symmetric])
next
  case (neg n)
  then have "succ n \<noteq> 1" unfolding nat_one_def by auto
  with neg show ?thesis by auto
qed

definition "Int_Rep_inv \<equiv> Int_Rep_rec
  (\<lambda>n. (if n = 0 then Int_Rep_nonneg else Int_Rep_neg) n)
  Int_Rep_nonneg"

lemma
  assumes "n : Nat"
  shows "(if n = 0 then Int_Rep_nonneg n else Int_Rep_neg n) : Int_Rep"
proof -
  {
    assume "n \<noteq> 0"
    then have "n : Element (\<nat> \<setminus> {0})" by (auto intro: ElementI)
  }
  then show ?thesis by auto
qed

lemma Int_Rep_inv_zero_eq [simp]: "Int_Rep_inv Int_Rep_zero = Int_Rep_zero"
  unfolding Int_Rep_inv_def Int_Rep_zero_def by simp

lemma Int_Rep_inv_nonneg_eq [simp]:
  "n \<noteq> 0 \<Longrightarrow> Int_Rep_inv (Int_Rep_nonneg n) = Int_Rep_neg n"
  unfolding Int_Rep_inv_def by simp

lemma Int_Rep_inv_neg_eq [simp]:
  "Int_Rep_inv (Int_Rep_neg n) = Int_Rep_nonneg n"
  unfolding Int_Rep_inv_def by simp

lemma Int_Rep_inv_type [type]: "Int_Rep_inv : Int_Rep \<Rightarrow> Int_Rep"
proof -
  {
    fix n assume "n \<in> \<nat>" "n \<noteq> 0"
    then have "n : Element (\<nat> \<setminus> {0})" by (auto intro: ElementI)
  }
  note this[dest]
  show ?thesis
    unfolding Int_Rep_inv_def by (intro Dep_fun_typeI, elim mem_Int_RepE) auto
qed

lemma Int_Rep_inv_inv_eq [simp]:
  "x : Int_Rep \<Longrightarrow> Int_Rep_inv (Int_Rep_inv x) = x"
  by (erule mem_Int_RepE, erule mem_natE) (auto simp: Int_Rep_zero_def[symmetric])

lemma Int_Rep_pred_inv_eq_inv_succ:
  assumes "x : Int_Rep"
  shows "Int_Rep_pred (Int_Rep_inv x) = Int_Rep_inv (Int_Rep_succ x)"
proof -
  {
    fix n assume "n \<in> \<nat>"
    then have
      "Int_Rep_nonneg n = Int_Rep_inv (Int_Rep_succ (Int_Rep_neg (succ n)))"
    proof (cases n rule: mem_natE)
      case zero
      then show ?thesis
        by (simp add: nat_one_def[symmetric] Int_Rep_zero_def[symmetric])
    next
      case (succ n)
      have "succ (succ n) \<noteq> 1" unfolding nat_one_def by auto
      with succ show ?thesis by simp
    qed
  }
  note this[intro!]
  from assms show ?thesis
    by (elim mem_Int_RepE)
    (auto elim: mem_natE simp: Int_Rep_zero_def[symmetric] nat_one_def)
qed

corollary Int_Rep_inv_pred_inv_eq_succ [simp]:
  assumes "x : Int_Rep"
  shows "Int_Rep_inv (Int_Rep_pred (Int_Rep_inv x)) = Int_Rep_succ x"
  using Int_Rep_pred_inv_eq_inv_succ by simp

corollary Int_Rep_succ_inv_eq_inv_pred:
  assumes "x : Int_Rep"
  shows "Int_Rep_succ (Int_Rep_inv x) = Int_Rep_inv (Int_Rep_pred x)"
  using Int_Rep_inv_pred_inv_eq_succ[of "Int_Rep_inv x"] by simp

corollary Int_Rep_inv_succ_inv_eq_pred [simp]:
  assumes "x : Int_Rep"
  shows "Int_Rep_inv (Int_Rep_succ (Int_Rep_inv x)) = Int_Rep_pred x"
  using Int_Rep_succ_inv_eq_inv_pred by simp


end