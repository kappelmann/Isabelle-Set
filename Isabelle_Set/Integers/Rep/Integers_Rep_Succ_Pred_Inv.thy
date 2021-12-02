text \<open>Successor, Predecessor, and Inverse\<close>
theory Integers_Rep_Succ_Pred_Inv
imports Integers_Rep_Base
begin

definition "int_rep_succ \<equiv> int_rep_rec (\<lambda>n. int_rep_nonneg (succ n))
  (\<lambda>n. (if n = 1 then int_rep_nonneg else int_rep_neg) (pred n))"

lemma int_rep_succ_nonneg_eq [simp]:
  "int_rep_succ (int_rep_nonneg n) = int_rep_nonneg (succ n)"
  unfolding int_rep_succ_def by simp

lemma int_rep_succ_neg_one_eq [simp]:
  "int_rep_succ (int_rep_neg 1) = int_rep_zero"
  unfolding int_rep_succ_def nat_one_def int_rep_zero_def by simp

lemma int_rep_succ_neg_eq [simp]:
  "n \<noteq> 1 \<Longrightarrow> int_rep_succ (int_rep_neg n) = int_rep_neg (pred n)"
  unfolding int_rep_succ_def by simp

lemma int_rep_succ_type [type]:
  "int_rep_succ : Element int_rep \<Rightarrow> Element int_rep"
proof -
  {
    fix n assume "n \<in> \<nat>" "n \<noteq> 0" "n \<noteq> 1"
    then have "pred n \<in> \<nat> \<setminus> {0}" using Nat_pred_eq_zero_iff by auto
    then have "int_rep_neg (pred n) \<in> int_rep" by discharge_types
  }
  note this[intro]
  show ?thesis unfolding int_rep_succ_def
    by (unfold_types, elim mem_int_repE) (auto simp: Nat_pred_eq_zero_iff)
qed

definition "int_rep_pred \<equiv> int_rep_rec
  (\<lambda>n. if n = 0 then int_rep_neg 1 else int_rep_nonneg (pred n))
  (\<lambda>n. int_rep_neg (succ n))"

lemma int_rep_pred_neg_eq [simp]:
  "int_rep_pred (int_rep_neg n) = int_rep_neg (succ n)"
  unfolding int_rep_pred_def by simp

lemma int_rep_pred_zero_eq_neg_one [simp]:
  "int_rep_pred int_rep_zero = int_rep_neg 1"
  unfolding int_rep_pred_def int_rep_zero_def by simp

lemma int_rep_pred_nonneg_eq [simp]:
  "n \<noteq> 0 \<Longrightarrow> int_rep_pred (int_rep_nonneg n) = int_rep_nonneg (pred n)"
  unfolding int_rep_pred_def by simp

lemma int_rep_pred_type [type]:
  "int_rep_pred : Element int_rep \<Rightarrow> Element int_rep"
  unfolding int_rep_pred_def nat_one_def
  by (unfold_types, elim mem_int_repE) auto

lemma int_rep_pred_succ_eq [simp]:
  assumes "x \<in> int_rep"
  shows "int_rep_pred (int_rep_succ x) = x"
using assms
proof (cases x rule: mem_int_repE)
  case (neg n)
  then show ?thesis by (cases "n = 1") auto
qed simp

lemma int_rep_succ_pred_eq [simp]:
  assumes "x \<in> int_rep"
  shows "int_rep_succ (int_rep_pred x) = x"
using assms
proof (cases x rule: mem_int_repE)
  case (nonneg n)
  then show ?thesis by (cases "n = 0") (auto simp: int_rep_zero_def[symmetric])
next
  case (neg n)
  then have "succ n \<noteq> 1" unfolding nat_one_def by auto
  with neg show ?thesis by auto
qed

definition "int_rep_inv \<equiv> int_rep_rec
  (\<lambda>n. (if n = 0 then int_rep_nonneg else int_rep_neg) n)
  int_rep_nonneg"

lemma int_rep_inv_zero_eq [simp]: "int_rep_inv int_rep_zero = int_rep_zero"
  unfolding int_rep_inv_def int_rep_zero_def by simp

lemma int_rep_inv_nonneg_eq [simp]:
  "n \<noteq> 0 \<Longrightarrow> int_rep_inv (int_rep_nonneg n) = int_rep_neg n"
  unfolding int_rep_inv_def by simp

lemma int_rep_inv_neg_eq [simp]:
  "int_rep_inv (int_rep_neg n) = int_rep_nonneg n"
  unfolding int_rep_inv_def by simp

lemma int_rep_inv_type [type]: "int_rep_inv : Element int_rep \<Rightarrow> Element int_rep"
  unfolding int_rep_inv_def by (unfold_types, elim mem_int_repE)
  (*TODO: would be nice if this works*)
  (* (insert int_rep_neg_type, auto) *)
  (insert int_rep_neg_type, unfold_types, auto)

lemma int_rep_inv_inv_eq [simp]:
  "x \<in> int_rep \<Longrightarrow> int_rep_inv (int_rep_inv x) = x"
  by (erule mem_int_repE, erule mem_natE) (auto simp: int_rep_zero_def[symmetric])

lemma int_rep_pred_inv_eq_inv_succ:
  assumes "x \<in> int_rep"
  shows "int_rep_pred (int_rep_inv x) = int_rep_inv (int_rep_succ x)"
proof -
  {
    fix n assume "n \<in> \<nat>"
    then have
      "int_rep_nonneg n = int_rep_inv (int_rep_succ (int_rep_neg (succ n)))"
    proof (cases n rule: mem_natE)
      case zero
      then show ?thesis
        by (simp add: nat_one_def[symmetric] int_rep_zero_def[symmetric])
    next
      case (succ n)
      have "succ (succ n) \<noteq> 1" unfolding nat_one_def by auto
      with succ show ?thesis by simp
    qed
  }
  note this[intro!]
  from assms show ?thesis
    by (elim mem_int_repE)
    (auto elim: mem_natE simp: int_rep_zero_def[symmetric] nat_one_def)
qed

corollary int_rep_inv_pred_inv_eq_succ [simp]:
  assumes "x \<in> int_rep"
  shows "int_rep_inv (int_rep_pred (int_rep_inv x)) = int_rep_succ x"
  using int_rep_pred_inv_eq_inv_succ by simp

corollary int_rep_succ_inv_eq_inv_pred:
  assumes "x \<in> int_rep"
  shows "int_rep_succ (int_rep_inv x) = int_rep_inv (int_rep_pred x)"
  using int_rep_inv_pred_inv_eq_succ[of "int_rep_inv x"] by simp

corollary int_rep_inv_succ_inv_eq_pred [simp]:
  assumes "x \<in> int_rep"
  shows "int_rep_inv (int_rep_succ (int_rep_inv x)) = int_rep_pred x"
  using int_rep_succ_inv_eq_inv_pred by simp


end