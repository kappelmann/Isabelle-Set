subsubsection \<open>Addition\<close>
theory TSNat_Add
  imports TSNat_Rec
begin

unbundle no_hotg_add_syntax

definition "nat_add m n \<equiv> nat_rec m n succ"

lemma nat_add_type [type]: "nat_add \<Ztypecolon> Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_add_def by auto

bundle isa_set_nat_add_syntax begin notation nat_add (infixl "+" 65) end
bundle no_isa_set_nat_add_syntax begin no_notation nat_add (infixl "+" 65) end

unbundle no_HOL_groups_syntax
unbundle isa_set_nat_add_syntax

lemma zero_add_eq [simp]: "0 + n = n"
  unfolding nat_add_def by simp

lemma Nat_add_zero_eq [simp]: "n \<Ztypecolon> Nat \<Longrightarrow> n + 0 = n"
  unfolding nat_add_def by (induction n rule: Nat_induct) auto

lemma Nat_add_assoc:
  "\<lbrakk>l \<Ztypecolon> Nat; m \<Ztypecolon> Nat; n \<Ztypecolon> Nat\<rbrakk> \<Longrightarrow> l + m + n = l + (m + n)"
  unfolding nat_add_def by (induction l rule: Nat_induct) auto

lemma Nat_succ_add_eq [simp]: "m \<Ztypecolon> Nat \<Longrightarrow> succ m + n = succ (m + n)"
  unfolding nat_add_def by simp

lemma Nat_add_succ_eq [simp]: "m \<Ztypecolon> Nat \<Longrightarrow> m + succ n = succ (m + n)"
  by (induction m rule: Nat_induct) auto

corollary Nat_succ_add_eq_add_succ: "m \<Ztypecolon> Nat \<Longrightarrow> succ m + n = m + succ n"
  by simp

lemma Nat_add_comm: "m \<Ztypecolon> Nat \<Longrightarrow> n \<Ztypecolon> Nat \<Longrightarrow> m + n = n + m"
  by (induction m rule: Nat_induct) auto

lemma Nat_add_comm_left:
  "\<lbrakk>l \<Ztypecolon> Nat; m \<Ztypecolon> Nat; n \<Ztypecolon> Nat\<rbrakk> \<Longrightarrow> l + (m + n) = m + (l + n)"
  by (induction l rule: Nat_induct) auto

lemmas Nat_add_AC_rules = Nat_add_comm Nat_add_assoc Nat_add_comm_left

lemma Nat_one_add_eq_succ: "1 + n = succ n"
  by (simp add: nat_add_def)

lemma nat_add_one_eq_succ: "n \<Ztypecolon> Nat \<Longrightarrow> n + 1 = succ n"
  by (simp only: Nat_add_comm[of n] Nat_one_add_eq_succ)

lemma Nat_add_ne_zero_if_ne_zero_left:
  assumes "m \<Ztypecolon> Nat"
  and "m \<noteq> 0"
  shows "m + n \<noteq> 0"
  using assms by (cases m rule: NatE) auto

lemma Nat_add_ne_zero_if_ne_zero_right [simp]:
  assumes "m \<Ztypecolon> Nat"
  and "n \<noteq> 0"
  shows "m + n \<noteq> 0"
  using assms by (cases m rule: NatE) auto

lemma Nat_pred_add_eq [simp]:
  "\<lbrakk>m \<Ztypecolon> Nat; n \<Ztypecolon> Nat; m \<noteq> 0\<rbrakk> \<Longrightarrow> pred m + n = pred (m + n)"
  by (cases m rule: NatE) auto

corollary Nat_add_pred_eq [simp]:
  "\<lbrakk>m \<Ztypecolon> Nat; n \<Ztypecolon> Nat; n \<noteq> 0\<rbrakk> \<Longrightarrow> m + pred n = pred (m + n)"
  by (auto simp only: Nat_add_comm[of m] intro: Nat_pred_add_eq)

lemma Nat_succ_add_pred_eq [simp]:
  "\<lbrakk>m \<Ztypecolon> Nat; n \<Ztypecolon> Nat; n \<noteq> 0\<rbrakk> \<Longrightarrow> succ m + pred n = m + n"
  by (cases m rule: NatE) auto

corollary nat_pred_add_succ [simp]:
  "\<lbrakk>m \<Ztypecolon> Nat; n \<Ztypecolon> Nat; m \<noteq> 0\<rbrakk> \<Longrightarrow> pred m + succ n = m + n"
  by (auto simp only: Nat_add_comm[of m] Nat_add_comm[of "pred m"]
    intro: Nat_succ_add_pred_eq)

unbundle no_HOL_order_syntax

lemma Nat_le_add [intro]: "m \<Ztypecolon> Nat \<Longrightarrow> n \<Ztypecolon> Nat \<Longrightarrow> m \<le> m + n"
  by (induction m rule: Nat_induct) auto

lemma Nat_lt_add_if_ne_zero: "\<lbrakk>m \<Ztypecolon> Nat; n \<Ztypecolon> Nat; n \<noteq> 0\<rbrakk> \<Longrightarrow> m < m + n"
  by (induction m rule: Nat_induct) auto

lemma Nat_lt_if_add_lt: "\<lbrakk>l \<Ztypecolon> Nat; m \<Ztypecolon> Nat; n \<Ztypecolon> Nat; l + m < n\<rbrakk> \<Longrightarrow> l < n"
  using lt_if_lt_if_le[OF Nat_le_add[of l m]] by auto

lemma Nat_le_if_add_le: "\<lbrakk>l \<Ztypecolon> Nat; m \<Ztypecolon> Nat; n \<Ztypecolon> Nat; l + m \<le> n\<rbrakk> \<Longrightarrow> l \<le> n"
  using le_trans[OF Nat_le_add[of l m]] by auto

lemma Nat_lt_add_if_lt:
  assumes "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  and "l < m"
  shows "l < m + n"
proof -
  note \<open>l < m\<close>
  moreover have "... \<le> m + n" by auto
  ultimately show "l < m + n" using lt_if_le_if_lt by auto
(*TODO: Transitivity rules have typing assumptions. Proof should more
  look like this:
  note \<open>l < m\<close>
  also have "... \<le> m + n" by auto
  finally show "l < m + n" .
*)
qed

lemma Nat_add_lt_add_if_lt:
  assumes "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  and "l < m"
  shows "l + n < m + n"
using \<open>n \<Ztypecolon> Nat\<close>
proof (induction n rule: Nat_induct)
  (*TODO: should be derivable automatically*)
  from assms have "l \<Ztypecolon> Nat" using Nat_if_lt_Nat by auto
  case zero then show "?case" by simp
  case (succ n)
  have "l + succ n = succ (l + n)" by simp
  moreover with succ.IH have "... < succ (m + n)"
    by (auto intro: Nat_succ_lt_succ_if_lt)
  moreover have "... = m + succ n" by simp
  (*TODO: transitivity proofs are ugly at the moment*)
  ultimately show "?case" by (simp only:)
qed

lemma Nat_lt_if_add_lt_add:
  assumes "l \<Ztypecolon> Nat" "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  shows "l + n < m + n \<Longrightarrow> l < m"
using \<open>n \<Ztypecolon> Nat\<close>
proof (induction n rule: Nat_induct)
  (* case zero then show "?case" by simp *)
  case (succ n)
  have "succ (l + n) = l + succ n" by simp
  moreover have "... < m + succ n" by fact
  moreover have "... = succ (m + n)" by simp
  (*TODO: transitivity proofs are ugly at the moment*)
  ultimately have "succ (l + n) < succ (m + n)" by (simp only:)
  then have "l + n < m + n" by simp
  then show "l < m" by (rule succ.IH)
qed simp

corollary Nat_add_lt_add_iff_lt:
  assumes "l \<Ztypecolon> Nat" "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  shows "l + n < m + n \<longleftrightarrow> l < m"
using assms Nat_lt_if_add_lt_add Nat_add_lt_add_if_lt by blast


end
