\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Subtraction (truncated)\<close>
theory TSNat_Sub
  imports TSNat_Add
begin

definition "nat_sub m n \<equiv> nat_rec n m pred"

lemma nat_sub_type [type]: "nat_sub \<Ztypecolon> Nat \<Rightarrow> Nat \<Rightarrow> Nat"
  unfolding nat_sub_def by discharge_types

open_bundle isa_set_nat_sub_syntax begin notation nat_sub (infixl "-" 65) end

lemma nat_sub_zero_eq [simp]: "m - 0 = m"
  unfolding nat_sub_def by simp

lemma Nat_sub_succ_eq [simp]: "n \<Ztypecolon> Nat \<Longrightarrow> m - succ n = pred (m - n)"
  unfolding nat_sub_def by simp

lemma Nat_pred_sub_eq [simp]: "m \<Ztypecolon> Nat \<Longrightarrow> pred n - m = pred (n - m)"
  by (induction m rule: Nat_induct) auto

lemma Nat_sub_eq_zero_if_le: "n \<Ztypecolon> Nat \<Longrightarrow> m \<le> n \<Longrightarrow> m - n = 0"
proof (induction n arbitrary: m rule: Nat_induct)
  case (succ n)
  then show ?case
  proof (cases "m = 0")
    case True
    then have "m \<le> n" by simp
    with succ.IH have "0 = m - n" by simp
    then have "0 = pred (m - n)" by simp
    also have "... = m - succ n" by simp
    finally show "m - succ n = 0" by simp
  next
    case False
    then have "pred m < succ n" using Nat_pred_lt_if_le_if_ne_zero by auto
    then have "pred m \<le> n" using le_if_lt_succ by auto
    with succ.IH have "0 = pred m - n" by simp
    also have "... = m - succ n" by simp
    finally show "m - succ n = 0" by simp
  qed
qed simp

lemma Nat_zero_sub_eq [simp]: "m \<Ztypecolon> Nat \<Longrightarrow> 0 - m = 0"
  by (rule Nat_sub_eq_zero_if_le) auto

lemma Nat_sub_self_eq [simp]: "m \<Ztypecolon> Nat \<Longrightarrow> m - m = 0"
  by (rule Nat_sub_eq_zero_if_le) auto

lemma Nat_succ_sub_succ_eq [simp]:
  "m \<Ztypecolon> Nat \<Longrightarrow> n \<Ztypecolon> Nat \<Longrightarrow> succ m - succ n = m - n"
  unfolding nat_sub_def by (rule Nat_induct[of n]) auto

lemma Nat_sub_lt_sub_if_le_if_lt:
  assumes "m \<Ztypecolon> Nat"
  and "l < m"
  and "n \<le> l"
  shows "l - n < m - n"
proof -
  from assms have "n \<Ztypecolon> Nat" "l \<Ztypecolon> Nat"
    by (auto intro: Nat_if_lt_Nat Nat_if_le_Nat)
  then show ?thesis using assms
  proof (induction n arbitrary: l m rule: Nat_induct)
    case (succ n)
    have "l - n \<noteq> 0"
    proof -
      from succ.prems have "n < l" using Nat_lt_if_succ_le by auto
      then have "n - n < l - n" by (subst succ.IH) auto
      then show ?thesis by simp
    qed
    moreover have "l - n < m - n"
    proof (rule succ.IH)
      from succ.prems show "n \<le> l" by (auto intro: Nat_le_if_succ_le)
    qed discharge_types
    ultimately have "pred (l - n) < pred (m - n)"
      by (auto intro!: Nat_pred_lt_pred_if_lt_if_ne_zero)
    then show ?case by simp
  qed simp
qed

corollary Nat_zero_lt_sub_if_lt:
  assumes "n \<Ztypecolon> Nat"
  and "m < n"
  shows "0 < n - m"
  using assms Nat_sub_lt_sub_if_le_if_lt[OF assms le_self]
    by (auto dest: Nat_if_lt_Nat)

lemma Nat_lt_if_sub_lt_sub:
  assumes "l \<Ztypecolon> Nat" "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  and "l - n < m - n"
  shows "l < m"
using \<open>n \<Ztypecolon> Nat\<close> assms
proof (induction n arbitrary: l m rule: Nat_induct)
  case (succ n)
  then have "pred l - n < pred m - n" by simp
  with succ.IH have "pred l < pred m" by simp
  with Nat_lt_if_pred_lt_pred show ?case by simp
qed simp

corollary Nat_lt_if_zero_lt_sub:
  assumes "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  and "0 < m - n"
  shows "n < m"
proof -
  from \<open>0 < m - n\<close> have "n - n < m - n" by simp
  then show ?thesis by (intro Nat_lt_if_sub_lt_sub[of n m n]) discharge_types
qed

corollary Nat_zero_lt_sub_iff_lt:
  "\<lbrakk>m \<Ztypecolon> Nat; n \<Ztypecolon> Nat\<rbrakk> \<Longrightarrow> 0 < n - m \<longleftrightarrow> m < n"
  using Nat_zero_lt_sub_if_lt Nat_lt_if_sub_lt_sub[of m n m] by auto

lemma Nat_succ_sub_eq_if_le:
  assumes "m \<Ztypecolon> Nat"
  and "n \<le> m"
  shows "succ m - n = succ (m - n)"
proof (cases n rule: NatE)
  fix n' assume "n' \<Ztypecolon> Nat" and [simp]: "n = succ n'"
  have "succ m - n = m - n'" by (simp del: Nat_sub_succ_eq)
  also have "... = succ (pred (m - n'))"
  proof (subst Nat_succ_pred_eq_if_ne_zero)
    from \<open>n \<le> m\<close> have "n' < m" by (auto intro: Nat_lt_if_succ_le)
    then show "m - n' \<noteq> 0"
      using Nat_zero_lt_sub_if_lt ne_if_lt[symmetric] by auto
  qed auto
  also have "... = succ (m - n)" by simp
  finally show "succ m - n = succ (m - n)" .
qed (auto intro: Nat_if_le_Nat[OF assms])

lemma Nat_sub_pred_eq_succ_if_le_if_ne_zero:
  assumes "m \<Ztypecolon> Nat"
  and "n \<noteq> 0"
  and "n \<le> m"
  shows "m - pred n = succ (m - n)"
proof (cases n rule: NatE)
   (*TODO: should be derivable automatically*)
  from assms show "n \<Ztypecolon> Nat" using Nat_if_le_Nat by auto
  fix n' assume "n' \<Ztypecolon> Nat" and [simp]: "n = succ n'"
  then have "m - pred n = m - n'" by simp
  also have "... = succ (pred (m - n'))"
  proof (subst Nat_succ_pred_eq_if_ne_zero)
    from \<open>n \<le> m\<close> have "n' < m" by (auto intro: Nat_lt_if_succ_le)
    then show "m - n' \<noteq> 0"
      using Nat_zero_lt_sub_if_lt ne_if_lt[symmetric] by auto
  qed auto
  also have "...  = succ (m - n)" by simp
  finally show "m - pred n = succ (m - n)" .
qed (insert \<open>n \<noteq> 0\<close>, auto)

lemma Nat_add_sub_assoc:
  assumes "l \<Ztypecolon> Nat" "m \<Ztypecolon> Nat" "n \<le> m"
  shows "l + m - n = l + (m - n)"
proof -
  (*TODO: should be derivable automatically*)
  from assms have "n \<Ztypecolon> Nat" using Nat_if_le_Nat by auto
  then show "?thesis" using assms
  proof (induction n arbitrary: l m rule: Nat_induct)
    case (succ n)
    have "l + m - succ n = pred (l + m - n)" using Nat_sub_succ_eq by simp
    also have "... = pred (l + (m - n))"
      by (subst succ.IH) (auto intro: Nat_le_if_succ_le)
    also have "... = l + pred (m - n)"
    proof (subst Nat_add_pred_eq)
      from \<open>succ n \<le> m\<close> have "n < m" using Nat_lt_if_succ_le by simp
      then have "n - n < m - n" by (intro Nat_sub_lt_sub_if_le_if_lt) auto
      then show "m - n \<noteq> 0" by simp
    qed auto
    also have "... = l + (m - succ n)" using Nat_sub_succ_eq by simp
    finally show ?case .
  qed simp
qed

lemma Nat_sub_add_eq_sub_sub:
  assumes "l \<Ztypecolon> Nat" "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  shows "l - (m + n) = l - m - n"
using \<open>n \<Ztypecolon> Nat\<close> assms
proof (induction n rule: Nat_induct)
  case (succ n)
  have "l - (m + succ n) = pred (l - (m + n))" by simp
  also with succ.IH have "... = pred (l - m - n)" by simp
  also have "... = l - m - succ n" by simp
  finally show ?case .
qed simp

lemma Nat_sub_sub_eq_sub_sub:
  assumes "l \<Ztypecolon> Nat" "m \<Ztypecolon> Nat" "n \<Ztypecolon> Nat"
  shows "l - m - n = l - n - m"
  by (simp only: Nat_sub_add_eq_sub_sub[symmetric] Nat_add_comm)


end