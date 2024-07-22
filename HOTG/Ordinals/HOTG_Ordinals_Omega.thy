\<^marker>\<open>creator "Niklas Krofta"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOTG_Ordinals_Omega
  imports
    HOTG_Transfinite_Recursion
    HOTG_Universes
begin

unbundle
  no_HOL_ascii_syntax
  no_HOL_groups_syntax
  no_HOL_order_syntax

definition omega :: set where
  "omega = least_wrt_rel (\<le>) limit_ordinal"

bundle hotg_omega_syntax begin notation omega ("\<omega>") end
bundle no_hotg_omega_syntax begin no_notation omega ("\<omega>") end
unbundle hotg_omega_syntax

text \<open>This proves the existence of limit ordinals.\<close>

lemma limit_ordinal_collect_univ_ordinal:
  fixes X :: set
  defines "Ord\<^sub>U \<equiv> {\<alpha> \<in> univ X | ordinal \<alpha>}"
  shows "limit_ordinal Ord\<^sub>U"
proof (intro limit_ordinalI)
  have "\<beta> \<in> Ord\<^sub>U" if "\<alpha> \<in> Ord\<^sub>U" "\<beta> \<in> \<alpha>" for \<alpha> \<beta>
    using that ordinal_if_mem_if_ordinal subset_univ_if_mem Ord\<^sub>U_def by blast
  moreover have "\<forall>\<alpha> : Ord\<^sub>U. mem_trans_closed \<alpha>"
    using Ord\<^sub>U_def by (blast elim: ordinal_mem_trans_closedE)
  ultimately show "ordinal Ord\<^sub>U" by (blast intro: ordinal_if_mem_trans_closedI)
qed (unfold Ord\<^sub>U_def, auto)

corollary
  limit_ordinal_omega: "limit_ordinal \<omega>"
  and is_least_wrt_le_limit_ordinal_omega: "is_least_wrt_rel (\<le>) limit_ordinal \<omega>"
proof -
  show "is_least_wrt_rel (\<le>) limit_ordinal \<omega>"
    using is_least_wrt_rel_least_wrt_rel_if_le_ordinal_if_pred limit_ordinal_collect_univ_ordinal
    unfolding omega_def by (auto elim: limit_ordinalE)
  then show "limit_ordinal \<omega>" by auto
qed

lemma
  ordinal_omega: "ordinal \<omega>" and
  zero_mem_omega [iff]: "0 \<in> \<omega>" and
  succ_mem_omega_if_mem [intro!]: "n \<in> \<omega> \<Longrightarrow> succ n \<in> \<omega>"
  using limit_ordinal_omega by (auto elim: limit_ordinalE)

lemma one_mem_omega [iff]: "1 \<in> \<omega>" by auto
lemma two_mem_omega [iff]: "2 \<in> \<omega>" by auto

lemma ordinal_if_mem_omega:
  assumes "n \<in> \<omega>"
  shows "ordinal n"
  using assms ordinal_omega ordinal_if_mem_if_ordinal by blast

lemma not_limit_ordinal_if_mem_omega:
  assumes "n \<in> \<omega>"
  shows "\<not>(limit_ordinal n)"
  using is_least_wrt_le_limit_ordinal_omega assms lt_if_mem by fastforce

lemma mem_omegaE:
  assumes "n \<in> \<omega>"
  obtains (zero) "n = 0" | (succ) m where "m \<in> \<omega>" "n = succ m"
proof -
  have "ordinal n" using assms ordinal_omega ordinal_if_mem_if_ordinal by blast
  then show ?thesis
  proof (cases rule: ordinal_cases)
    case (succ m)
    then have "m \<in> n" using succ_eq_insert_self by auto
    then have "m \<in> \<omega>" using assms ordinal_omega by (auto elim: ordinal_mem_trans_closedE)
    then show ?thesis using that \<open>succ m = n\<close> by blast
  qed (auto simp: assms not_limit_ordinal_if_mem_omega that)
qed

lemma omega_induct [case_names zero succ, induct set: omega]:
  assumes "n \<in> \<omega>"
  and "P 0"
  and P_succ: "\<And>m. \<lbrakk>m \<in> \<omega>; P m\<rbrakk> \<Longrightarrow> P (succ m)"
  shows "P n"
proof -
  have "n \<in> \<omega> \<Longrightarrow> P n" if "ordinal n" for n
    using \<open>ordinal n\<close>
  proof (induction rule: ordinal_induct)
    case (succ m)
    have "m \<in> \<omega>" using \<open>succ m \<in> \<omega>\<close> succ_eq_insert_self ordinal_omega
      by (auto elim: ordinal_mem_trans_closedE)
    then show ?case using \<open>m \<in> \<omega> \<Longrightarrow> P m\<close> P_succ by blast
  qed (auto simp: \<open>P 0\<close> not_limit_ordinal_if_mem_omega)
  moreover have "ordinal n" using \<open>n \<in> \<omega>\<close> ordinal_omega ordinal_if_mem_if_ordinal by blast
  ultimately show ?thesis using \<open>n \<in> \<omega>\<close> by blast
qed

lemma eq_zero_or_zero_mem_if_mem_omegaE:
  assumes "n \<in> \<omega>"
  obtains (eq_zero) "n = 0" | (zero_mem) "0 \<in> n"
  using assms
proof (cases rule: mem_omegaE)
  case (succ m)
  then have "ordinal n" "n \<noteq> 0" using ordinal_if_mem_omega succ_ne_zero by auto
  then show ?thesis using that
    by (auto elim!: ordinal_mem_trans_closedE intro!: empty_mem_if_mem_trans_closedI)
qed (auto simp: that)

lemma lt_iff_mem_if_mem_omega:
  assumes "n \<in> \<omega>"
  shows "m < n \<longleftrightarrow> m \<in> n"
  using assms ordinal_if_mem_omega lt_iff_mem_if_ordinal by blast

lemma mem_trans_closed_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> mem_trans_closed n"
  using ordinal_if_mem_omega by (auto elim: ordinal_mem_trans_closedE)

lemma zero_mem_succ_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> 0 \<in> succ n"
  by (cases rule: eq_zero_or_zero_mem_if_mem_omegaE) auto

lemma mem_trans_closed_omega [iff]: "mem_trans_closed \<omega>"
  using ordinal_omega by (blast elim: ordinal_mem_trans_closedE)

lemma mem_trans_if_mem_omega: "\<lbrakk>n \<in> \<omega>; k \<in> m; m \<in> n\<rbrakk> \<Longrightarrow> k \<in> n"
  using ordinal_omega by (auto elim!: ordinal_mem_trans_closedE)

lemma mem_if_succ_mem_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> succ m \<in> n \<Longrightarrow> m \<in> n"
  using mem_trans_if_mem_omega[of n m "succ m"] succ_eq_insert_self by auto

lemma subset_omega_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> n \<subseteq> \<omega>"
  using mem_trans_closed_omega[unfolded mem_trans_closed_def] by blast

lemma mem_omega_if_mem_if_mem_omega: "x \<in> \<omega> \<Longrightarrow> y \<in> x \<Longrightarrow> y \<in> \<omega>"
  using subset_omega_if_mem_omega by auto

lemma succ_mem_succ_if_mem_if_mem_omega: "\<lbrakk>n \<in> \<omega>; m \<in> n\<rbrakk> \<Longrightarrow> succ m \<in> succ n"
  by (induction n rule: omega_induct) (use succ_eq_insert_self in auto)

lemma mem_if_succ_mem_succ_if_mem_omega:
  assumes "n \<in> \<omega>" and succ_m_mem: "succ m \<in> succ n"
  shows "m \<in> n"
proof -
  have "mem_trans_closed (succ n)" by (rule mem_trans_closed_if_mem_omega) (auto intro: \<open>n \<in> \<omega>\<close>)
  from mem_trans_closedD[OF this] succ_m_mem have "succ m \<subseteq> succ n" by auto
  then have "m \<in> (n \<union> {n})" using succ_eq_insert_self by auto
  with succ_m_mem show "m \<in> n" by auto
qed

lemma succ_mem_succ_iff_mem_if_mem_omega [iff]:
  "n \<in> \<omega> \<Longrightarrow> succ m \<in> succ n \<longleftrightarrow> m \<in> n"
  using succ_mem_succ_if_mem_if_mem_omega mem_if_succ_mem_succ_if_mem_omega
  by blast

lemma pred_mem_omega_if_mem_omega: "n \<in> \<omega> \<Longrightarrow> pred n \<in> \<omega>"
  by (cases rule: mem_omegaE) auto

lemma succ_pred_eq_self_if_ne_zero_if_mem_omega:
  assumes "n \<in> \<omega>" "n \<noteq> 0"
  shows "succ (pred n) = n"
proof -
  from assms obtain m where "m \<in> \<omega>" "n = succ m" using mem_omegaE by auto
  then have "pred n = m" using pred_succ_eq_self by auto
  then show ?thesis using \<open>n = succ m\<close> by auto
qed

lemma pred_mem_if_ne_zero_if_mem_omega:
  assumes "n \<in> \<omega>" "n \<noteq> 0"
  shows "pred n \<in> n"
  using succ_pred_eq_self_if_ne_zero_if_mem_omega assms mem_succ by auto

definition omega_rec :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> set \<Rightarrow> 'a" where
  "omega_rec a r = transfrec (\<lambda>f n. if n = 0 then a else r (f (pred n)))"

lemma
  omega_rec_zero [simp]: "omega_rec a r 0 = a" and
  omega_rec_succ: "n \<in> \<omega> \<Longrightarrow> omega_rec a r (succ n) = r (omega_rec a r n)"
proof -
  let ?f = "omega_rec a r"
  let ?step = "\<lambda>f n. if n = 0 then a else r (f (pred n))"
  have f_eq: "?f n = (if n = 0 then a else r (?f (pred n)))" if "n \<in> \<omega>" for n
    using transfrec_eq[of ?step n] unfolding omega_rec_def[symmetric]
    using pred_mem_if_ne_zero_if_mem_omega that by auto
  then show "?f 0 = a" by auto
  assume "n \<in> \<omega>"
  then show "?f (succ n) = r (?f n)"
    using f_eq succ_ne_zero succ_mem_omega_if_mem pred_succ_eq_self by auto
qed

end