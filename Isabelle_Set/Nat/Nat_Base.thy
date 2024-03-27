\<^marker>\<open>creator "Alexander Krauss"\<close>
\<^marker>\<open>creator "Josh Chen"\<close>
\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Basics for natural numbers\<close>
theory Nat_Base
imports
  Transport.HOL_Syntax_Bundles_Groups
  Transport.HOL_Syntax_Bundles_Orders
  Ordinals
begin

text \<open>The basic results have already been shown for \<nat> = \<omega>.\<close>

definition "nat \<equiv> \<omega>"

bundle isa_set_nat_syntax begin notation nat ("\<nat>") end
bundle no_isa_set_nat_syntax begin no_notation nat ("\<nat>") end
unbundle isa_set_nat_syntax

lemmas fixpoint_nat [iff] = fixpoint_omega[folded nat_def]
  and zero_mem_nat [iff] = zero_mem_omega[folded nat_def]
  and succ_mem_nat_if_mem [intro!] = succ_mem_omega_if_mem[folded nat_def]
  and mem_natE = mem_omegaE[folded nat_def, case_names _ zero succ]
  and nat_induct [case_names zero succ, induct set: nat] =
    omega_induct[folded nat_def]

unbundle no_HOL_groups_syntax

context
  notes nat_def[uhint]
begin

subsection \<open>\<nat> as a type\<close>

abbreviation "Nat \<equiv> Element \<nat>"

(*TODO: could be auto-generated*)
lemma Nat_induct [case_names zero succ, induct pred: Nat]:
  assumes "n : Nat"
  and "P 0"
  and "\<And>n. n : Nat \<Longrightarrow> P n \<Longrightarrow> P (succ n)"
  shows "P n"
  using assms by (simp only: mem_iff_Element[symmetric]) (rule nat_induct)

(*TODO: could be auto-generated*)
lemma NatE:
  assumes "n : Nat"
  obtains (zero) "n = 0" | (succ) m where "m : Nat" "n = succ m"
  using assms by (simp only: mem_iff_Element[symmetric]) (rule mem_natE)

lemma Nat_Ord [derive]: "x : Nat \<Longrightarrow> x : Ord"
  by (induction x rule: Nat_induct) simp

lemma Nat_zero_type [type]: "0 : Nat" by unfold_types auto

lemma Nat_succ_type [type]: "succ : Nat \<Rightarrow> Nat" by unfold_types auto

lemma Nat_one_type [type]: "1 : Nat" by discharge_types

lemma Nat_succ_lt_succ_if_lt: "n : Nat \<Longrightarrow> m < n \<Longrightarrow> succ m < succ n"
  sorry

lemma Nat_lt_if_succ_lt_succ: "\<lbrakk>n : Nat; succ m < succ n\<rbrakk> \<Longrightarrow> m < n"
  sorry

corollary Nat_succ_lt_succ_iff_lt [iff]: "n : Nat \<Longrightarrow> succ m < succ n \<longleftrightarrow> m < n"
  using Nat_succ_lt_succ_if_lt Nat_lt_if_succ_lt_succ by blast

lemma Nat_trichotomy:
  assumes "m : Nat" "n : Nat"
  obtains (lt) "m < n" | (eq) "m = n" | (gt) "n < m"
  (*Good example of type derivation helpfulness*)
  by (rule Ord_trichotomy[of m n]) discharge_types

lemma Nat_le_if_succ_le: "n : Nat \<Longrightarrow> succ m \<le> n \<Longrightarrow> m \<le> n"
  sorry

lemma le_if_lt: "m < n \<Longrightarrow> m \<le> n" unfolding le_def by simp

lemma Nat_le_if_not_lt:
  assumes "m : Nat" "n : Nat" "\<not>(m < n)"
  shows "n \<le> m"
  by (rule Nat_trichotomy[of m n]) (auto simp: assms dest: le_if_lt)

lemma Nat_not_lt_if_le:
  assumes "m : Nat" "n : Nat" "m \<le> n"
  shows "\<not>(n < m)"
  using assms lt_if_lt_if_le[of m m n] by auto

corollary Nat_not_lt_iff_le:
  assumes "m : Nat" "n : Nat"
  shows "\<not>(n < m) \<longleftrightarrow> m \<le> n"
  using assms Nat_le_if_not_lt Nat_not_lt_if_le by blast

lemma Nat_succ_le_succ_if_le: "\<lbrakk>n : Nat; m \<le> n\<rbrakk> \<Longrightarrow> succ m \<le> succ n"
  unfolding le_def by auto

lemma Nat_le_if_succ_le_succ: "\<lbrakk>n : Nat; succ m \<le> succ n\<rbrakk> \<Longrightarrow> m \<le> n"
  unfolding le_def by auto

corollary Nat_succ_le_succ_iff_le [iff]: "n : Nat \<Longrightarrow> succ m \<le> succ n \<longleftrightarrow> m \<le> n"
  using Nat_le_if_succ_le_succ Nat_succ_le_succ_if_le by blast

lemma le_if_lt_succ: "m < succ n \<Longrightarrow> m \<le> n"
  sorry

lemma Nat_lt_succ_if_le: "n : Nat \<Longrightarrow> m \<le> n \<Longrightarrow> m < succ n"
  sorry

corollary Nat_lt_succ_iff_le: "n : Nat \<Longrightarrow> m < succ n \<longleftrightarrow> m \<le> n"
  using le_if_lt_succ Nat_lt_succ_if_le by blast

lemma Nat_succ_le_if_lt: "n : Nat \<Longrightarrow> m < n \<Longrightarrow> succ m \<le> n"
  using le_if_lt_succ by auto

lemma Nat_lt_if_succ_le: "n : Nat \<Longrightarrow> succ m \<le> n \<Longrightarrow> m < n"
  using Nat_lt_succ_if_le by auto

corollary Nat_succ_le_iff_lt: "n : Nat \<Longrightarrow> succ m \<le> n \<longleftrightarrow> m < n"
  using Nat_succ_le_if_lt Nat_lt_if_succ_le by blast

(*TODO: the following should be part of the type checker*)
lemma Nat_if_lt_Nat: "n : Nat \<Longrightarrow> m < n \<Longrightarrow> m : Nat"
  (*TODO: would be nice if this works*)
  (* unfolding nat_def lt_def using mem_omega_if_mem_if_mem_omega by auto *)
  (* unfolding nat_def lt_def by unfold_types (fact mem_omega_if_mem_if_mem_omega) *)
  sorry

lemma Nat_if_le_Nat: "n : Nat \<Longrightarrow> m \<le> n \<Longrightarrow> m : Nat"
  unfolding le_def using Nat_if_lt_Nat by auto

lemma Nat_lt_if_lt_succ_if_lt: "n : Nat \<Longrightarrow> l < m \<Longrightarrow> m < succ n \<Longrightarrow> l < n"
  (* using lt_if_le_if_lt[of n l m] by (auto intro: le_if_lt_succ) *)
  sorry

lemma Nat_succ_lt_if_lt_if_lt: "n : Nat \<Longrightarrow> l < m \<Longrightarrow> m < n \<Longrightarrow> succ l < n"
  by (rule lt_if_lt_if_le[of "succ l" m n])
    (auto intro: le_if_lt_succ Nat_if_lt_Nat)


subsection \<open>More induction principles\<close>

lemma Nat_strong_induct [case_names step, induct pred: Nat]:
  assumes "n : Nat"
  and step: "\<And>m. m : Nat \<Longrightarrow> (\<And>l. l : Nat \<Longrightarrow> l < m \<Longrightarrow> P l) \<Longrightarrow> P m"
  shows "P n"
proof -
  {
    fix m assume "m : Nat"
    then have "\<And>l. l : Nat \<Longrightarrow> l < m \<Longrightarrow> P l"
    proof (induction m rule: Nat_induct)
      case (succ m)
      show "P l"
      proof (rule step)
        fix l' assume "l' : Nat" "l' < l"
        then have "l' < m"
          using \<open>l < succ m\<close> Nat_lt_if_lt_succ_if_lt[of m l'] by auto
        then show "P l'" by (intro succ.IH[of l']) auto
      qed fact
    qed auto
  }
  note P_if_lt_Nat = this
  show "P n" by (rule P_if_lt_Nat) auto
qed

lemma Nat_le_induct [case_names le step, induct pred: Nat]:
  assumes "n : Nat"
  and "m \<le> n"
  and step: "\<And>m. m : Nat \<Longrightarrow> m \<le> n \<Longrightarrow> (\<And>l. l : Nat \<Longrightarrow> l < m \<Longrightarrow> P l) \<Longrightarrow> P m"
  shows "P m"
proof (rule Nat_strong_induct[where ?n=m and ?P="\<lambda>m. m \<le> n \<longrightarrow> P m", rule_format])
  fix m assume "m : Nat" "m \<le> n"
    and IH: "\<And>l. l : Nat \<Longrightarrow> l < m \<Longrightarrow> l \<le> n \<Longrightarrow> P l"
  show "P m"
  proof (rule step)
    fix l assume "l : Nat" "l < m"
    moreover with \<open>m \<le> n\<close> have "l \<le> n" by (auto intro!: lt_if_le_if_lt[of n l m] le_if_lt)
    ultimately show "P l" using IH by auto
  qed fact+
qed (auto intro: Nat_if_le_Nat assms)


subsection \<open>Truncated predecessor function\<close>

definition "pred n = (if n = 0 then 0 else (THE m \<in> \<nat>. n = succ m))"

lemma pred_type [type]: "pred : Nat \<Rightarrow> Nat"
  unfolding pred_def by unfold_types (auto intro: bthe_memI elim: mem_natE)

lemma pred_zero_eq [simp]: "pred 0 = 0"
  unfolding pred_def by simp

lemma Nat_pred_succ_eq [simp]: "n : Nat \<Longrightarrow> pred (succ n) = n"
  unfolding pred_def by auto

lemma Nat_succ_pred_eq_if_ne_zero [simp]:
  "n : Nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> succ (pred n) = n"
  unfolding pred_def by (rule NatE) (auto intro!: arg_cong[where ?f="succ"])


subsubsection \<open>\<open>pred\<close> and \<open><\<close>\<close>

lemma Nat_pred_lt_self_if_ne_zero [iff]:
  "n : Nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> pred n < n"
  by (rule NatE) auto

(* lemma Nat_pred_lt_if_lt: "n : Nat \<Longrightarrow> m < n \<Longrightarrow> pred m < n"
  by (rule NatE[of m]) (auto intro: Nat_lt_if_succ_lt Nat_if_lt_Nat) *)

lemma Nat_lt_if_lt_pred: "n : Nat \<Longrightarrow> m < pred n \<Longrightarrow> m < n"
  by (rule NatE[of n]) (auto intro: Nat_if_lt_Nat lt_succ_if_lt)

lemma Nat_pred_lt_pred_if_lt_if_ne_zero:
  assumes "n : Nat"
  and "m \<noteq> 0"
  and "m < n"
  shows "pred m < pred n"
  by (rule NatE[of m]; rule NatE[of n])
    (insert assms, auto intro: Nat_if_lt_Nat)

lemma Nat_lt_if_pred_lt_pred:
  assumes "m : Nat" "n : Nat"
  and "pred m < pred n"
  shows "m < n"
  by (rule NatE[of m]; rule NatE[of n]) (insert assms, auto)

corollary Nat_pred_lt_pred_iff_lt_if_ne_zero [iff]:
  assumes "m : Nat" "n : Nat"
  and "m \<noteq> 0"
  shows "pred m < pred n \<longleftrightarrow> m < n"
  using assms Nat_pred_lt_pred_if_lt_if_ne_zero Nat_lt_if_pred_lt_pred by blast

lemma Nat_lt_pred_if_succ_lt:
  assumes "n : Nat"
  assumes "succ m < n"
  shows "m < pred n"
  by (rule NatE[of n]) (insert assms, auto)

lemma Nat_succ_lt_if_lt_pred:
  assumes "n : Nat"
  and "m < pred n"
  shows "succ m < n"
  by (rule NatE[of n]) (insert assms, auto)

lemma Nat_lt_if_lt_if_pred_lt:
  assumes "l : Nat" "n : Nat"
  and "pred l < m" "m < n"
  shows "l < n"
  by (rule NatE[of l]) (insert assms, auto dest: Nat_succ_lt_if_lt_if_lt lt_trans)

lemma Nat_lt_pred_if_lt_if_lt:
  assumes "n : Nat"
  and "l < m" "m < n"
  shows "l < pred n"
  by (rule NatE[of n]) (insert assms, auto dest: Nat_succ_lt_if_lt_if_lt)


subsubsection \<open>\<open>pred\<close> and \<open>\<le>\<close>\<close>

lemma Nat_pred_le_self [iff]: "n : Nat \<Longrightarrow> pred n \<le> n"
  by (rule NatE) (auto intro: le_succ_if_le)

lemma Nat_pred_le_if_le: "n : Nat \<Longrightarrow> m \<le> n \<Longrightarrow> pred m \<le> n"
  by (rule NatE[of m]) (auto intro: Nat_if_le_Nat Nat_le_if_succ_le)

lemma Nat_le_if_le_pred: "n : Nat \<Longrightarrow> m \<le> pred n \<Longrightarrow> m \<le> n"
  by (rule NatE[of n]) (auto intro: le_succ_if_le)

lemma Nat_pred_le_pred_if_le:
  assumes "n : Nat"
  and "m \<le> n"
  shows "pred m \<le> pred n"
  by (rule NatE[of m]; rule NatE[of n]) (insert assms, auto intro: Nat_if_le_Nat)

lemma Nat_le_if_pred_le_pred_if_ne_zero:
  assumes "m : Nat" "n : Nat"
  and "n \<noteq> 0"
  and "pred m \<le> pred n"
  shows "m \<le> n"
  by (rule NatE[of m]; rule NatE[of n]) (insert assms, auto)

corollary Nat_pred_le_pred_iff_le_if_ne_zero [iff]:
  assumes "m : Nat" "n : Nat"
  and "n \<noteq> 0"
  shows "pred m \<le> pred n \<longleftrightarrow> m \<le> n"
  using assms Nat_pred_le_pred_if_le Nat_le_if_pred_le_pred_if_ne_zero by blast

lemma Nat_le_pred_if_succ_le:
  assumes "n : Nat"
  assumes "succ m \<le> n"
  shows "m \<le> pred n"
  by (rule NatE[of n]) (insert assms, auto)

lemma Nat_succ_le_if_le_pred_if_ne_zero:
  assumes "n : Nat"
  and "n \<noteq> 0"
  and "m \<le> pred n"
  shows "succ m \<le> n"
  by (rule NatE[of n]) (insert assms, auto)


subsubsection \<open>\<open>pred\<close> and \<open><\<close> and \<open>\<le>\<close>\<close>

lemma Nat_le_if_pred_lt: "n : Nat \<Longrightarrow> m : Nat \<Longrightarrow> pred m < n \<Longrightarrow> m \<le> n"
  by (rule NatE[of m]) (auto dest: Nat_succ_le_if_lt)

lemma Nat_pred_lt_if_le_if_ne_zero: "n : Nat \<Longrightarrow> m \<noteq> 0 \<Longrightarrow> m \<le> n \<Longrightarrow> pred m < n"
  by (rule NatE[of m]) (auto intro: Nat_if_le_Nat Nat_lt_if_succ_le)

corollary Nat_pred_lt_iff_le_if_ne_zero:
  assumes "n : Nat" "m : Nat"
  and "m \<noteq> 0"
  shows "pred m < n \<longleftrightarrow> m \<le> n"
  using assms Nat_le_if_pred_lt Nat_pred_lt_if_le_if_ne_zero by blast

lemma Nat_le_pred_if_lt: "n : Nat \<Longrightarrow> m < n \<Longrightarrow> m \<le> pred n"
  by (rule NatE[of n]) (auto dest: le_if_lt_succ)

lemma Nat_lt_if_le_pred_if_ne_zero: "n : Nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> m \<le> pred n \<Longrightarrow> m < n"
  by (rule NatE[of n]) (auto dest: Nat_lt_if_succ_le)

corollary Nat_le_pred_iff_lt_if_ne_zero:
  "n : Nat \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> m \<le> pred n \<longleftrightarrow> m < n"
  using Nat_lt_if_le_pred_if_ne_zero Nat_le_pred_if_lt by blast

lemma Nat_pred_eq_zero_iff: "n : Nat \<Longrightarrow> pred n = 0 \<longleftrightarrow> n = 0 \<or> n = 1"
proof
  fix n assume "n : Nat" "pred n = 0"
  then show "n = 0 \<or> n = succ 0"
  proof (cases n rule: NatE)
    case (succ m)
    then have "m = pred n" by simp
    also have "... = 0" by fact
    finally have "m = 0" .
    with \<open>n = succ m\<close> show "n = 0 \<or> n = succ 0" by simp
  qed auto
qed auto

end

end
