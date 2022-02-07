section \<open>Set Difference\<close>
theory Set_Difference
  imports Union_Intersection
begin

definition "diff A B \<equiv> {x \<in> A | x \<notin> B}"

bundle hotg_diff_syntax begin notation diff (infixl "\<setminus>" 65) end
bundle no_hotg_diff_syntax begin no_notation diff (infixl "\<setminus>" 65) end
unbundle hotg_diff_syntax

lemma mem_diff_iff [iff]: "a \<in> A \<setminus> B \<longleftrightarrow> (a \<in> A \<and> a \<notin> B)"
  unfolding diff_def by auto

lemma mem_if_mem_diff: "a \<in> A \<setminus> B \<Longrightarrow> a \<in> A"
  by simp

lemma not_mem_if_mem_diff: "a \<in> A \<setminus> B \<Longrightarrow> a \<notin> B"
  by simp

lemma diff_subset [simp, intro!]: "A \<setminus> B \<subseteq> A"
  by blast

lemma subset_diff_if_inter_eq_empty_if_subset: "C \<subseteq> A \<Longrightarrow> C \<inter> B = {} \<Longrightarrow> C \<subseteq> A \<setminus> B"
  by blast

lemma diff_self_eq [simp, intro!]: "A \<setminus> A = {}"
  by blast

lemma diff_eq_left_if_inter_eq_empty: "A \<inter> B = {} \<Longrightarrow> A \<setminus> B = A"
  by auto

lemma empty_diff_eq [simp, intro!]: "{} \<setminus> A = {}"
  by blast

lemma diff_empty_eq [simp, intro!]: "A \<setminus> {} = A"
  by (rule subset_antisym) auto

lemma diff_eq_empty_iff_subset: "A \<setminus> B = {} \<longleftrightarrow> A \<subseteq> B"
  unfolding subset_def by auto

lemma inter_diff_eq_empty [simp, intro!]: "A \<inter> (B \<setminus> A) = {}"
  by blast

lemma bin_union_diff_eq [simp, intro!]: "A \<union> (B \<setminus> A) = A \<union> B"
  by (rule subset_antisym) auto

lemma bin_union_diff_eq_if_subset: "A \<subseteq> B \<Longrightarrow> A \<union> (B \<setminus> A) = B"
  by (rule subset_antisym) auto

lemma subset_bin_union_diff: "A \<subseteq> B \<union> (A \<setminus> B)"
  by blast

lemma diff_diff_subset_antisym: "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> B \<setminus> (C \<setminus> A) = A"
  by auto

lemma bin_union_diff_diff_eq [simp, intro!]: "(A \<union> B) \<setminus> (B \<setminus> A) = A"
  by (rule subset_antisym) auto

lemma diff_bin_union_eq_bin_inter_diff: "A \<setminus> (B \<union> C) = (A \<setminus> B) \<inter> (A \<setminus> C)"
  by (rule subset_antisym) auto

lemma diff_bin_inter_eq_bin_union_diff: "A \<setminus> (B \<inter> C) = (A \<setminus> B) \<union> (A \<setminus> C)"
  by (rule subset_antisym) auto

lemma bin_union_diff_eq_bin_union_diff: "(A \<union> B) \<setminus> C = (A \<setminus> C) \<union> (B \<setminus> C)"
  by (rule subset_antisym) auto

lemma bin_union_diff_eq_diff_right [simp, intro!]: "(A \<union> B) \<setminus> B = A \<setminus> B"
  using bin_union_diff_eq_bin_union_diff by auto

lemma bin_union_diff_eq_diff_left [simp, intro!]: "(B \<union> A) \<setminus> B = A \<setminus> B"
  using bin_union_diff_eq_bin_union_diff by auto

lemma bin_inter_diff_eq_bin_inter_diff: "(A \<inter> B) \<setminus> C = A \<inter> (B \<setminus> C)"
  by (rule subset_antisym) auto

lemma diff_bin_inter_eq_diff_if_subset: "C \<subseteq> A \<Longrightarrow> ((A \<setminus> B) \<inter> C) = (C \<setminus> B)"
  by auto

lemma diff_bin_inter_distrib_right: "C \<inter> (A \<setminus> B) = (C \<inter> A) \<setminus> (C \<inter> B)"
  by (rule subset_antisym) auto

lemma diff_bin_inter_distrib_left: "(A \<setminus> B) \<inter> C = (A \<inter> C) \<setminus> (B \<inter> C)"
  by (rule subset_antisym) auto

lemma diff_idx_union_eq_idx_union: "I \<noteq> {} \<Longrightarrow> B \<setminus> (\<Union>i\<in> I. A i) = (\<Inter>i\<in> I. B \<setminus> A i)"
  by (rule subset_antisym) auto

lemma diff_idx_inter_eq_idx_inter: "I \<noteq> {} \<Longrightarrow> B \<setminus> (\<Inter>i\<in> I. A i) = (\<Union>i\<in> I. B \<setminus> A i)"
  by (rule subset_antisym) auto

lemma collect_diff: "{x \<in> (A \<setminus> B) | P x} = {x \<in> A | P x} \<setminus> {x \<in> B | P x}"
  by (rule subset_antisym) auto


end
