section \<open>Set Difference\<close>

theory Set_Difference
imports Union_Intersection
begin

definition diff :: \<open>[set, set] \<Rightarrow> set\<close>  (infixl "\<setminus>" 65)
  where "A \<setminus> B \<equiv> {x \<in> A | x \<notin> B}"

lemma diff_iff [simp]: "c \<in> A \<setminus> B \<longleftrightarrow> (c \<in> A \<and> c \<notin> B)"
  unfolding diff_def by auto

lemma diffI [intro!]: "\<lbrakk>a \<in> A; a \<notin> B\<rbrakk> \<Longrightarrow> a \<in> A \<setminus> B"
  by simp

lemma diffD1: "a \<in> A \<setminus> B \<Longrightarrow> a \<in> A"
  by simp

lemma diffD2: "a \<in> A \<setminus> B \<Longrightarrow> a \<notin> B"
  by simp

lemma diffE [elim!]: "\<lbrakk>a \<in> A \<setminus> B; \<lbrakk>a \<in> A; a \<notin> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma diff_subset [simp, intro]: "A \<setminus> B \<subseteq> A"
  by blast

lemma diff_contains: "C \<subseteq> A \<Longrightarrow> C \<inter> B = {} \<Longrightarrow> C \<subseteq> A \<setminus> B"
  by blast

lemma diff_cancel [simp]: "A \<setminus> A = {}"
  by blast

lemma diff_triv: "A \<inter> B = {} \<Longrightarrow> A \<setminus> B = A"
  by (rule extensionality) auto

lemma empty_diff [simp]: "{} \<setminus> A = {}"
  by blast

lemma diff_empty [simp]: "A \<setminus> {} = A"
  by (rule extensionality) auto

lemma diff_eq_empty_iff: "A \<setminus> B = {} \<longleftrightarrow> A \<subseteq> B"
  by auto

lemma diff_disjoint: "A \<inter> (B \<setminus> A) = {}"
  by blast

lemma diff_partition: "A \<subseteq> B \<Longrightarrow> A \<union> (B \<setminus> A) = B"
  by (rule extensionality) auto

lemma diff_partition': "A \<union> (B \<setminus> A) = A \<union> B"
  by (rule extensionality) auto

lemma subset_bin_union_diff: "A \<subseteq> B \<union> (A \<setminus> B)"
  by blast

lemma double_complement: "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> B \<setminus> (C \<setminus> A) = A"
  by (rule extensionality) auto

lemma double_complement_bin_union: "(A \<union> B) \<setminus> (B \<setminus> A) = A"
  by (rule extensionality) auto

lemma bin_union_bin_inter_dist3:
 "(A \<inter> B) \<union> (B \<inter> C) \<union> (C \<inter> A) = (A \<union> B) \<inter> (B \<union> C) \<inter> (C \<union> A)"
  by (rule extensionality) auto

lemma diff_bin_union: "A \<setminus> (B \<union> C) = (A \<setminus> B) \<inter> (A \<setminus> C)"
  by (rule extensionality) auto

lemma diff_bin_inter: "A \<setminus> (B \<inter> C) = (A \<setminus> B) \<union> (A \<setminus> C)"
  by (rule extensionality) auto

lemma bin_union_diff: "(A \<union> B) \<setminus> C = (A \<setminus> C) \<union> (B \<setminus> C)"
  by (rule extensionality) auto
  
lemma bin_union_diff_eq_diff_right: "(A \<union> B) \<setminus> B = A \<setminus> B"
  using bin_union_diff by auto
  
lemma bin_union_diff_eq_diff_left: "(B \<union> A) \<setminus> B = A \<setminus> B"
  using bin_union_diff by auto

lemma bin_inter_diff: "(A \<inter> B) \<setminus> C = A \<inter> (B \<setminus> C)"
  by (rule extensionality) auto

lemma bin_inter_diff_eq: "C \<subseteq> A \<Longrightarrow> ((A \<setminus> B) \<inter> C) = (C \<setminus> B)"
  by (rule extensionality) auto

lemma diff_bin_inter_distrib: "C \<inter> (A \<setminus> B) = (C \<inter> A) \<setminus> (C \<inter> B)"
  by (rule extensionality) auto

lemma diff_bin_inter_distrib2: "(A \<setminus> B) \<inter> C = (A \<inter> C) \<setminus> (B \<inter> C)"
  by (rule extensionality) auto

lemma diff_idxunion: "I \<noteq> {} \<Longrightarrow> B \<setminus> (\<Union>i\<in> I. A i) = (\<Inter>i\<in> I. B \<setminus> A i)"
  by (rule extensionality) auto

lemma diff_idxinter: "I \<noteq> {} \<Longrightarrow> B \<setminus> (\<Inter>i\<in> I. A i) = (\<Union>i\<in> I. B \<setminus> A i)"
  by (rule extensionality) auto

lemma collect_diff: "collect (A \<setminus> B) P = collect A P \<setminus> collect B P"
  by (rule extensionality) auto


end
