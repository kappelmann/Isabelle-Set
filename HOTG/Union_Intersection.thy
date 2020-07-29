section \<open>Union and Intersection\<close>

theory Union_Intersection
imports Comprehension
begin

(* TODO: This file is kinda messy and should be split or made more cohesive. *)

definition inter :: \<open>set => set\<close> ("\<Inter>_" [90] 90)
  where "\<Inter>A \<equiv> {x \<in> \<Union>A . \<forall>y \<in> A. x \<in> y}"

lemma union_empty [simp]: "\<Union>{} = {}"
  by auto

lemma inter_empty [simp]: "\<Inter>{} = {}"
  unfolding inter_def by auto

lemma union_subset_iff: "\<Union>A \<subseteq> C \<longleftrightarrow> (\<forall>x \<in> A. x \<subseteq> C)"
  by blast

lemma union_upper: "B \<in> A \<Longrightarrow> B \<subseteq> \<Union>A"
  by blast

lemma union_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<subseteq> C) \<Longrightarrow> \<Union>A \<subseteq> C"
  by blast

subsection \<open>Indexed union and intersection:\<close>

syntax
  "_idxunion" :: \<open>[pttrn, set, set] => set\<close> ("(3\<Union>_\<in> _./ _)" [0, 0, 10] 10)
  "_idxinter" :: \<open>[pttrn, set, set] => set\<close> ("(3\<Inter>_\<in> _./ _)" [0, 0, 10] 10)
translations
  "\<Union>x\<in> A. B" \<rightleftharpoons> "\<Union>{B. x \<in> A}"
  "\<Inter>x\<in> A. B" \<rightleftharpoons> "\<Inter>{B. x \<in> A}"

lemma idxunion_iff [iff]: "b \<in> (\<Union>x\<in> A. (B x)) \<longleftrightarrow> (\<exists>x \<in> A. b \<in> B x)"
  by (simp add: bex_def) blast

(*LP: The order of the premises presupposes that A is rigid; b may be flexible*)
lemma idxunionI: "a \<in> A \<Longrightarrow>  b \<in> B a \<Longrightarrow> b \<in> (\<Union>x\<in> A. B x)"
  by (simp, blast)

lemma idxunionE [elim!]: "\<lbrakk>b \<in> (\<Union>x\<in> A. B x); \<And>x. \<lbrakk>x \<in> A; b \<in> B x\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by blast

lemma idxunion_cong:
  "\<lbrakk>A = B; \<And>x. x \<in> B \<Longrightarrow> C x = D x\<rbrakk> \<Longrightarrow> (\<Union>x\<in> A. C x) = (\<Union>x\<in> B. D x)"
  by simp

lemma idxunion_const: "A \<noteq> {} \<Longrightarrow> (\<Union>x\<in> A. B) = B"
  by (rule extensionality) auto

lemma idxunion_empty_family: "(\<Union>x\<in> {}. B) = {}"
  by auto

lemma idxunion_empty_sets: "(\<Union>x\<in> A. {}) = {}"
  by auto

lemma inter_iff [iff]: "A \<in> \<Inter>C \<longleftrightarrow> (\<forall>x \<in> C. A \<in> x) \<and> C \<noteq> {}"
  unfolding inter_def ball_def
  by (auto elim: not_emptyE)

lemma idxunion_subset_iff: "(\<Union>x\<in>A. B x) \<subseteq> C \<longleftrightarrow> (\<forall>x \<in> A. B x \<subseteq> C)"
by blast

lemma idxunion_upper: "x \<in> A \<Longrightarrow> B x \<subseteq> (\<Union>x\<in>A. B x)"
  by blast

lemma idxunion_least: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C) \<Longrightarrow> (\<Union>x\<in>A. B x) \<subseteq> C"
  by blast

lemma union_as_idxunion: "\<Union>A = (\<Union>x\<in> A. x)"
  by auto

lemma union_empty_iff [simp]: "\<Union>A = {} \<longleftrightarrow> A = {} \<or> A = {{}}"
proof
  assume "\<Union>A = {}" show "A = {} \<or> A = {{}}"
  proof (rule disjCI2)
    assume "A \<noteq> {}" then obtain x where "x \<in> A" by auto
    from \<open>\<Union>A = {}\<close> have [simp]: "\<And>x. x \<in> A \<Longrightarrow> x = {}" by auto
    with \<open>x \<in> A\<close> have "x = {}" by simp
    with \<open>x \<in> A\<close> have [simp]: "{} \<in> A" by simp
    show "A = {{}}" by (rule equalityI) auto
  qed
qed auto

lemma inter_as_idxinter: "\<Inter>A = (\<Inter>x \<in> A. x)"
  by auto

lemma inter_subset_iff: "A \<noteq> {} \<Longrightarrow> C \<subseteq> \<Inter>A \<longleftrightarrow> (\<forall>x \<in> A. C \<subseteq> x)"
  by blast

lemma inter_lower: "B \<in> A \<Longrightarrow> \<Inter>A \<subseteq> B"
  by blast

lemma inter_greatest: "\<lbrakk>A \<noteq> {}; \<And>x. x \<in> A \<Longrightarrow> C \<subseteq> x\<rbrakk> \<Longrightarrow> C \<subseteq> \<Inter>A"
  by blast

lemma idxinter_lower: "x \<in> A \<Longrightarrow> (\<Inter>x \<in> A. B x) \<subseteq> B x"
  by blast

lemma idxinter_greatest: "\<lbrakk>A \<noteq> {}; \<And>x. x \<in> A \<Longrightarrow> C \<subseteq> B x\<rbrakk> \<Longrightarrow> C \<subseteq> (\<Inter>x \<in> A. B x)"
  by auto

lemma union_singleton: "\<Union>{b} = b"
  by (rule extensionality) auto

lemma inter_singleton: "\<Inter>{b} = b"
  by (rule extensionality) auto

lemma idxunion_empty [simp]: "(\<Union>i \<in> {}. A i) = {}"
  by blast

lemma idxunion_singleton: "(\<Union>x\<in>A. {x}) = A"
  by (rule extensionality) auto

lemma flatten_idxunion [simp]:
  "(\<Union>x\<in> (\<Union>y \<in> A. B y). C x) = (\<Union>y \<in> A. \<Union>x\<in> B y. C x)"
  by (rule extensionality) auto

lemma idxunion_constant [simp]:
  "(\<Union>y \<in> A. c) = (if A = {} then {} else c)"
  by (rule extensionality) auto

lemma idxinter_constant [simp]:
  "(\<Inter>y \<in> A. c) = (if A = {} then {} else c)"
  by (rule extensionality) auto

lemma idxunion_repl [simp]:
  "(\<Union>y \<in> repl A f. B y) = (\<Union>x\<in> A. B (f x))"
  by auto

lemma idxinter_repl [simp]:
  "(\<Inter>x \<in> repl A f. B x) = (\<Inter>a \<in> A. B(f a))"
  by (auto simp add: inter_def)

lemma idxinter_union_eq:
  "{} \<notin> A \<Longrightarrow> (\<Inter>x \<in> \<Union>A. B x) = (\<Inter>y \<in> A. \<Inter>x \<in> y. B x)"
  by (rule equalityI) auto

lemma inter_idxunion_eq:
  assumes "\<forall>x \<in> A. B x \<noteq> {}"
  shows "(\<Inter>z \<in> (\<Union>x\<in>A. B x). C z) = (\<Inter>x \<in> A. \<Inter>z \<in> B x. C z)"
proof (rule equalityI)
  fix x assume "x \<in> (\<Inter>z \<in> (\<Union>x\<in> A. B x). C z)"
  with assms show "x \<in> (\<Inter>x\<in>A. \<Inter>z\<in> B x. C z)" by auto
next
  fix x assume *: "x \<in> (\<Inter>x \<in> A. \<Inter>z \<in> B x. C z)"
  then have "A \<noteq> {}" by auto
  then obtain y where "y \<in> A" by auto
  with assms have "B y \<noteq> {}" by auto
  with \<open>y\<in>A\<close> have "{B x | x \<in> A} \<noteq> {{}}" by (auto dest: equalityD)
  with * show "x \<in> (\<Inter>z \<in> (\<Union>x\<in> A. B x). C z)" by auto
qed

text \<open>Intersection is well-behaved only if the family is non-empty!\<close>

lemma interI [intro!]: "\<lbrakk>\<And>x. x \<in> C \<Longrightarrow> A \<in> x; C \<noteq> {}\<rbrakk> \<Longrightarrow> A \<in> \<Inter>C"
  by auto

(*LP: A "destruct" rule: every B in C contains A as an element, but A \<in> B can
  hold when B \<in> C does not! This rule is analogous to "spec".*)
lemma interD [elim, Pure.elim]: "\<lbrakk>A \<in> \<Inter>C; B \<in> C\<rbrakk> \<Longrightarrow> A \<in> B"
  by auto

(*LP: "Classical" elimination rule - does not require exhibiting "B \<in> C"*)
lemma interE [elim]: "\<lbrakk>A \<in> \<Inter>C; B \<notin> C \<Longrightarrow> R; A \<in> B \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by auto

lemma idxinter_iff: "b \<in> (\<Inter>x \<in> A. B x) \<longleftrightarrow> (\<forall>x \<in> A. b \<in> B x) \<and> A \<noteq> {}"
  by auto
  
lemma idxinterI: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> b \<in> B x; A \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> (\<Inter>x \<in> A. B x)"
  by blast

lemma idxinterE: "\<lbrakk>b \<in> (\<Inter>x \<in> A. B x); a \<in> A\<rbrakk> \<Longrightarrow> b \<in> B a"
  by blast

lemma idxinter_cong:
  "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> C x = D x) \<Longrightarrow> (\<Inter>x \<in> A. C x) = (\<Inter>x \<in> B. D x)"
  by simp


subsection \<open>Binary union and intersection\<close>

definition bin_union :: \<open>[set, set] \<Rightarrow> set\<close> (infixl "\<union>" 70)
  where "A \<union> B = \<Union>{A, B}"

definition bin_inter :: \<open>[set, set] \<Rightarrow> set\<close> (infixl "\<inter>" 70)
  where "A \<inter> B \<equiv> \<Inter>{A, B}"

lemma bin_union_iff [simp]: "x \<in> A \<union> B \<longleftrightarrow> x \<in> A \<or> x \<in> B"
  unfolding bin_union_def by auto

lemma bin_inter_iff [simp]: "x \<in> A \<inter> B \<longleftrightarrow> x \<in> A \<and> x \<in> B"
  unfolding bin_inter_def by auto

lemma bin_unionI1 [elim?]: "c \<in> A \<Longrightarrow> c \<in> A \<union> B"
  by simp

lemma bin_unionI2 [elim?]: "c \<in> B \<Longrightarrow> c \<in> A \<union> B"
  by simp

lemma bin_unionE [elim!]: "\<lbrakk>c \<in> A \<union> B; c \<in> A \<Longrightarrow> P; c \<in> B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(*LP: Stronger version of the rule above*)
lemma bin_unionE': "\<lbrakk>c \<in> A \<union> B; c \<in> A \<Longrightarrow> P; \<lbrakk>c \<in> B; c \<notin> A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

(*LP: Classical introduction rule: no commitment to A vs B*)
lemma bin_unionCI [intro!]: "(c \<notin> B \<Longrightarrow> c \<in> A) \<Longrightarrow> c \<in> A \<union> B"
  by auto

lemma bin_union_commute: "A \<union> B = B \<union> A"
  by (rule extensionality) auto

lemma bin_union_left_commute: "A \<union> (B \<union> C) = B \<union> (A \<union> C)"
  by (rule extensionality) auto

lemma empty_bin_union_eq [simp]: "{} \<union> A = A"
  by (rule extensionality) auto

lemma bin_union_empty_eq [simp]: "A \<union> {} = A"
  by (rule extensionality) auto

lemma bin_union_singleton_absorb [simp]: "a \<in> A \<Longrightarrow> {a} \<union> A = A"
  by (rule equalityI) auto

lemma singleton_bin_union_eq_cons: "{x} \<union> A = cons x A"
  by (rule extensionality) auto

lemma bin_union_singleton_eq_cons': "A \<union> {x} = cons x A"
  using singleton_bin_union_eq_cons by (subst bin_union_commute)
  
lemma mem_bin_union_singleton_left: "a \<in> {a} \<union> B" by auto

lemma mem_bin_union_singleton_right: "b \<in> A \<union> {b}" by auto

lemma bin_union_subset_iff: "A \<union> B \<subseteq> C \<longleftrightarrow> A \<subseteq> C \<and> B \<subseteq> C"
  by blast

lemma bin_union_upper1: "A \<subseteq> A \<union> B"
  by blast

lemma bin_union_upper2: "B \<subseteq> A \<union> B"
  by blast

lemma bin_union_least: "\<lbrakk>A \<subseteq> C; B \<subseteq> C\<rbrakk> \<Longrightarrow> A \<union> B \<subseteq> C"
  by blast

lemma bin_union_absorb [simp]: "A \<union> A = A"
  by (rule extensionality) auto

lemma bin_union_left_absorb: "A \<union> (A \<union> B) = A \<union> B"
  by (rule extensionality) auto

lemma bin_union_assoc: "(A \<union> B) \<union> C  =  A \<union> (B \<union> C)"
  by (rule extensionality) auto

(*Binary union is an AC-operator*)
lemmas bin_union_ac =
  bin_union_assoc bin_union_left_absorb bin_union_commute bin_union_left_commute

lemma bin_union_subset_absorb1: "A \<subseteq> B \<Longrightarrow> A \<union> B = B"
  by (rule extensionality) auto

lemma bin_union_subset_absorb2: "B \<subseteq> A \<Longrightarrow> A \<union> B = A"
  by (rule extensionality) auto
  
lemma bin_union_mono_right: "B \<subseteq> C \<Longrightarrow> A \<union> B \<subseteq> A \<union> C" by auto

lemma bin_union_mono_left: "A \<subseteq> B \<Longrightarrow> A \<union> C \<subseteq> B \<union> C" by auto

lemma bin_union_bin_inter_distrib: "(A \<inter> B) \<union> C  =  (A \<union> C) \<inter> (B \<union> C)"
  by (rule extensionality) auto

lemma subset_bin_union_iff: "A \<subseteq> B \<longleftrightarrow> A \<union> B = B"
  by (auto intro: equalityI' dest: equalityD)

lemma subset_bin_union_iff2: "A \<subseteq> B \<longleftrightarrow> B \<union> A = B"
  by (auto intro: equalityI' dest: equalityD)

lemma bin_union_empty [iff]: "(A \<union> B = {}) \<longleftrightarrow> (A = {} \<and> B = {})"
  by blast

lemma bin_interI [intro!]: "\<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> c \<in> A \<inter> B"
  by simp

lemma bin_interD1: "c \<in> A \<inter> B \<Longrightarrow> c \<in> A"
  by simp

lemma bin_interD2: "c \<in> A \<inter> B \<Longrightarrow> c \<in> B"
  by simp

lemma bin_interE [elim!]: "\<lbrakk>c \<in> A \<inter> B; \<lbrakk>c \<in> A; c \<in> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma bin_inter_empty_iff [iff]: "(\<forall>a \<in> A. a \<notin> B) \<longleftrightarrow> A \<inter> B = {}"
  by auto

lemma bin_inter_commute: "A \<inter> B = B \<inter> A"
  by (rule extensionality) auto
  
lemma empty_bin_inter_eq_empty [simp]: "{} \<inter> B = {}"
  by auto

lemma bin_inter_empty_eq_empty [simp]: "A \<inter> {} = {}"
  by auto

lemma bin_inter_subset_iff [simp]: "C \<subseteq> A \<inter> B \<longleftrightarrow> C \<subseteq> A \<and> C \<subseteq> B"
  by blast

lemma bin_inter_lower1: "A \<inter> B \<subseteq> A"
  by blast

lemma bin_inter_lower2: "A \<inter> B \<subseteq> B"
  by blast

lemma bin_inter_greatest: "\<lbrakk>C \<subseteq> A; C \<subseteq> B\<rbrakk> \<Longrightarrow> C \<subseteq> A \<inter> B"
  by blast

lemma bin_inter_absorb [simp]: "A \<inter> A = A"
  by (rule extensionality) auto

lemma bin_inter_left_absorb [simp]: "A \<inter> (A \<inter> B) = A \<inter> B"
  by (rule extensionality) auto

lemma bin_inter_left_commute: "A \<inter> (B \<inter> C) = B \<inter> (A \<inter> C)"
  by (rule extensionality) auto

lemma bin_inter_assoc: "(A \<inter> B) \<inter> C  =  A \<inter> (B \<inter> C)"
  by (rule extensionality) auto

(*Binary intersection is an AC-operator*)
lemmas bin_inter_ac =
  bin_inter_assoc bin_inter_left_absorb bin_inter_commute bin_inter_left_commute

lemma bin_inter_subset_left_absorb: "B \<subseteq> A \<Longrightarrow> A \<inter> B = B"
  by (rule extensionality) auto

lemma bin_inter_subset_right_absorb: "A \<subseteq> B \<Longrightarrow> A \<inter> B = A"
  by (rule extensionality) auto

lemma bin_inter_bin_union_distrib: "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  by (rule extensionality) auto

lemma bin_inter_bin_union_distrib2: "(B \<union> C) \<inter> A = (B \<inter> A) \<union> (C \<inter> A)"
  by (rule extensionality) auto

lemma subset_bin_inter_iff: "A \<subseteq> B \<longleftrightarrow> A \<inter> B = A"
  by (auto intro: equalityI' dest: equalityD)

lemma subset_bin_inter_iff2: "A \<subseteq> B \<longleftrightarrow> B \<inter> A = A"
  by (auto intro: equalityI' dest: equalityD)

lemma bin_union_bin_inter_assoc_iff:
  "(A \<inter> B) \<union> C = A \<inter> (B \<union> C) \<longleftrightarrow> C \<subseteq> A"
  by (auto intro: equalityI' dest: equalityD)

lemma collect_bin_union:
  "{x \<in> A \<union> B | P x} = {x \<in> A | P x} \<union> {x \<in> B | P x}"
  by (rule extensionality) auto

lemma collect_bin_inter:
  "{x \<in> A \<inter> B | P x} = {x \<in> A | P x} \<inter> {x \<in> B | P x}"
  by (rule extensionality) auto

lemma bin_inter_collect_absorb:
  "A \<inter> {x \<in> A | P x} = {x \<in> A | P x}"
  by (rule extensionality) auto

lemma collect_idxunion_eq [simp]:
  "collect (\<Union>x\<in> A. B x) P = (\<Union>x\<in> A. collect (B x) P)"
  by (rule extensionality) auto

lemma bin_inter_collect_left:
  "{x \<in> A. P x} \<inter> B = {x \<in> A \<inter> B. P x}"
  by (rule extensionality) auto

lemma bin_inter_collect_right:
  "A \<inter> {x \<in> B. P x} = {x \<in> A \<inter> B. P x}"
  by (rule extensionality) auto

lemma collect_conj_eq:
  "{x \<in> A | P(x) \<and> Q(x)} = {x \<in> A | P x} \<inter> {x \<in> A | Q x}" 
  by (rule extensionality) auto

lemma collect_disj_eq:
  "{x \<in> A | P(x) \<or> Q(x)} = {x \<in> A | P x} \<union> {x \<in> A | Q x}"
  by (rule extensionality) auto

lemma union_bin_union_distrib: "\<Union>(A \<union> B) = \<Union>A \<union> \<Union>B"
  by (rule extensionality) auto

lemma union_bin_inter_subset: "\<Union>(A \<inter> B) \<subseteq> \<Union>A \<inter> \<Union>B"
  by blast

lemma union__disjoint_iff:
  "\<Union>C \<inter> A = {} \<longleftrightarrow> (\<forall>B \<in> C. B \<inter> A = {})"
  by (blast elim!: equalityE)
  
lemma subset_idxunion_iff_eq: "A \<subseteq> (\<Union>i \<in> I. B i) \<longleftrightarrow> A = (\<Union>i \<in> I. A \<inter> B i)"
  apply (rule iffI)
  apply (rule extensionality)
  apply (auto dest: equalityD)
  done

lemma union_empty_iff2: "\<Union>A = {} \<longleftrightarrow> (\<forall>B \<in> A. B = {})"
  by blast

lemma bin_inter_union_eq: "\<Union>B \<inter> A = (\<Union>C \<in> B. C \<inter> A)"
  by (rule extensionality) auto

lemma bin_union_inter_subset:
  "\<lbrakk>z \<in> A; z \<in> B\<rbrakk> \<Longrightarrow> \<Inter>A \<union> \<Inter>B \<subseteq> \<Inter>(A \<inter> B)"
  by blast

lemma inter_bin_union_distrib:
  "\<lbrakk>A \<noteq> {}; B \<noteq> {}\<rbrakk> \<Longrightarrow> \<Inter>(A \<union> B) = \<Inter>A \<inter> \<Inter>B"
  by (rule extensionality) auto

lemma idxunion_bin_union:
  "(\<Union>i\<in> A \<union> B. C i) = (\<Union>i\<in> A. C i) \<union> (\<Union>i\<in> B. C i)"
  by (rule extensionality) auto

lemma idxinter_union:
  "(\<Inter>i\<in> I \<union> J. A i) = (
    if I = {} then \<Inter>j\<in> J. A j
    else if J = {} then \<Inter>i\<in> I. A i
    else (\<Inter>i\<in> I. A i) \<inter> (\<Inter>j\<in> J. A j))"
  by (rule extensionality) auto

(*Halmos, Naive Set Theory, page 35*)
lemma bin_inter_idxunion_distrib:
  "B \<inter> (\<Union>i\<in> I. A i) = (\<Union>i\<in> I. B \<inter> A i)"
  by (rule extensionality) auto

lemma bin_union_idxinter_distrib:
  "I \<noteq> {} \<Longrightarrow> B \<union> (\<Inter>i\<in> I. A i) = (\<Inter>i\<in> I. B \<union> A i)"
  by (rule extensionality) auto

lemma bin_inter_idxunion_distrib2:
  "(\<Union>i\<in> I. A i) \<inter> (\<Union>j\<in> J. B j) = (\<Union>i\<in> I. \<Union>j\<in> J. A i \<inter> B j)"
  by (rule extensionality) auto

lemma bin_union_idxinter_distrib2:
  "\<lbrakk>I \<noteq> {}; J \<noteq> {}\<rbrakk> \<Longrightarrow>
    (\<Inter>i\<in> I. A i) \<union> (\<Inter>j\<in> J. B j) = (\<Inter>i\<in> I. \<Inter>j\<in> J. A i \<union> B j)"
  by (rule extensionality) auto

lemma idxunion_bin_union_distrib:
  "(\<Union>i\<in> I. A i \<union> B i) = (\<Union>i\<in> I. A i) \<union> (\<Union>i\<in> I. B i)"
  by (rule extensionality) auto

lemma idxinter_bin_inter_distrib:
  "I \<noteq> {} \<Longrightarrow> (\<Inter>i\<in> I. A i \<inter> B i) = (\<Inter>i\<in> I. A i) \<inter> (\<Inter>i\<in> I. B i)"
  by (rule extensionality) auto

lemma idxunion_bin_inter_subset:
  "(\<Union>z\<in> I \<inter> J. A z) \<subseteq> (\<Union>z\<in> I. A z) \<inter> (\<Union>z\<in> J. A z)"
  by blast


end
