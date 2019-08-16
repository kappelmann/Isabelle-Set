section \<open>Ordinals\<close>

theory Ordinal
imports Fixed_Points

begin

definition Ord :: \<open>set type\<close> where
  Ord_typedef: "Ord \<equiv> Type (\<lambda>x. mem_transitive x \<and> (\<forall>y \<in> x. mem_transitive y))"

lemma empty_ordinal [intro!]: "{} : Ord"
  unfolding Ord_typedef mem_transitive_def by squash_types auto

lemma Ord_transitive [elim]: "\<lbrakk>y \<in> x; x : Ord\<rbrakk> \<Longrightarrow> y : Ord"
  unfolding Ord_typedef mem_transitive_def by squash_types blast

lemma Ord_mem_subset: "\<lbrakk>y \<in> x; x : Ord\<rbrakk> \<Longrightarrow> y \<subseteq> x"
  unfolding Ord_typedef mem_transitive_def by squash_types

(* Adapted from a proof by Chad Brown *)
lemma Ord_trichotomy_aux:
  "X : Ord \<Longrightarrow> Y : Ord \<Longrightarrow> X \<notin> Y \<Longrightarrow> Y \<notin> X \<Longrightarrow> X = Y"
proof (induction X Y rule: mem_double_induct)
  fix X Y
  assume ord: "X : Ord" "Y : Ord"
  assume IH1: "\<And>x. x \<in> X \<Longrightarrow> x : Ord \<Longrightarrow> Y : Ord \<Longrightarrow> x \<notin> Y \<Longrightarrow> Y \<notin> x \<Longrightarrow> x = Y"
  assume IH2: "\<And>y. y \<in> Y \<Longrightarrow> X : Ord \<Longrightarrow> y : Ord \<Longrightarrow> X \<notin> y \<Longrightarrow> y \<notin> X \<Longrightarrow> X = y"
  assume *: "X \<notin> Y" "Y \<notin> X"
  show "X = Y"
  proof (rule extensionality)
    show "X \<subseteq> Y"
    proof
      fix x assume "x \<in> X"
      with ord have "x \<subseteq> X" "x : Ord" by (auto elim!: Ord_mem_subset)
      with * ord IH1 \<open>x \<in> X\<close> show "x \<in> Y" by blast
    qed
    show "Y \<subseteq> X"
    proof
      fix y assume "y \<in> Y"
      with ord have "y \<subseteq> Y" "y : Ord" by (auto elim!: Ord_mem_subset)
      with * ord IH2 \<open>y \<in> Y\<close> show "y \<in> X" by blast
    qed
  qed
qed

lemma Ord_trichotomy: "\<lbrakk>X : Ord; Y : Ord\<rbrakk> \<Longrightarrow> X \<in> Y \<or> X = Y \<or> Y \<in> X"
  using Ord_trichotomy_aux by blast

definition mem_well_ordered :: "set \<Rightarrow> bool"
  where "mem_well_ordered x \<equiv> \<forall>y. y \<subseteq> x \<and> y \<noteq> {} \<longrightarrow> (\<exists>!u \<in> y. \<not>(\<exists>v \<in> y. v \<in> u))"

lemma ordinals_well_ordered: "x : Ord \<Longrightarrow> mem_well_ordered x"
  oops

lemma Ord_subset_mem: "\<lbrakk>x \<subseteq> y; x \<noteq> y; x : Ord; y : Ord\<rbrakk> \<Longrightarrow> x \<in> y"
  oops


subsection \<open>The von Neumann ordinals\<close>

definition succ :: "set \<Rightarrow> set"
  where "succ x \<equiv> x \<union> {x}"

lemma succ_Ord: "x : Ord \<Longrightarrow> succ x : Ord"
  unfolding Ord_typedef succ_def mem_transitive_def by squash_types blast

lemma succ_neq [intro]: "x \<noteq> succ x"
unfolding succ_def
proof (rule, elim equalityE)
  assume "x \<union> {x} \<subseteq> x"
  thus False using mem_irrefl by auto
qed

lemma succ_mem: "x \<in> succ x"
  unfolding succ_def by auto

lemma succ_memI: "x \<in> y \<Longrightarrow> x \<in> succ y"
  unfolding succ_def by auto

lemma succ_not_empty: "succ n \<noteq> {}"
  unfolding succ_def by auto

lemma succ_inject: "succ n = succ m \<Longrightarrow> n = m"
proof (rule ccontr)
  assume succ_eq: "succ n = succ m"
  assume neq: "n \<noteq> m"

  have "n \<in> succ n" unfolding succ_def by blast
  with succ_eq have "n \<in> succ m" by simp
  with neq have "n \<in> m" unfolding succ_def by blast

  have "m \<in> succ m" unfolding succ_def by blast
  with succ_eq have "m \<in> succ n" by simp
  with neq have "m \<in> n" unfolding succ_def by blast

  from `n \<in> m` `m \<in> n` show False using mem_asym by blast
qed


subsection \<open>\<omega>, the smallest infinite ordinal\<close>

definition omega ("\<omega>")
  where "\<omega> \<equiv> {}"


end
