theory Ordinal
imports Set_Theory

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

lemma Ord_subset_elem: "\<lbrakk>x \<subseteq> y; x \<noteq> y; x : Ord; y : Ord\<rbrakk> \<Longrightarrow> x \<in> y"
  oops


subsection \<open>The von Neumann ordinals\<close>

definition Succ :: "set \<Rightarrow> set"
  where "Succ x \<equiv> x \<union> {x}"

lemma Succ_Ord: "x : Ord \<Longrightarrow> Succ x : Ord"
  unfolding Ord_typedef Succ_def mem_transitive_def by squash_types blast

lemma Succ_neq [intro]: "x \<noteq> Succ x"
unfolding Succ_def
proof (rule, elim equalityE)
  assume "x \<union> {x} \<subseteq> x"
  thus False using mem_irrefl by auto
qed

lemma Succ_elem: "x \<in> Succ x"
  unfolding Succ_def by auto

lemma Succ_not_empty: "Succ n \<noteq> {}"
  unfolding Succ_def by auto

lemma Succ_inject: "Succ n = Succ m \<Longrightarrow> n = m"
proof (rule ccontr)
  assume Succ_eq: "Succ n = Succ m"
  assume neq: "n \<noteq> m"

  have "n \<in> Succ n" unfolding Succ_def by blast
  with Succ_eq have "n \<in> Succ m" by simp
  with neq have "n \<in> m" unfolding Succ_def by blast

  have "m \<in> Succ m" unfolding Succ_def by blast
  with Succ_eq have "m \<in> Succ n" by simp
  with neq have "m \<in> n" unfolding Succ_def by blast

  from `n \<in> m` `m \<in> n` show False using mem_asym by blast
qed



end
