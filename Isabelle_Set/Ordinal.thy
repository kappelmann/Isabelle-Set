theory Ordinal
imports Set_Theory
begin

definition Ord :: "set type" where
  Ord_typedef: "Ord \<equiv> Type (\<lambda>x. epsilon_transitive x \<and> (\<forall>y \<in> x. epsilon_transitive y))"

lemma empty_ordinal [intro!]: "{} : Ord"
  unfolding Ord_typedef epsilon_transitive_def by squash_types auto

lemma Ord_transitive [elim]: "\<lbrakk>y \<in> x; x : Ord\<rbrakk> \<Longrightarrow> y : Ord"
  unfolding Ord_typedef epsilon_transitive_def by squash_types blast

lemma Ord_elem_subset: "\<lbrakk>x : Ord; y \<in> x\<rbrakk> \<Longrightarrow> y \<subseteq> x"
  unfolding Ord_typedef epsilon_transitive_def by squash_types


(* Adaptation of an Egal proof originally formulated by Chad E. Brown *)
lemma Ord_trichotomy_aux:
  "X : Ord \<Longrightarrow> Y : Ord \<Longrightarrow> X \<notin> Y \<Longrightarrow> Y \<notin> X \<Longrightarrow> X = Y"
proof (induction X Y rule: elem_double_induct)
  fix X Y
  assume Ord: "X : Ord" "Y : Ord"
  assume IH1: "\<And>x Y. x \<in> X \<Longrightarrow> x : Ord \<Longrightarrow> Y : Ord \<Longrightarrow> x \<notin> Y \<Longrightarrow> Y \<notin> x \<Longrightarrow> x = Y"
  assume IH2: "\<And>y. y \<in> Y \<Longrightarrow> X : Ord \<Longrightarrow> y : Ord \<Longrightarrow> X \<notin> y \<Longrightarrow> y \<notin> X \<Longrightarrow> X = y"
  assume a: "X \<notin> Y" "Y \<notin> X"
  show "X = Y"
  proof (rule extensionality)
    show "X \<subseteq> Y" 
    proof
      fix x assume "x \<in> X"
      with Ord have "x \<subseteq> X" "x : Ord" by (auto elim!: Ord_elem_subset)
      with a Ord IH1[of x Y] `x \<in> X` show "x \<in> Y" by blast
    qed
    show "Y \<subseteq> X"
    proof
      fix y assume "y \<in> Y"
      with Ord have "y \<subseteq> Y" "y : Ord" by (auto elim!: Ord_elem_subset)
      with a Ord IH2[of y] `y \<in> Y` show "y \<in> X" by blast
    qed
  qed
qed

lemma Ord_trichotomy: "\<lbrakk>X : Ord; Y : Ord\<rbrakk> \<Longrightarrow> X \<in> Y \<or> X = Y \<or> Y \<in> X"
  using Ord_trichotomy_aux by blast

definition epsilon_well_ordered :: "set \<Rightarrow> bool"
  where "epsilon_well_ordered x \<equiv> \<forall>y. y \<subseteq> x \<and> y \<noteq> {} \<longrightarrow> (\<exists>!u \<in> y. \<not>(\<exists>v \<in> y. v \<in> u))"

lemma ordinals_well_ordered: "x : Ord \<Longrightarrow> epsilon_well_ordered x"
  oops

lemma Ord_subset_elem: "\<lbrakk>x \<subseteq> y; x \<noteq> y; x : Ord; y : Ord\<rbrakk> \<Longrightarrow> x \<in> y"
  oops


subsection \<open>The von Neumann ordinals\<close>

definition Succ :: "set \<Rightarrow> set"
  where "Succ x \<equiv> x \<union> {x}"

lemma Succ_Ord: "x : Ord \<Longrightarrow> Succ x : Ord"
  unfolding Ord_typedef Succ_def epsilon_transitive_def by squash_types blast

lemma Succ_neq [intro]: "x \<noteq> Succ x"
unfolding Succ_def
proof (rule, elim equalityE)
  assume "x \<union> {x} \<subseteq> x"
  thus False using elem_irrefl by auto
qed

lemma Succ_elem: "x \<in> Succ x"
  unfolding Succ_def by auto


end
