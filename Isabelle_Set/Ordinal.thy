theory Ordinal
imports Set_Theory

begin

definition Ord :: "set type" where
  Ord_typedef: "Ord \<equiv> Type (\<lambda>x. epsilon_transitive x \<and> (\<forall>y \<in> x. epsilon_transitive y))"

lemma empty_ordinal [intro!]: "{} : Ord"
  unfolding Ord_typedef epsilon_transitive_def by stauto

lemma Ord_transitive [elim]: "\<lbrakk>y \<in> x; x : Ord\<rbrakk> \<Longrightarrow> y : Ord"
  unfolding Ord_typedef epsilon_transitive_def by stauto blast+

(* Adaptation of an Egal proof originally formulated by Chad E. Brown *)
lemma Ord_trichotomy:
  "\<lbrakk>X : Ord; Y : Ord\<rbrakk> \<Longrightarrow> X \<in> Y \<or> X = Y \<or> Y \<in> X"
proof -
  let ?PX = "\<lambda>X. X : Ord \<longrightarrow> (\<forall>Y. Y : Ord \<longrightarrow> X \<in> Y \<or> X = Y \<or> Y \<in> X)"
  have "\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?PX x) \<longrightarrow> ?PX X"
  proof (rule, rule, rule)
    fix X assume AX: "\<forall>x. x \<in> X \<longrightarrow> ?PX x" "X : Ord"
    let ?PY = "\<lambda>Y. Y : Ord \<longrightarrow> X \<in> Y \<or> X = Y \<or> Y \<in> X"
    have "\<forall>Y. (\<forall>y. y \<in> Y \<longrightarrow> ?PY y) \<longrightarrow> ?PY Y"
    proof (rule, rule, rule)
      fix Y assume AY: "\<forall>y. y \<in> Y \<longrightarrow> ?PY y" "Y : Ord"
      have "X \<notin> Y \<and> Y \<notin> X \<longrightarrow> X = Y"
      proof
        assume Ain: "X \<notin> Y \<and> Y \<notin> X"
        have XY: "X \<subseteq> Y"
        proof
          fix x assume xX: "x \<in> X"
          have SxX: "x \<subseteq> X"
            using xX AX(2) unfolding Ord_typedef epsilon_transitive_def by stauto
          have "x : Ord" using Ord_transitive xX AX by auto
          then show "x \<in> Y" using AX xX AY Ain SxX by auto
        qed
        have "Y \<subseteq> X"
        proof
          fix y assume yY: "y \<in> Y"
          have SyY: "y \<subseteq> Y"
            using yY AY(2) unfolding Ord_typedef epsilon_transitive_def by stauto
          have "y : Ord" using Ord_transitive yY AY by auto
          then show "y \<in> X" using AX yY AY Ain SyY by auto
        qed
        then show "X = Y" using XY extensionality by auto
      qed
      thus "X \<in> Y \<or> X = Y \<or> Y \<in> X" by auto
    qed
    then show " \<forall>Y. ?PY Y" using elem_induct_axiom[of ?PY] by blast
  qed
  hence "\<forall>X. ?PX X" using elem_induct_axiom[of ?PX] by blast
  thus "\<lbrakk>X : Ord; Y : Ord\<rbrakk> \<Longrightarrow> X \<in> Y \<or> X = Y \<or> Y \<in> X" by blast
qed

abbreviation epsilon_well_ordered :: "set \<Rightarrow> bool"
  where "epsilon_well_ordered x \<equiv> \<forall>y. y \<subseteq> x \<and> y \<noteq> {} \<longrightarrow> (\<exists>!u \<in> y. \<not>(\<exists>v \<in> y. v \<in> u))"

lemma ordinals_well_ordered: "x : Ord \<Longrightarrow> epsilon_well_ordered x"
unfolding Ord_typedef
proof stauto
  oops

lemma Ord_subset_elem: "\<lbrakk>x \<subseteq> y; x \<noteq> y; x : Ord; y : Ord\<rbrakk> \<Longrightarrow> x \<in> y"
  oops


subsection \<open>The von Neumann ordinals\<close>

definition Succ :: "set \<Rightarrow> set"
  where "Succ x \<equiv> x \<union> {x}"

lemma Succ_Ord: "x : Ord \<Longrightarrow> Succ x : Ord"
  unfolding Ord_typedef Succ_def epsilon_transitive_def by stauto blast

lemma Succ_neq [intro]: "x \<noteq> Succ x"
unfolding Succ_def
proof (rule, elim equalityE)
  assume "x \<union> {x} \<subseteq> x"
  thus False using elem_irrefl by auto
qed

lemma Succ_elem: "x \<in> Succ x"
  unfolding Succ_def by auto


end
