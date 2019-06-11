theory Ordinal
imports Pair

begin

definition Ord :: "set type" where
  Ord_typedef: "Ord \<equiv> Type (\<lambda>x. epsilon_transitive x \<and> (\<forall>y \<in> x. epsilon_transitive y))"

theorem empty_ordinal [intro!]: "{} : Ord"
  unfolding Ord_typedef epsilon_transitive_def by stauto

lemma Ord_transitive [elim]: "\<lbrakk>y \<in> x; x : Ord\<rbrakk> \<Longrightarrow> y : Ord"
  unfolding Ord_typedef epsilon_transitive_def by stauto blast+

(* Adaptation of an Egal proof originally formulated by Chad E. Brown *)
theorem Ord_trichotomy:
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


end
