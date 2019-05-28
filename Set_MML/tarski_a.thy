theory tarski_a
imports tarski

begin

theorem tarski_a_th_1:
  "\<And>N. \<exists>M.
    N \<in> M \<and>
    (\<forall>X Y. X \<in> M \<and> Y \<subseteq> X \<longrightarrow> Y \<in> M) \<and>
    (\<forall>X. X \<in> M \<longrightarrow> (\<exists>Z. Z \<in> M \<and> (\<forall>Y. Y \<subseteq> X \<longrightarrow> Y \<in> Z))) \<and>
    (\<forall>X. X \<subseteq> M \<longrightarrow> (X, M are_equipotent) \<or> X \<in> M)"
apply rule
apply (rule conjI) defer
apply (rule conjI) defer
apply (rule conjI) defer defer
proof -
  fix N

  show "N \<in> Univ N" by (fact Univ_member)

  show "\<forall>X Y. X \<in> Univ N \<and> Y \<subseteq> X \<longrightarrow> Y \<in> Univ N"
  proof rule+
    fix X Y assume
    1: "X \<in> Univ N \<and> Y \<subseteq> X"
    hence
    2: "Pow X \<in> Univ N"
      using Univ_ZF_closed unfolding ZF_closed_def by auto
    with 1 have "Y \<in> Pow X" by auto
    with 2 show "Y \<in> Univ N"
      using Univ_transitive unfolding transitive_def by auto
  qed

  show "\<forall>X. X \<in> Univ N \<longrightarrow> (\<exists>Z. Z \<in> Univ N \<and> (\<forall>Y. Y \<subseteq> X \<longrightarrow> Y \<in> Z))"
  proof rule+
    fix X assume "X \<in> Univ N"
    thus "Pow X \<in> Univ N"
      using Univ_ZF_closed unfolding ZF_closed_def by auto
  qed (auto intro: PowI)

  show "\<forall>X. X \<subseteq> Univ N \<longrightarrow> (X, Univ N are_equipotent) \<or> X \<in> Univ N"
    sorry
qed

end
