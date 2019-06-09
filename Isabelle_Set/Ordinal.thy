theory Ordinal
imports Pair

begin

definition ordinal :: "set \<Rightarrow> bool" where
  "ordinal \<equiv> \<lambda> X. epsilon_transitive X \<and> (\<forall> x. x \<in> X \<longrightarrow> epsilon_transitive x)"

theorem ord_th1:
  "ordinal {}" 
proof(unfold ordinal_def,standard)
  show "epsilon_transitive {}" unfolding epsilon_transitive_def using empty_axiom by auto
  show "\<forall> x. x \<in> {} \<longrightarrow> epsilon_transitive x" using empty_axiom by auto  
qed

theorem ord_th2:
  "ordinal X \<and> Y \<in> X \<longrightarrow> ordinal Y"
proof(standard)
  assume A: "ordinal X \<and> Y \<in> X"
  show "ordinal Y"
  proof(unfold ordinal_def,standard)
    show "epsilon_transitive Y" using A unfolding ordinal_def by auto 
    show "\<forall>x. x \<in> Y \<longrightarrow> epsilon_transitive x"
    proof(auto)
      have " epsilon_transitive X" using A unfolding ordinal_def by blast
      hence A2: "Y \<subseteq> X" using A epsilon_transitive_def[of X] by auto
      fix x assume "x \<in> Y"
      hence "x \<in> X" using A2 by auto
      then show "epsilon_transitive x" using A unfolding ordinal_def by auto  
    qed
  qed
qed

(* Adaptation of a Egal proof, originally formulated by Chad .E. Brown*)
theorem trichotomy:
  "ordinal X \<and> ordinal Y \<longrightarrow> X \<in> Y \<or> X=Y \<or> Y \<in> X"
proof-
  let ?PX = "\<lambda> X. ordinal X \<longrightarrow> (\<forall> Y. ordinal Y \<longrightarrow> X \<in> Y \<or> X=Y \<or> Y \<in> X)"
  have "\<forall>X. (\<forall>x. x \<in> X \<longrightarrow> ?PX x) \<longrightarrow> ?PX X"
  proof(standard,standard,standard)
    fix X assume AX: "\<forall>x. x \<in> X \<longrightarrow> ?PX x" "ordinal X"
    let ?PY = "\<lambda> Y. ordinal Y \<longrightarrow> X \<in> Y \<or> X=Y \<or> Y \<in> X"
    have "\<forall>Y. (\<forall>y. y \<in> Y \<longrightarrow> ?PY y) \<longrightarrow> ?PY Y"
    proof(standard,standard,standard)
      fix Y assume AY: "\<forall>y. y \<in> Y \<longrightarrow> ?PY y" "ordinal Y" 
      have "\<not> X \<in> Y \<and> \<not> Y \<in> X \<longrightarrow> X=Y"
      proof  
        assume Ain: "\<not> X \<in> Y \<and> \<not> Y \<in> X"
        have XY: "X \<subseteq> Y"
        proof
          fix x assume xX: "x \<in> X"
          have SxX: "x \<subseteq> X" using xX AX(2) unfolding ordinal_def 
                 epsilon_transitive_def by auto
          have "ordinal x" using ord_th2 xX AX by auto
          then show "x \<in> Y" using AX xX AY Ain SxX by auto     
        qed
        have "Y \<subseteq> X"
        proof
          fix y assume yY: "y \<in> Y"
          have SyY: "y \<subseteq> Y" using yY AY(2) unfolding ordinal_def 
                 epsilon_transitive_def by auto
          have "ordinal y" using ord_th2 yY AY by auto
          then show "y \<in> X" using AX yY AY Ain SyY by auto     
        qed
        then show "X=Y" using XY extensionality_axiom by auto
      qed
      then show "X \<in> Y \<or> X = Y \<or> Y \<in> X" by auto
    qed
    then show " \<forall>Y. ?PY Y" using elem_induct_axiom[of ?PY] by blast
  qed
  hence " \<forall>X. ?PX X" using elem_induct_axiom[of ?PX] by blast
  then show "ordinal X \<and> ordinal Y \<longrightarrow> X \<in> Y \<or> X=Y \<or> Y \<in> X" by blast
qed

end
