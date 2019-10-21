theory Tarski_A
imports KPTest
begin

definition Tarski_axiom_A where 
  " Tarski_axiom_A \<equiv>  \<forall> N. \<exists> M.
        N \<in> M \<and>
       (\<forall> X Y. X \<in> M \<and> Y \<subseteq> X \<longrightarrow> Y \<in> M)\<and>
       (\<forall> X. X \<in> M \<longrightarrow> Pow X \<in> M)\<and>
       (\<forall> X. X \<subseteq> M \<longrightarrow> (\<exists> b. b: bij X M) \<or> X \<in> M)" 

theorem
  "AC_axiom \<longrightarrow> Tarski_axiom_A" 
  unfolding Tarski_axiom_A_def
proof(intro impI allI)
  assume AC: "AC_axiom"
  fix N
   show "\<exists> M.
        N \<in> M \<and>
       (\<forall> X Y. X \<in> M \<and> Y \<subseteq> X \<longrightarrow> Y \<in> M)\<and>
       (\<forall> X. X \<in> M \<longrightarrow> Pow X \<in> M)\<and>
       (\<forall> X. X \<subseteq> M \<longrightarrow> (\<exists> b. b: bij X M) \<or> X \<in> M)"
  proof(rule exI[of _ "Univ N"],intro conjI)
    show "N \<in> Univ N" using Univ_base by auto
    show "\<forall>X Y. X \<in> Univ N \<and> Y \<subseteq> X \<longrightarrow> Y \<in> Univ N" 
    proof(intro allI impI)
      fix X Y assume A: "X \<in> Univ N \<and> Y \<subseteq> X"
      hence "Pow X \<in> Univ N" using ZF_closed_def Univ_ZF_closed by auto
      hence "Pow X \<subseteq> Univ N" using Univ_transitive mem_transitive_def by auto
      thus "Y \<in> Univ N" using A by auto
    qed
    show "\<forall>X. X \<in> Univ N \<longrightarrow> Pow X \<in> Univ N"  using ZF_closed_def Univ_ZF_closed by auto
    show "\<forall>X. X \<subseteq> Univ N \<longrightarrow> (\<exists>b. b : bij X (Univ N)) \<or> X \<in> Univ N" using  
      Axioms.Univ_transitive Univ_ZF_closed CB_Th_5 AC by auto
  qed
qed

end