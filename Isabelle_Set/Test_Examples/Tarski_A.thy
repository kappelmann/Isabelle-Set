theory Tarski_A
imports KPTest
begin

definition Tarski_axiom_A where 
  " Tarski_axiom_A \<equiv>  \<forall> N. \<exists> M.
        N \<in> M \<and>
       (\<forall> X Y. X \<in> M \<and> Y \<subseteq> X \<longrightarrow> Y \<in> M)\<and>
       (\<forall> X. X \<in> M \<longrightarrow> powerset X \<in> M)\<and>
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
       (\<forall> X. X \<in> M \<longrightarrow> powerset X \<in> M)\<and>
       (\<forall> X. X \<subseteq> M \<longrightarrow> (\<exists> b. b: bij X M) \<or> X \<in> M)"
  proof(rule exI[of _ "univ N"],intro conjI)
    show "N \<in> univ N" using univ_elem by auto
    show "\<forall>X Y. X \<in> univ N \<and> Y \<subseteq> X \<longrightarrow> Y \<in> univ N" 
    proof(intro allI impI)
      fix X Y assume A: "X \<in> univ N \<and> Y \<subseteq> X"
      hence "powerset X \<in> univ N" using ZF_closed_def univ_ZF_closed by auto
      hence "powerset X \<subseteq> univ N" using univ_transitive mem_transitive_def by auto
      thus "Y \<in> univ N" using A by auto
    qed
    show "\<forall>X. X \<in> univ N \<longrightarrow> powerset X \<in> univ N"  using ZF_closed_def univ_ZF_closed by auto
    show "\<forall>X. X \<subseteq> univ N \<longrightarrow> (\<exists>b. b: bij X (univ N)) \<or> X \<in> univ N" using  
      Axioms.univ_transitive univ_ZF_closed CB_Th_5 AC by auto
  qed
qed

end